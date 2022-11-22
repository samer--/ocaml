(* 
 * Inference
 *
 * Uses WTree (tree with thunk to distribution over subtrees)
 * Monadic type is just WTree
 * Uses a record of functions to parameterise over Prob modules
 *)

(* open Delimcc *)
open Utils
open Monads
open Lazydata
open Dist
open Prob


type 'a mapdist = 'a MDist.t

module type INFERENCE = sig
  include Prob.PROB
  exception Failure

  val print : ('a -> string) -> 'a m -> unit
  val flatten : int option -> 'a m -> 'a m
  val exact_reify : (unit -> 'a) -> 'a m
  val variable_elim : ('b -> 'a) -> 'b -> 'a

  type ('a,'b) sampler
  type 'a mapsampler = ('a, 'a mapdist transformer) sampler

  val sample_rejection        : ('a,'a) sampler
  val sample_importance       : int -> ('a,'a weighted) sampler
  val sample_importance_map   : int -> ('a, 'a mapdist transformer) sampler

  val accum_simple   : 'a            -> 'a mapdist transformer
  val accum_weighted : 'a weighted   -> 'a mapdist transformer

  val map_sampler : ('b -> 'c) -> ('a,'b) sampler -> ('a,'c) sampler 
  val collect  : int -> 'a mapsampler -> ('a, int * 'a dist) sampler
  val reify_sampler : ('a,'b) sampler -> 'a m -> 'b m 
  val run_sampler : ('a,'b) sampler -> 'a m -> 'b

  val collect_samples : int -> 'a mapsampler -> 'a thunk -> int * 'a dist
end


module TreeM = struct
  (* Weighted non-determinism monad using WTree lazy trees. 
   * The Node constructor contains a thunk to produce a distribution over
   * sub-trees. The monadic type is 'a tree, which has two constructors,
   * [Leaf] and [Node]. This means that return x can be represented simply
   * as Leaf x, but failure must be represented by a Node that produces an empty
   * list. 
   * *)
  include WTree

  type 'a m = 'a tree
  let return x = Leaf x
  let rec extend f = function
    | Leaf x -> f x
    | Node tst -> Node (Dist.fmap (extend f) ** tst)

  let bind t f = extend f t
  let fail = Node (const [])
  let choice xs = Node (const (Dist.fmap return xs))
end


(* Probabilistic effects based on some tree monad 
 *
 * NB: I am using operators from Utils.Pair to notate some common
 * function application patterns on pairs.
 *)
module TreeSampler : INFERENCE = struct
  (* functions in a record to allow higher-order polymorphism *)
  type prob = {
    dist : 'a. 'a dist -> 'a;
    fail : 'a. unit -> 'a;
    memo : 'a 'b. ('a -> 'b) -> 'a -> 'b;
    letlazy : 'a. (unit -> 'a) -> unit -> 'a
  }

  module ProbDict (M : PROBMONAD) = struct
    include Probimps.Make(M)
    let dict = { dist=dist; fail=fail; memo=memo; letlazy=letlazy } 
  end

  module P = ProbDict(TreeM)
  module R = ProbDict(SampleEM)
  include P 

  open WTree
  open Pair

  type ('a,'b) sampler = prob -> 'a m -> 'b 
  type 'a mapsampler = ('a, 'a mapdist transformer) sampler

  exception Failure

  let print = WTree.print

  let rec md_accum_tree w0 map (w,t) = match t with
    | Leaf x -> MDist.accum (w0 *. w,x) map
    | Node tt -> List.fold_left (md_accum_tree (w0 *. w)) map (tt ()) 


  let flatten depth tree =
    let rec bfold d w0 s0 (w,t) = match t with
      | Leaf x -> MDist.accum (w*.w0,x) $> s0
      | Node tt -> if d<=0 then cons (w*.w0, t) <$ s0 
                   else List.fold_left (bfold (d-1) (w*.w0)) s0 (tt ()) 

    in let rec ufold w0 s0 (w,t) = match t with
      | Leaf x -> MDist.accum (w*.w0,x) s0
      | Node tt -> List.fold_left (ufold (w*.w0)) s0 (tt ())

    (* choose bounded or unbounded depending on depth option *)
    in let (nodes,leaves) = match depth with 
      | Some depth -> bfold depth one ([],MDist.empty) (one, tree)
      | None -> ([],ufold one MDist.empty (one, tree)) 

    in node (MDist.foldl (fun (w,x) ts -> (w,Leaf x) :: ts) leaves nodes)

  let exact_reify f = flatten None (reify f)
  let variable_elim f arg = reflect (exact_reify (fun () -> f arg))


  (* sample_rejection : prob -> 'a m -e-> 'a option
   *
   * This simply takes a lazy tree and reflects back into a
   * a arbitrary probability effect determined by the function dist.
   * If this comes from Prob.Make(TreeM), this simply recreates the tree
   * on reification (with unit weights attached to all values), 
   * but if Prob.Make(SampleM) is used to reflect and
   * reify, we get actual samples from the distribution.
   *)
  let rec sample_rejection dict = function 
    | Leaf x -> x
    | Node tt -> match tt () with
      | [] -> raise Failure
      | d  -> sample_rejection dict (dict.dist d)


  (* bound_and_prune : int -> 'a tree dist weighted -> 'a tree dist weighted 
   *
   * This function takes a distribution over trees and maps it to an
   * upper bound on the probability mass contained with the trees
   * (by detecting failures within a certain depth) along with
   * a renomalised distribution over the trees with the dead branches
   * removed.
   * This version is implemented as an idempotent function on pairs of
   * distributions and weights such as the result is equivalent to the input
   * when expanded as a list of weighted leaves. 
   *)
  let rec bound_and_prune depth (w0,trees) = 
    if trees=[] then (zero, [])
    else if depth=0 then (w0, trees)
    else let reweight (w,t) = match t with 
      | Leaf x -> (w,t)
      | Node tt -> node $> bound_and_prune (depth-1) (w, tt ())
      in mul w0 <$ normalise' (prune (List.map reweight trees))

  (* sample_importance : int -> prob -> 'a m -[e]-> 'a weighted
   *
   * This essentially reflects the results of bound_and_prune back
   * into an arbitrary probabilistic effect determined by [dist].
   * If [Prob.Make(TreeM)] is used to reflect and reify, then we get a
   * pruned and reweighted version of the original tree. If [Prob.Make(SampleM)]
   * is used, then we get weighted samples.
   *)
  let sample_importance depth dict tree = 
    let dist = function | [] -> raise Failure | xs -> dict.dist xs in
    let rec sample_weighted (w0,t) = match t with 
      | Leaf x -> (w0,x)
      | Node tt -> sample_weighted (dist $> bound_and_prune depth (w0, tt ()))
    in sample_weighted (one,tree)

  (* split_trees : int -> 'a tree dist 
   *                    -> 'a tree dist weighted * 'a tree dist weighted 
   *
   * this, it turns out, is a bit like Oleg's shallow_explore, except he
   * accumulates leaves in a PMap, whereas I replicate the tree structure.
   * Also I return a dist of renormalised branches.
   *)
  let rec split_trees depth trees = 
    if trees=[] then ((zero,[]),(zero,[])) 
    else if depth=0 then ((zero,[]), (one,trees))
    else 
      let accum w (tot,ts') ts = if tot=zero then ts else (w*.tot, Node (const ts'))::ts in
      let split_tree (leaves,branches) (w,t) = match t with 
          | Leaf x -> ((w,t) :: leaves, branches)
          | Node tt -> pzip (accum w) (split_trees (depth-1) (tt ())) (leaves,branches) in
      normalise' <$> (List.fold_left split_tree ([],[]) trees)


  (* This version will add leaves to the given mapdist *)
  let sample_importance_map depth dict : 'a tree -> 'a mapdist transformer = 
    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> md_accum_tree w0 map (one,Leaf x) 
      | Node tt -> let ((ltot,leaves),(btot,normed)) = split_trees depth (tt ()) in
          (if btot=zero then id 
          else sample_weighted (w0 *. btot) (dict.dist normed))
            (md_accum_tree w0 map (ltot, node leaves))
    in sample_weighted one


  let accum_simple x = MDist.accum (one,x)
  let accum_weighted = MDist.accum  
  let accum_tree t m = md_accum_tree one m t

  let collect n sampler dict tree = 
    let acc' s = try sampler dict tree $> s with Failure -> succ <$ s in
    MDist.to_dist $>  iterate n acc'  (0,MDist.empty) 

  let reify_sampler sampler tree = reify (fun () -> sampler dict tree)
  let run_sampler sampler tree = R.reify (fun () -> sampler R.dict tree) ()

  let collect_samples n sampler thunk = 
    run_sampler (collect n sampler) (reify thunk)

  let map_sampler f sampler dict tree = f (sampler dict tree)
end

let ( *|* ) = TreeSampler.map_sampler


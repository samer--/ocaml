(* Inference3 - 'a m = 'a WTree.tree, Node of 'a tree dist thunk
 * 
 * WTree (tree dist thunk)
 * Monadic type is just the tree type
 * My sampling framework
 *)

open Utils
open Lazydata
open Dist
open Prob
open WTree
open Pair


let rec md_accum_tree w0 map (w,t) = match t with
  | Leaf x -> MDist.accum (w0 *. w,x) map
  | Node tt -> List.fold_left (md_accum_tree (w0 *. w)) map (tt ()) 

(* Probabilistic effects based on some tree monad 
 *
 * NB: I am using operators from Utils.Pair to notate some common
 * function application patterns on pairs.
 *)
module Explore = ExploreOps (struct

  type 'a m = 'a tree

  let print = WTree.print
  let accum w0 tree md = md_accum_tree w0 md (one,tree)

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

 let search_bf tree = 
   let rec bf = function
     | [] -> None
     | (_,t)::ts -> match t with
          | Leaf x -> Some x
          | Node tts -> bf (ts @ (tts ())) in
   bf [(one,tree)]

 let search_df tree = 
   let rec df = function
     | [] -> None
     | (_,t)::ts -> match t with
          | Leaf x -> Some x
          | Node tts -> df ((tts ()) @ ts) in
   df [(one,tree)]
 end)


module Sampler (X : PROB) : sig
  open Explore

  type 'a xm = 'a X.m

  val sample_rejection        : ('a,'a) sampler
  val sample_rejection_mdist  : ('a, (int * 'a mapdist) transformer) sampler

  val sample_importance       : int -> ('a,'a weighted) sampler
  val sample_importance_tree  : int -> ('a, 'a tree weighted) sampler
  val sample_importance_mdist : int -> ('a, 'a mapdist transformer) sampler
  val sample_importance_mdist' : int -> ('a, 'a mapdist transformer) sampler

  val xreify_sampler : ('a,'b) sampler -> 'a m -> 'b xm 

end = struct
  open Explore

  type 'a xm = 'a X.m

  let rec sample_rejection = function 
    | Leaf x -> x
    | Node tt -> match tt () with
      | [] -> raise Failure
      | d  -> sample_rejection (X.dist d)

  let rec sample_rejection_mdist t (f, m) = match t with 
    | Leaf x -> (f, MDist.accum (one,x) m)
    | Node tt -> match tt () with
      | [] -> (succ f,m)
      | d  -> sample_rejection_mdist (X.dist d) (f,m)

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

  (* This essentially reflects the results of bound_and_prune back
   * into an arbitrary probabilistic effect determined by [dist].
   * If [Prob.Make(TreeM)] is used to reflect and reify, then we get a
   * pruned and reweighted version of the original tree. If [Prob.Make(SampleM)]
   * is used, then we get weighted samples.
   *)
  let sample_importance depth tree = 
    let distf = function 
      | [] -> raise Failure 
      | xs -> X.dist xs in
    let rec sample_weighted (w0,t) = 
      match t with 
      | Leaf x -> (w0,x)
      | Node tt -> sample_weighted (distf $> bound_and_prune depth (w0, tt ()))
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


  (* this builds an 'a tree weighted representing all the leaves collected 
   * on walking down the tree. The distributions at the nodes may not be
   * normalised; the idea is you treat it as a bag of weighted leaves.
   *
   * NB can check for failure by checking whole of resulting tree.
   *)
  let rec sample_importance_tree depth : 'a tree -> 'a tree weighted = function
    | Leaf x -> (one,Leaf x)
    | Node tt -> let ((ltot,leaves),(btot,normed)) = split_trees depth (tt ()) in
        let nleaves = (ltot, node leaves) in
        if btot=zero then nleaves else
          let wnodes = sample_importance_tree depth (X.dist normed) in
          if ltot=zero then wnodes else (one, node [ nleaves; mul btot <$ wnodes ])
          (* alternative is to use node $> normalise' [ nleaves; wnodes ] *)

  (* This version will add leaves to the given mapdist *)
  let sample_importance_mdist depth : 'a tree -> 'a mapdist transformer = 
    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> MDist.accum (w0,x) map 
      | Node tt -> let ((ltot,leaves),(btot,normed)) = split_trees depth (tt ()) in
          (if btot=zero then id 
          else sample_weighted (w0 *. btot) (X.dist normed))
            (md_accum_tree w0 map (ltot, node leaves))
    in sample_weighted one

  (* split_trees' *)
  let rec split_trees' w0 depth trees mdist = 
    if trees=[] then ((zero,[]),mdist) 
    else if depth=0 then ((one,trees),mdist)
    else 
      let accum w ts (tot,ts') = if tot=zero then ts else (w*.tot, Node (const ts'))::ts in
      let split_tree (branches,mdist) (w,t) = match t with 
          | Leaf x -> (branches, MDist.accum (w *. w0, x) mdist)
          | Node tt -> accum w branches <$ split_trees' (w *. w0) (depth-1) (tt ()) mdist  in
      normalise' <$ (List.fold_left split_tree ([],mdist) trees)

  (* This version will add leaves to the given mapdist *)
  let sample_importance_mdist' depth : 'a tree -> 'a mapdist transformer = 
    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> MDist.accum (w0,x) map 
      | Node tt -> 
          let ((btot,normed),map') = split_trees' w0 depth (tt ()) map in
          if btot=zero then map' 
          else sample_weighted (w0 *. btot) (X.dist normed) map'
    in sample_weighted one

  let xreify_sampler sampler tree = X.reify (fun () -> sampler tree)
end


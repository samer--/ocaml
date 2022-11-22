(* Inference1 - 'a m = 'a WTreeAlt.tree thunk
 * 
 * - WTreeAlt (distribution over thunks)
 * - Monadic type is a tree thunk (not a tree).
 * - my sampling framework
 *)

open Utils
open Lazydata
open Dist
open Prob
open WTreeAlt
open Pair

let lnode x () = Node x
let lleaf x () = Leaf x
let rec md_accum_tree w0 map (w,tt) = match tt () with
  | Leaf x -> MDist.accum (w0 *. w,x) map
  | Node t -> List.fold_left (md_accum_tree (w0 *. w)) map t 

module Explore = ExploreOps (struct

  type 'a m = 'a tree thunk

  let print f tt = WTreeAlt.print f (tt ())
  let accum w0 tree md = md_accum_tree w0 md (one,tree)

  let flatten depth tt =
    let rec bfold d w0 s0 (w,tt) = match tt () with
      | Leaf x -> MDist.accum (w*.w0,x) $> s0
      | Node ts -> if d<=0 then cons (w*.w0, tt) <$ s0 
                   else List.fold_left (bfold (d-1) (w*.w0)) s0 ts 

    in let rec ufold w0 s0 (w,tt) = match tt () with
      | Leaf x -> MDist.accum (w*.w0,x) s0
      | Node ts -> List.fold_left (ufold (w*.w0)) s0 ts

    (* choose bounded or unbounded depending on depth option *)
    in let (nodes,leaves) = match depth with 
      | Some depth -> bfold depth one ([],MDist.empty) (one,tt)
      | None -> ([],ufold one MDist.empty (one,tt)) 

    in lnode (MDist.foldl (fun (w,x) ts -> (w,lleaf x) :: ts) leaves nodes)

 let search_bf tree = 
   let rec bf = function
     | [] -> None
     | (_,t)::ts -> match t () with
          | Leaf x -> Some x
          | Node ts' -> bf (ts @ ts') in
   bf [(one,tree)]

 let search_df tree = 
   let rec df = function
     | [] -> None
     | (_,t)::ts -> match t () with
          | Leaf x -> Some x
          | Node ts' -> df (ts' @ ts) in
   df [(one,tree)]
end)

module Sampler (X : PROB) : sig
  open Explore

  type 'a xm = 'a X.m

  val sample_rejection        : ('a,'a) sampler
  val sample_rejection_mdist  : ('a, (int * 'a mapdist) transformer) sampler

  val sample_importance       : int -> ('a,'a weighted) sampler
  val sample_importance_tree  : int -> ('a, 'a tree thunk weighted) sampler
  val sample_importance_mdist : int -> ('a, 'a mapdist transformer) sampler

  val xreify_sampler : ('a,'b) sampler -> 'a m -> 'b xm 

end = struct
  open Explore

  type 'a xm = 'a X.m

  let rec sample_rejection tt = match tt () with 
    | Leaf x -> x
    | Node tt -> match tt with
      | [] -> raise Failure
      | d  -> sample_rejection (X.dist d)

  let rec sample_rejection_mdist tt (f, m) = match tt () with 
    | Leaf x -> (f, MDist.accum (one,x) m)
    | Node ts -> match ts with
      | [] -> (succ f,m)
      | d  -> sample_rejection_mdist (X.dist d) (f,m)

  (* bound_and_prune : int -> 'a tree thunk dist weighted -> 'a tree thunk dist weighted 
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
      else let reweight (w,tt) = match tt () with 
        | Leaf x -> (w, lleaf x)
        | Node ts -> lnode $> bound_and_prune (depth-1) (w, ts)
        in mul w0 <$ normalise' (prune (List.map reweight trees))

  (* This essentially reflects the results of bound_and_prune back
   * into an arbitrary probabilistic effect determined by [dist].
   * If [Prob.Make(TreeM)] is used to reflect and reify, then we get a
   * pruned and reweighted version of the original tree. If [Prob.Make(SampleM)]
   * is used, then we get weighted samples.
   *)
  let sample_importance depth tt = 
    let distf = function 
      | [] -> raise Failure
      | xs -> X.dist xs in 
    let rec sample_weighted (w0,tt) = 
      match tt () with 
      | Leaf x -> (w0,x)
      | Node t -> sample_weighted (distf $> bound_and_prune depth (w0, t))
    in sample_weighted (one, tt)


  (* split_trees : int -> 'a tree thunk dist 
   *                   -> 'a tree thunk dist weighted * 'a tree thunk dist weighted 
   *
   * this, it turns out, is a bit like Oleg's shallow_explore, except he
   * accumulates leaves in a PMap, whereas I replicate the tree structure.
   * Also I return a dist of renormalised branches.
   *)
  let rec split_trees depth trees = 
    if trees=[] then ((zero,[]),(zero,[])) 
    else if depth=0 then ((zero,[]), (one,trees))
    else 
      let accum w (tot,ts') ts = 
        if tot=zero then ts else (w*.tot, const (Node ts'))::ts in
      let split_tree (leaves,branches) (w,tt) = match tt () with 
          | Leaf x -> ((w, lleaf x) :: leaves, branches)
          | Node ts -> pzip (accum w) (split_trees (depth-1) ts) (leaves,branches) in
      normalise' <$> (List.fold_left split_tree ([],[]) trees)


  (* this builds an 'a tree weighted representing all the leaves collected 
   * on walking down the tree. The distributions at the nodes may not be
   * normalised; the idea is you treat it as a bag of weighted leaves.
   *
   * NB can check for failure by checking whole of resulting tree.
   *)
  let rec sample_importance_tree depth tt = match tt () with
    | Leaf x -> (one, lleaf x)
    | Node t -> let ((ltot,leaves),(btot,normed)) = split_trees depth t in
      let nleaves = (ltot, lnode leaves) in 
        if btot=zero then nleaves else
          let wnodes = sample_importance_tree depth (X.dist normed) in
          if ltot=zero then wnodes 
          else (one, lnode [ nleaves; mul btot <$ wnodes ])

  (* This version will add leaves to the given mapdist *)
  let sample_importance_mdist depth : 'a tree thunk -> 'a mapdist transformer = 
    let rec sample_weighted w0 tt map = match tt () with 
      | Leaf x -> MDist.accum (w0,x) map 
      | Node t -> let ((ltot,leaves),(btot,normed)) = split_trees depth t in
          (if btot=zero then id 
          else sample_weighted (w0 *. btot) (X.dist normed))
            (md_accum_tree w0 map (ltot, lnode leaves))
    in sample_weighted one

  let xreify_sampler sampler tree = X.reify (fun () -> sampler tree)
end


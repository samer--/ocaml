(* Inference2 - 'a m = 'a WTreeAlt.tree
 * 
 * WTreeAlt (distribution over thunks)
 * Monadic type is tree
 * My sampling framework (cross reification)
 *)

open Utils
open Lazydata
open Dist
open Prob
open Pair
open WTreeAlt

let lnode x () = Node x
let lleaf x () = Leaf x
let rec md_accum_tree w0 map (w,tt) = match tt () with
  | Leaf x -> MDist.accum (w0 *. w,x) map
  | Node t -> List.fold_left (md_accum_tree (w0 *. w)) map t 

module WSTree = struct
  type 'a tree = Leaf of 'a | Node of 'a tree
end

type 'a xtree = 'a WTreeAlt.tree WSTree.tree
(* module ST = WSTree *)
(* module LT = WTreeAlt *)

module Explore = ExploreOps (struct
  type 'a m = 'a tree

  let print = WTreeAlt.print
  let accum w0 tree md = md_accum_tree w0 md (one,const tree)

  let flatten depth tree =
    let rec bfold d w0 s0 (w,tt) = match tt () with
      | Leaf x -> MDist.accum (w*.w0,x) $> s0
      | Node ts -> if d<=0 then cons (w*.w0, tt) <$ s0 
                   else List.fold_left (bfold (d-1) (w*.w0)) s0 ts 

    in let rec ufold w0 s0 (w,tt) = match tt () with
      | Leaf x -> MDist.accum (w*.w0,x) s0
      | Node ts -> List.fold_left (ufold (w*.w0)) s0 ts

    (* choose bounded or unbounded depending on depth option *)
    in let (nodes,leaves) = match depth with 
      | Some depth -> bfold depth one ([],MDist.empty) (one, const tree)
      | None -> ([], ufold one MDist.empty (one, const tree))

    in Node (MDist.foldl (fun (w,x) ts -> (w,lleaf x) :: ts) leaves nodes)

 let search_bf tree = 
   let rec bf = function
     | [] -> None
     | (_,t)::ts -> match t () with
          | Leaf x -> Some x
          | Node ts' -> bf (ts @ ts') in
   bf [(one,const tree)]

 let search_df tree = 
   let rec df = function
     | [] -> None
     | (_,t)::ts -> match t () with
          | Leaf x -> Some x
          | Node ts' -> df (ts' @ ts) in
   df [(one,const tree)]
end)

include Explore

module Sampler (X : PROB) : sig
  open Explore
  type 'a xm = 'a X.m

  val sample_rejection        : ('a,'a) sampler
  val sample_rejection_mdist  : ('a, (int * 'a mapdist) transformer) sampler
  val sample_importance       : int -> ('a,'a weighted) sampler
  val sample_importance_mdist : int -> ('a, 'a mapdist transformer) sampler
  val sample_importance_mdist' : int -> ('a, 'a mapdist transformer) sampler
  val sample_importance_mdist' : int -> ('a, 'a mapdist transformer) sampler
  val sample_importance_dist : int -> int -> ('a, 'a dist) sampler

  val xreify_sampler : ('a,'b) sampler -> 'a m -> 'b xm 

end = struct
  open Explore

  type 'a xm = 'a X.m

  let rec sample_rejection = function 
    | Leaf x -> x
    | Node tt -> match tt with
      | [] -> raise Failure
      | d  -> sample_rejection ((X.dist d) ())

  let rec sample_rejection_mdist t (f, m) = match t with 
    | Leaf x -> (f, MDist.accum (one,x) m)
    | Node tt -> match tt with
      | [] -> (succ f,m)
      | d  -> sample_rejection_mdist ((X.dist d) ()) (f,m)


  (* This essentially reflects the results of bound_and_prune back
   * into an arbitrary probabilistic effect determined by [dist].  *)
  let sample_importance depth tree = 
    (* bound_and_prune : int -> 'a tree thunk dist weighted -> 'a tree thunk dist weighted 
     * Takes a distribution over trees and maps it to an * upper bound on the 
     * probability mass contained with the trees renormalised pruned tree. *)
    let rec bound_and_prune depth (w0,trees) = 
       if trees=[] then (zero, [])
        else if depth=0 then (w0, trees)
        else let reweight (w,tt) = match tt () with 
          | Leaf x -> (w, lleaf x)
          | Node ts -> lnode $> bound_and_prune (depth-1) (w, ts)
          in mul w0 <$ normalise' (prune (List.map reweight trees)) in

    let distf = function | [] -> raise Failure | xs -> X.dist xs () in 

    let rec sample_weighted (w0,t) = 
      match t with 
      | Leaf x -> (w0,x)
      | Node t -> sample_weighted (distf $> bound_and_prune depth (w0, t))
    in sample_weighted (one, tree)


  (* This version will add leaves to the given mapdist 
   * Uses cross reifier to sample *)
  let sample_importance_mdist depth = 
    (* split_trees : weight -> int -> 'a tree thunk dist -> 'a mapdist 
     *                      -> 'a tree thunk dist weighted * 'a mapdist 
     * this, it turns out, is like Oleg's shallow_explore and look_ahead * functions.  *)
    let rec split_trees w0 depth trees mdist = 
      if trees=[] then ((zero,[]),mdist) 
      else if depth=0 then ((one,trees),mdist)
      else 
        let accum w ts (tot,ts') = 
          if tot=zero then ts else (w*.tot, const (Node ts'))::ts in
        let split_tree (branches, mdist) (w,tt) = match tt () with 
          | Leaf x -> (branches, MDist.accum (w *. w0, x) mdist) 
          | Node ts -> accum w branches <$ split_trees (w0 *. w) (depth-1) ts mdist in
        normalise' <$ (List.fold_left split_tree ([],mdist) trees) in

    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> MDist.accum (w0,x) map 
      | Node t -> 
          let ((btot,normed),map') = split_trees w0 depth t map in
          if btot=zero then map' 
          else sample_weighted (w0 *. btot) (X.dist normed ()) map'

    in sample_weighted one 
    (* Printf.printf "Inference2.sample_importance_mdist %d: %d success" *)

  (* Uses direct sampling *)
  let sample_importance_mdist' depth = 

    (* weight -> int -> 'a tree thunk dist -> 'a mapdist -> 'a tree thunk dist* 'a mapdist *)
    let rec split_trees w0 depth trees mdist = 
      if trees=[] then ([],mdist) 
      else if depth=0 then (trees,mdist)
      else 
        let split_tree (branches, mdist) (w,tt) = match tt () with 
            | Leaf x -> (branches, MDist.accum (w *. w0, x) mdist) 
            | Node ts -> let (branches',mdist) = split_trees (w0 *. w) (depth-1) ts mdist in
                         let btot = total branches' in
                         (  (if btot = zero then branches
                            else (  w*.btot 
                                 ,  fun () -> Node (div_weights btot branches')) :: branches) 
                         ,  mdist) in
        List.fold_left split_tree ([],mdist) trees in

    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> MDist.accum (w0,x) map 
      | Node t -> 
          let (branches,map') = split_trees w0 depth t map in
          let btot = total branches in
          if btot=zero then map' 
          else sample_weighted (w0 *. btot) (sample' btot branches ()) map'

    in sample_weighted one
   
  (* This version will sample many times and count successes *)
  (* Plan: reduce thunk and pattern matching by either:
    *   strict list of lazy subtrees
    *   or hybrid strict/lazy tree
  * Also, factor out common deterministic part like Oleg?
  *)

  let sample_importance_dist nsamples depth tree = 
    let successes = ref 0 in
    let failures = ref 0 in
    let incr r = r := succ !r in

    (* split_trees : weight -> int -> 'a tree thunk dist -> 'a mapdist 
     *                      -> 'a tree thunk dist weighted * 'a mapdist 
     * this, it turns out, is like Oleg's shallow_explore and look_ahead * functions.  *)
    let rec split_trees w0 depth trees mdist = 
      if trees=[] then (incr failures; ((zero,[]),mdist))
      else if depth=0 then ((one,trees),mdist)
      else 
        let accum w ts (tot,ts') = 
          if tot=zero then ts else (w*.tot, const (Node ts'))::ts in
        let split_tree (branches, mdist) (w,tt) = match tt () with 
          | Leaf x -> incr successes; (branches, MDist.accum (w *. w0, x) mdist) 
          | Node ts -> accum w branches <$ split_trees (w0 *. w) (depth-1) ts mdist in
        normalise' <$ (List.fold_left split_tree ([],mdist) trees) in

    let rec sample_weighted w0 tree map = match tree with 
      | Leaf x -> incr successes; MDist.accum (w0,x) map 
      | Node t -> 
          let ((btot,normed),map') = split_trees w0 depth t map in
          if btot=zero then map' 
          else sample_weighted (w0 *. btot) (Dist.sample normed ()) map' in

    let mdist = iterate nsamples (sample_weighted one tree) MDist.empty in
    Printf.printf "\n%d failures detected." !failures; 
    Printf.printf "\n%d leaves detected.\n" !successes; 
    MDist.to_dist mdist

(*
  (* harvest : int ->  weight -> 'a mapdist * 'a itree -> 'a mapdist * 'a itree *)
  let rec harvest depth w0 (leaves,tree) =

    let rec split_trees' w0 depth trees mdist = 
      if trees=[] then ((zero,[]),mdist) 
      else if depth=0 then ((one,trees),mdist)
      else 
        let accum w ts (tot,ts') = 
          if tot=zero then ts else (w*.tot, const (Node ts'))::ts in
        (* split_tree :  _ * 'a mapdist -> 'a tree thunk weighted -> _ * 'a mapdist *)
        let split_tree (branches, mdist) (w,tt) = match tt () with 
            | Leaf x -> (branches, MDist.accum (w *. w0, x) mdist) 
            | Node ts -> accum w branches <$ split_trees' (w0 *. w) (depth-1) ts mdist in
        normalise' <$ (List.fold_left split_tree ([],mdist) trees)
*)

  let xreify_sampler sampler tree = X.reify (fun () -> sampler tree)
end


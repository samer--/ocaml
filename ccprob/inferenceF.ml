(* InferenceF - 'a m = 'a WFTreeAlt
 * 
 * WFTree - (tree thunk dist) with Failure
 * Monad is just tree
 *)

open Utils
open Lazydata
open Dist
open Prob
open Pair
open WFTreeAlt

let lnode x () = Node x
let lleaf x () = Leaf x
let lfail ()   = Stump

let rec md_accum_tree w0 map (w,tt) = match tt () with
  | Leaf x -> MDist.accum (w0 *. w,x) map
  | Node t -> List.fold_left (md_accum_tree (w0 *. w)) map t 
  | Stump  -> map

module Explore = ExploreOps (struct
  type 'a m = 'a tree

  let print = WFTreeAlt.print
  let accum w0 tree md = md_accum_tree w0 md (one,const tree)

  let flatten depth tree =
    let rec bfold d w0 s0 (w,tt) = match tt () with
      | Stump -> s0
      | Leaf x -> MDist.accum (w*.w0,x) $> s0
      | Node ts -> if d<=0 then cons (w*.w0, tt) <$ s0 
                   else List.fold_left (bfold (d-1) (w*.w0)) s0 ts 

    in let rec ufold w0 s0 (w,tt) = match tt () with
      | Stump -> s0
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
          | Stump -> bf ts
          | Leaf x -> Some x
          | Node ts' -> bf (ts @ ts') in
   bf [(one,const tree)]

 let search_df tree = 
   let rec df = function
     | [] -> None
     | (_,t)::ts -> match t () with
          | Stump -> df ts
          | Leaf x -> Some x
          | Node ts' -> df (ts' @ ts) in
   df [(one,const tree)]
end)

module Sampler (X : PROB) : sig
  open Explore

  type 'a xm = 'a X.m

  val sample_rejection        : ('a,'a) sampler
  val sample_rejection_mdist  : ('a, (int * 'a mapdist) transformer) sampler
  val sample_importance_mdist : int -> ('a, 'a mapdist transformer) sampler

  val xreify_sampler : ('a,'b) sampler -> 'a m -> 'b xm 

end = struct
  open Explore

  type 'a xm = 'a X.m

  let rec sample_rejection = function 
    | Leaf x -> x
    | Stump -> raise Failure
    | Node tt -> sample_rejection ((X.dist tt) ())

  let rec sample_rejection_mdist t (f, m) = match t with 
    | Stump -> (succ f, m)
    | Leaf x -> (f, MDist.accum (one,x) m)
    | Node tt -> sample_rejection_mdist ((X.dist tt) ()) (f,m)


  (* split_trees : weight -> int -> 'a tree thunk dist 
   *                       -> 'a mapdist 
   *                       -> 'a tree thunk dist weighted * 'a mapdist 
   * NB could build a partially non lazy tree here for speed?
   *)
  let rec split_trees w0 depth trees mdist = 
    if trees=[] then ((zero,[]),mdist) 
    else if depth=0 then ((one,trees),mdist)
    else 
      let accum w ts (tot,ts') = 
        if tot=zero then ts else (w*.tot, const (Node ts'))::ts in
      let split_tree (branches, mdist) (w,tt) = match tt () with 
          | Stump -> (branches, mdist)
          | Leaf x -> (branches, MDist.accum (w *. w0, x) mdist) (* correct weight? *)
          | Node ts -> accum w branches <$ split_trees (w0 *. w) (depth-1) ts mdist in
      normalise' <$ (List.fold_left split_tree ([],mdist) trees)


  (* This version will add leaves to the given mapdist *)
  let sample_importance_mdist depth = 
    let rec sample_weighted w0 tree map = match tree with 
      | Stump -> map
      | Leaf x -> MDist.accum (w0,x) map 
      | Node t -> 
          let ((btot,normed),map') = split_trees w0 depth t map in
          if btot=zero then map' 
          else sample_weighted (w0 *. btot) (X.dist normed ()) map'
    in sample_weighted one

  let xreify_sampler sampler tree = X.reify (fun () -> sampler tree)
end


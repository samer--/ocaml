(* Inference2 - 'a m = 'a WTreeAlt, Oleg's importance sampling algorithm
 * 
 * WTreeAlt (distribution over thunks)
 * Monadic type is tree
 * Oleg's algorithm implemented for WTreeAlt
 * Hard coded sampler
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

open Explore

let rec sample_rejection_mdist t (f, m) = match t with 
  | Leaf x -> (f, MDist.accum (one,x) m)
  | Node tt -> match tt with
    | [] -> (succ f,m)
    | d  -> sample_rejection_mdist (sample d ()) (f,m)


let sample_dist (nsamples : int) (tree : 'a tree) = 
  let failures = ref 0 
  and successes = ref 0 
  and incr r = r := succ !r in

  (* look_ahead : int -> 'a mapdist * 'a tree thunk dist dist
   *                  -> 'a tree thunk weighted 
   *                  -> 'a mapdist * 'a tree thunk dist dist
   *)                   
  let sample_and_total xs =
    let t = List.fold_left (fun pa (p,_) -> pa +. p) 0.0 xs in
    (* let t = total xs in *) 
    (t,sample' t xs) in

  (* let x_sample_and_total xs = *)
  (*   let (t,normed) = normalise' xs in (t, X.dist xs) in *)

  let fsamples = from_int nsamples in

  (* look_ahead : weight -> 'a mapdist * 'a tree thunk dist dist
                         -> 'a tree thunk weighted 
                         -> 'a mapdist * 'a tree thunk dist dist *)
  let rec look_ahead w0 (ans,acc) (p,th) = match th () with
    | Leaf v -> incr successes; (MDist.accum (p *. w0, v) ans, acc)
    | Node ts -> (match ts with
        | [] -> incr failures; (ans,acc)
        | _ -> (ans, (p, ts)::acc)) in

  (* loop : weight -> 'a tree thunk dist -> 'a mapdist -> 'a mapdist *)
  let rec loop w0 (ts : 'a tree thunk dist) ans : 'a mapdist = 
    match  List.fold_left (look_ahead w0) (ans,[]) ts with
    | (ans,[]) -> ans
    | (ans,[(p,t)]) -> loop (w0 *. p) t ans (* saves sampling *)
    | (ans,tdd) -> let (ptotal,ts) = sample_and_total tdd in 
           loop (w0 *. ptotal) ts ans in

  (* toploop : weight -> 'a tree thunk dist dist -> 'a mapdist -> 'a mapdist *)
  let toploop w0 (tdd : 'a tree thunk dist dist) ans : 'a mapdist =	
    let (ptotal,ts) = sample_and_total tdd in
    loop (w0 *. ptotal) ts ans in

  (* make_threads : weight -> 'a tree thunk dist -> 'a mapdist -> 'a mapdist *)
  let rec make_threads w0 (ts : 'a tree thunk dist) ans =  
    match List.fold_left (look_ahead (w0 *. fsamples)) (ans,[]) ts with
    | (ans',[]) -> ans' 
    | (ans',[(p,ts'')]) -> make_threads (w0 *. p) ts'' ans'
    | (ans',ts') -> 
        let res = iterate nsamples (toploop w0 (List.rev ts')) ans' in
        Printf.printf "\n%d failures detected." !failures; 
        Printf.printf "\n%d leaves detected.\n" !successes; res

  in match tree with
  | Node ts -> make_threads one ts MDist.empty 
  | Leaf v -> MDist.accum (fsamples, v) MDist.empty


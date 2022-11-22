(* Inference4 - 'a m = 'a pV, Oleg's algorithm with my improvements
 *
 * Oleg's sampling algorithm, my optimised implementation
 *)
open Ptypes
open Utils

(* Explore and flatten the tree: perform exact inference to the given depth *)
(* If maxdepth is None, explore as far as possible   *)
let explore (maxdepth : int option) (choices : 'a pV) : 'a pV =
  let open Dist in
  let rec loop p depth down choices ((ans,susp) as answers) =
    match choices with
    | [] -> answers
    | (pt,V v)::rest -> loop p depth down rest 
	                  (MDist.accum (pt *. p, v) ans,susp)
    | (pt,C t)::rest when down ->
	let down' = match maxdepth with Some x -> depth < x | None -> true in
	loop p depth down rest
	  (loop (pt *. p) (succ depth) down' (t ()) answers) 
    | (pt, c)::rest -> loop p depth down rest (ans,(pt *. p,c)::susp) in
  let (ans,susp) = loop 1.0 0 true choices (MDist.empty,[])
  in MDist.foldl (fun (p,v) a -> (p,V v)::a) ans susp;;


(* Naive, rejection sampling: the baseline *)
let rejection_sample_dist nsamples ch =
  let open Dist in
  let rec loop pcontrib ch ans = (match ch with
    | V v  -> MDist.accum (pcontrib,v) ans
    | C th -> (match th () with 
        | [] -> ans
        | [(p,t)] -> loop (pcontrib *. p) t ans
        | ch -> let (ptotal,nch) = normalise' ch in
                loop (pcontrib *. ptotal) (sample nch) ans)) in

  iterate nsamples (loop 1.0 ch) MDist.empty


let random_selector () =
  let rec selection (r : float) (pcum : float) = function
      | [] -> failwith "Choice selection: can't happen"
      | ((p,th)::rest) -> let pcum = pcum +. p in
                          if r < pcum then th
	  else selection r pcum rest in
  fun choices ->
    let ptotal = List.fold_left (fun pa (p,_) -> pa +. p) 0.0 choices in
    (ptotal, selection (Random.float ptotal) 0.0 choices)

let sample_dist (total_sample : 'a pV selector) (nsamples : int) (ch : 'a pV) : 'a pV =

  (* let total_sample ch = *) 
  (*   let rec select (u : float) (cum : float) = function *)
  (*     | [] -> failwith "sampling failure" *)
  (*     | (w,x)::rest -> let cum = cum +. w in *)
  (*          if u < cum then x else select u cum rest in *)
  (*   let total = List.fold_left (fun pa (p,_) -> pa +. p) 0.0 ch in *)
  (*   (total,select (Random.float total) 0.0 ch) in *)

  let rec look_ahead pcontrib (ans,acc) = function (* explore the branch a bit *)
    | (p,V v) -> (PMap.insert_with (+.) v (p *. pcontrib) ans, acc)
    | (p,C t) -> (match t () with
        | [] -> (ans,acc)
        (* I have ensured that singleton choices do not occur *)
        (* | [(_,vc)] -> look_ahead pcontrib (ans,acc) (p,vc) *)  
        | ch -> (ans, (p,ch)::acc)) in

  let rec loop pcontrib ans ch = 
    match List.fold_left (look_ahead pcontrib) (ans,[]) ch with
    | (ans,[]) -> ans
    | (ans,[(p,ch)]) -> loop (pcontrib *. p) ans ch
    | (ans,cch) -> let (ptotal, ch) = total_sample cch in
                   loop (pcontrib *. ptotal) ans ch in

  let toploop (pcontrib : float) (cch : 'a pV dist) ans =	(* cch are already pre-explored *)
    let (ptotal, ch) = total_sample cch in
    loop (pcontrib *. ptotal) ans ch in 

  (* let rec iterate n f s = match n with 0 -> s | _ -> iterate (pred n) f (f s) in *)
  let driver (pcontrib : float) vals (cch : 'a pV dist) : 'a pV =
    let ans = iterate nsamples (toploop pcontrib cch) PMap.empty in
    let ns = float_of_int nsamples in
    let ans = PMap.foldi (fun v p a -> PMap.insert_with (+.) v (ns *. p) a) vals ans in
    PMap.foldi (fun v p a -> (p /. ns, V v)::a) ans [] in

  let rec make_threads (pcontrib : float) ans (ch : 'a pV) : 'a pV  =  (* pre-explore initial threads *)
    match List.fold_left (look_ahead pcontrib) (ans,[]) ch with
    | (ans,[]) -> PMap.foldi (fun v p a -> (p, V v)::a) ans [] 
    | (ans,[(p,ch)]) -> make_threads (pcontrib *. p) ans ch
    | (ans,cch) -> driver pcontrib ans (List.rev cch)
  in
  make_threads 1.0 PMap.empty ch 

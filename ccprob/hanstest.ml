open Notes
open Utils
open Printf

let seed = 1972

let vc_to_pv = let open Ptypes in function
  | V x -> [1.0,V x]
  | C tt -> tt ()

let pv_to_vc l = let open Ptypes in C (const l)

module Hansei : Prob.PROB with type 'a m = 'a Ptypes.vc = struct
  module P = ProbM

  type 'a m = 'a Ptypes.vc

  let fail    = P.fail
  let dist    = P.dist
  let reify f = pv_to_vc (P.reify0 f)
  let reflect m = P.reflect (vc_to_pv m)
  let letlazy = P.letlazy
  let memo    = P.memo
end

module TM = Treemonads.WTreeAltM
module ATM = Treemonads.WTreeM
module FTM = Treemonads.WFTreeAltM
module VCM : Monads.PROBMONAD with type 'a m = 'a Ptypes.vc = struct
  open Ptypes

  type 'a m = 'a vc
  let return x = V x
  let rec extend f = function
    | V x -> f x
    | C tt -> C (fun () -> Dist.fmap (extend f)  (tt ()))

  let bind t f = extend f t
  let fail = C (const [])
  (* let choice xs = C (const (Dist.fmap return xs)) *)
  let choice xs = C (fun () -> Dist.fmap return xs)
end

module Inference3VC = struct

  open Ptypes
  open Monads
  open Dist
  open Prob

  let node l = C (const l)
  let rec md_accum_tree w0 map (w,t) = match t with
    | V x -> MDist.accum (w0 *. w,x) map
    | C tt -> List.fold_left (md_accum_tree (w0 *. w)) map (tt ()) 

  module Explore = ExploreOps (struct 
    open Pair

    type 'a m = 'a VCM.m

    let print f t = ()
    let accum w0 ch md = md_accum_tree w0 md (one,ch)

    let flatten depth tree =
      let rec bfold d w0 s0 (w,t) = match t with
        | V x -> MDist.accum (w*.w0,x) $> s0
        | C tt -> if d<=0 then cons (w*.w0, t) <$ s0 
                     else List.fold_left (bfold (d-1) (w*.w0)) s0 (tt ()) 

      in let rec ufold w0 s0 (w,t) = match t with
        | V x -> MDist.accum (w*.w0,x) s0
        | C tt -> List.fold_left (ufold (w*.w0)) s0 (tt ())

      (* choose bounded or unbounded depending on depth option *)
      in let (nodes,leaves) = match depth with 
        | Some depth -> bfold depth one ([],MDist.empty) (one, tree)
        | None -> ([],ufold one MDist.empty (one, tree)) 

      in node (MDist.foldl (fun (w,x) ts -> (w,V x) :: ts) leaves nodes)
  end)


  module Sampler (X : PROB) : sig
    open Explore

    type 'a xm = 'a X.m

    val sample_rejection_mdist  : ('a, (int * 'a mapdist) transformer) sampler
    val sample_importance_mdist : int -> ('a, 'a mapdist transformer) sampler

    val xreify_sampler : ('a,'b) sampler -> 'a m -> 'b xm 

  end = struct
    open Explore
    open Pair


    type 'a xm = 'a X.m

    let rec sample_rejection_mdist t (f, m) = match t with 
      | V x -> (f, MDist.accum (one,x) m)
      | C tt -> match tt () with
        | [] -> (succ f,m)
        | d  -> sample_rejection_mdist (X.dist d) (f,m)

    (* split_trees' *)
    let rec split_trees' w0 depth trees mdist = 
      if trees=[] then ((zero,[]),mdist) 
      else if depth=0 then ((one,trees),mdist)
      else 
        let accum w ts (tot,ts') = if tot=zero then ts else (w*.tot, C (const ts'))::ts in
        let split_tree (branches,mdist) (w,t) = match t with 
            | V x -> (branches, MDist.accum (w *. w0, x) mdist)
            | C tt -> accum w branches <$ split_trees' (w *. w0) (depth-1) (tt ()) mdist  in
        normalise' <$ (List.fold_left split_tree ([],mdist) trees)

    (* This version will add leaves to the given mapdist *)
    let sample_importance_mdist depth = 
      let rec sample_weighted w0 tree map = match tree with 
        | V x -> MDist.accum (w0,x) map 
        | C tt -> 
            let ((btot,normed),map') = split_trees' w0 depth (tt ()) map in
            if btot=zero then map' 
            else sample_weighted (w0 *. btot) (X.dist normed) map'
      in sample_weighted one

    let xreify_sampler sampler tree = X.reify (fun () -> sampler tree)
  end
end

module Model (P : Prob.PROB) (L : Prob.SEQ)  = struct
  module PO = Prob.Ops(P)
  include PO
  include P

  let rec observe ll l = if L.equals l ll then () else fail ()

  let rec transp probs octave =
    match (probs,octave) with
    | ([],_) -> []
    | ((p::pt),(n::nt)) -> (p, n) :: transp pt nt

  let transposer probs n = 
    let arr = Array.init 12 (fun i -> transp probs (drop (n+i)  octave)) in
    (* printf "Building transposer by %d--%d...\n" n (n + List.length probs - 1); *)
    fun note -> dist' (arr.(note_to_int note))

  let transpose_dist = [ 0.52, id
                       ; 0.12, L.map (transposer [0.4;0.6] 1)
                       ; 0.06, L.map (transposer [0.5;0.5] 3)
                       ; 0.06, L.map (transposer [0.25;0.5;0.25] 4)
                       ; 0.06, L.map (transposer [0.25;0.5;0.25] 6)
                       ; 0.06, L.map (transposer [0.5;0.5] 8)
                       ; 0.12, L.map (transposer [0.6;0.4] 10) 
                       ]

  let transpose x = (dist transpose_dist) x 

  let rec subtran x = 
    let (z1,z2) = L.split_at (1 + uniform_nat (L.length x - 1)) x in 
    L.append (transform z1) (transform z2)

  and transform x = 
    if flip 0.1 then L.nil
    else let y = transpose x in
         if flip 0.5 then y else subtran y


  let music2_main src dst =
    let input = L.from_list src in
    observe (transform input) dst

  let test_main () = L.to_list (transform (L.from_list [C;C]))
  let transform_list l = L.to_list (transform (L.from_list l))

  (* Testing on a simpler example *)
  let main_simple () = music2_main [A;B;C] [Asharp;C]
  let main_medium () = music2_main [C;A;Gsharp;A] [B;A;B]
  let main_large () = music2_main [E; A; C; E; A; C; B; A; Gsharp; A]
                            [E; D; C; B; A; B]

  let main_model   = (main_large,  "main_large  ")
  let simple_model = (main_simple, "main_simple ")
  let medium_model = (main_medium, "main_medium ")
end

module type INFER = sig
  type 'a m

  val get_samples : int -> (unit -> 'a) -> unit
  val importance_sample : int -> (unit -> 'a) -> float
  val exact_reify : (unit -> 'a) -> 'a m
  val name : string
end

module Infer3VC (P : Prob.PROB with type 'a m = 'a VCM.m) : INFER with type 'a m = 'a VCM.m = struct
  type 'a m = 'a VCM.m

  module I = Inference3VC
  module IO = Prob.InfOps (P) (I.Explore)
  module SI = I.Sampler (Probimps.ImmediateProb)
  module EO = I.Explore

  let name = "Infer3VC"
  let get_samples n thunk = 
    SI.xreify_sampler 
      (EO.collect' n SI.sample_rejection_mdist) 
      (P.reify thunk) ();
    ()

  let importance_sample n thunk = 
    let results = SI.xreify_sampler 
      (EO.collect'' n (SI.sample_importance_mdist 1)) 
      (P.reify thunk) ()
    in (Dist.total (snd results) /. float_of_int n)

  let exact_reify = IO.exact_reify
end

module Infer3 (P : Prob.PROB with type 'a m = 'a ATM.m) = struct
  module I = Inference3
  module IO = Prob.InfOps (P) (I.Explore)
  module SI = I.Sampler (Probimps.ImmediateProb)
  module EO = I.Explore

  type 'a m = 'a ATM.m

  let name = "Infer3"

  let get_samples n thunk = 
    SI.xreify_sampler 
      (EO.collect' n SI.sample_rejection_mdist) 
      (P.reify thunk) ();
    ()

  let importance_sample n thunk = 
    let results = SI.xreify_sampler 
      (EO.collect'' n (SI.sample_importance_mdist' 1)) 
      (P.reify thunk) ()
    in (Dist.total (snd results) /. float_of_int n)

  let exact_reify = IO.exact_reify
end


module Infer2 (P : Prob.PROB with type 'a m = 'a TM.m) = struct
  module I = Inference2
  module IO = Prob.InfOps (P) (I.Explore)
  module SI = I.Sampler (Probimps.ImmediateProb)
  module EO = I.Explore

  type 'a m = 'a TM.m

  let name = "Infer2"
  (* let get_samples n thunk = *) 
  (*   SS.xreify_sample_collector n *) 
  (*     (accum_simple *|* SS.sample_rejection) *) 
  (*     thunk () *)

  let get_samples n thunk = 
    SI.xreify_sampler 
      (EO.collect' n SI.sample_rejection_mdist) 
      (P.reify thunk) ();
    ()

  (* let importance_sample' m n thunk = *)
  (*   SS.xreify_sample_collector n *)
  (*     (accum_weighted *|* SS.sample_importance m) *) 
  (*     thunk () *)

  (* let importance_sample m n thunk = *)
  (*   SI.xreify_sample_collector n *)
  (*     (SI.sample_importance_mdist m) *) 
  (*     thunk () *)

  let importance_sample n thunk = 
    let results = SI.xreify_sampler 
      (EO.collect'' n (SI.sample_importance_mdist 1)) 
      (P.reify thunk) () 
    in (Dist.total (snd results) /. float_of_int n)

  let exact_reify = IO.exact_reify
end

module Infer2A (P : Prob.PROB with type 'a m = 'a TM.m) = struct
  module I = Inference2
  module IO = Prob.InfOps (P) (I.Explore)
  module SI = I.Sampler (Probimps.ImmediateProb)
  module EO = I.Explore

  type 'a m = 'a TM.m

  let name = "Infer2A"

  let get_samples n thunk = 
    SI.xreify_sampler 
      (EO.collect' n SI.sample_rejection_mdist) 
      (P.reify thunk) ();
    ()

  let importance_sample n thunk = 
    let results = 
      (EO.collect'' n (SI.sample_importance_mdist' 1)) 
      (P.reify thunk) 
    in (Dist.total (snd results) /. float_of_int n)

  let exact_reify = IO.exact_reify
end

module InferF (P : Prob.PROB with type 'a m = 'a FTM.m) = struct
  module I = InferenceF
  module IO = Prob.InfOps (P) (I.Explore)
  module SI = I.Sampler (Probimps.ImmediateProb)
  module EO = I.Explore

  type 'a m = 'a FTM.m

  let name = "InferF"

  let get_samples n thunk = 
    SI.xreify_sampler 
      (EO.collect' n SI.sample_rejection_mdist) 
      (P.reify thunk) ();
    ()

  let importance_sample n thunk = 
    let results = SI.xreify_sampler 
      (EO.collect'' n (SI.sample_importance_mdist 1)) 
      (P.reify thunk) () 
    in (Dist.total (snd results) /. float_of_int n)

  let exact_reify = IO.exact_reify
end

module Infer2H (P : Prob.PROB with type 'a m = 'a TM.m) = struct
  module I = Inference2H
  module IO = Prob.InfOps (P) (I.Explore)
  open Dist

  type 'a m = 'a TM.m

  let name = "Infer2H"

  let get_samples n thunk = 
    iterate n (I.sample_rejection_mdist (P.reify thunk)) (0,MDist.empty); ()

  let importance_sample n thunk = 
    total (MDist.to_dist (I.sample_dist n (P.reify thunk))) /. float_of_int n

  let exact_reify = IO.exact_reify
end

module InferH (P : Prob.PROB with type 'a m = 'a VCM.m) = struct
  module H = ProbM
  module I = Inference

  type 'a m = 'a VCM.m

  let name = "InferH"
  let get_samples n thunk = 
    I.rejection_sample_dist (H.random_selector seed) n (vc_to_pv (P.reify thunk)); 
    ()

  let importance_sample nsamples thunk = (* m = 3 *)
    let results = I.sample_dist (H.random_selector seed)
      { I.sample_runner = fun z th -> (iterate nsamples th z,nsamples) }
      (vc_to_pv (P.reify thunk))
      (* (I.shallow_explore 3 (vc_to_pv (P.reify thunk))) *)
    in (Dist.total results)

  let exact_reify thunk = pv_to_vc (I.explore None (vc_to_pv (P.reify thunk)))
end

module Infer4 (P : Prob.PROB with type 'a m = 'a VCM.m) = struct
  module I = Inference4

  type 'a m = 'a VCM.m

  let name = "Infer4"
  let get_samples n thunk = 
    I.rejection_sample_dist n ((P.reify thunk)); 
    ()

  let importance_sample nsamples thunk = 
    let results = I.sample_dist (I.random_selector ()) nsamples 
      (* (I.shallow_explore 3 (vc_to_pv (P.reify thunk))) *)
      (vc_to_pv (P.reify thunk))
    (* in (Dist.total (Dist.MDist.to_dist results)) *)
    in (Dist.total results)

  let exact_reify thunk = pv_to_vc (I.explore None (vc_to_pv (P.reify thunk)))
end

module Test (P : Prob.PROB) (I : INFER with type 'a m = 'a P.m) = struct
  module L = Prob.LList(P) 
  module T = Model (P) (L) 
  open T
  open I

  let run title thunk = printf "%s \t---> " title; 
    Dist.init_random seed;
    try (timeit thunk; ()) with
    | Dynamic.Dynamic -> printf "** Dynamic exception.\n"
    | _               -> printf "** Other exception.\n"

  let timp fname f n (thunk,tname) = 
    run (Printf.sprintf "%s %d %s" fname n tname) 
        $ fun () -> printf "evidence = %g | " (f n thunk)

  let imp = timp "importance_sample" importance_sample 

  let run_all title =
    printf "\n----- %s (%s) -----\n\n" title name;
    run "exact_reify test_main               " (fun () -> exact_reify test_main);
    run "get_samples 10000 main_simple       " (fun () -> get_samples 10000 main_simple);
    (* run "get_samples' 10000 main_simple   " (fun () -> get_samples' 10000 main_simple); *)
    (* run "get_samples 10000 main_simple    " (fun () -> get_samples 10000 main_simple); *)

    imp 1000  simple_model;
    imp 5000  simple_model;
    imp 10000 simple_model;
    imp 2000  medium_model;
    imp 50000 main_model;
    ()
end

(* Lots of PROB implmentations! *)
open Probimps
let _ = 
  (* let module P = MakeRef1 (VCM) in let module TT = Test (P) (Infer3VC (P)) in TT.run_all "MakeRef1(VCM)"; *)
  (* let module P = MakeST (VCM)   in let module TT = Test (P) (Infer3VC (P)) in TT.run_all "MakeST(VCM)"; *)
  (* let module P = MakeST (TM)    in let module TT = Test (P) (Infer2 (P)) in TT.run_all "MakeST(TM)"; *)
  (* let module P = MakeST (VCM)   in let module TT = Test (P) (InferH (P)) in TT.run_all "MakeST(VCM)"; *)


  (* let module P = Hansei         in let module TT = Test (P) (Infer3VC (P)) in TT.run_all "Hansei"; *)
  (* let module P = MakeRef1 (VCM) in let module TT = Test (P) (Infer3VC (P)) in TT.run_all "MakeRef1(VCM)"; *)
 (*
  let module P = MakeRef1 (ATM) in let module TT = Test (P) (Infer3 (P)) in TT.run_all "MakeRef1(ATM)";
  let module P = MakeRef1 (TM)  in let module TT = Test (P) (Infer2 (P)) in TT.run_all "MakeRef1(TM)";
  let module P = MakeRef1 (TM)  in let module TT = Test (P) (Infer2A (P)) in TT.run_all "MakeRef1(TM)";
  let module P = ProbTreeRef1   in let module TT = Test (P) (Infer2 (P)) in TT.run_all "ProbTreeRef1";
  let module P = ProbTreeRef1   in let module TT = Test (P) (Infer2A (P)) in TT.run_all "ProbTreeRef1";
  let module P = MakeRef1 (FTM) in let module TT = Test (P) (InferF (P)) in TT.run_all "MakeRef1(FTM)";

  let module P = ProbTreeRef1   in let module TT = Test (P) (Infer2H (P)) in TT.run_all "ProbTreeRef1";
  let module P = ProbTreeRef2   in let module TT = Test (P) (Infer2H (P)) in TT.run_all "ProbTreeRef2";
  let module P = MakeRef1 (TM)  in let module TT = Test (P) (Infer2H(P)) in TT.run_all "MakeRef1(TM)";
*)
  let module P = Hansei         in let module TT = Test (P) (InferH (P)) in TT.run_all "Hansei";
  let module P = Hansei         in let module TT = Test (P) (Infer4 (P)) in TT.run_all "Hansei";
  (* let module P = MakeRef1 (VCM) in let module TT = Test (P) (Infer4 (P)) in TT.run_all "MakeRef1(VCM)"; *)
  let module P = ProbVCRef4     in let module TT = Test (P) (Infer4 (P)) in TT.run_all "ProbVCRef4";
  let module P = ProbVCRef5     in let module TT = Test (P) (Infer4 (P)) in TT.run_all "ProbVCRef5";
  let module P = ProbVCRef6     in let module TT = Test (P) (Infer4 (P)) in TT.run_all "ProbVCRef6";
  ()


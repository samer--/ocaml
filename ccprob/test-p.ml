open Utils
open Dist
open Printf

module Test (P : Prob.PROB) = struct
  module PO = Prob.Ops(P)
  include PO
  include P

  type coin = Heads | Tails
  let string_of_coin = function Heads -> "heads" | Tails -> "tails"

  let die () = uniform [1;2;3;4;5;6]
  let coin () = uniform [Heads;Tails]
  let thrower k = let dom = 1--k in memo (fun n -> uniform dom)
  let flipper () = memo (fun n -> let c=coin () in printf "coin %d = %s\n" n (string_of_coin c); c)

  let curry () =
    let meat = uniform ["meat";"chicken";"fish"]
    and sauce = uniform ["rogon";"dopiaza";"bhuna";"dhansak"]
    and starch = uniform ["pilau rice";"plain naan"] in
    if meat="fish" && sauce="dhansak" then fail (); (* just wrong *)
    meat^" "^sauce^" with "^starch

  let grass () = 
    let rain = bernoulli (1%2)
    and sprinkler = bernoulli (1%5)
    in let wet = bernoulli (1%10) && rain 
              || bernoulli (1%5) && sprinkler 
              || bernoulli (1%2)
    in if wet then rain  else fail ()

  (* palindromic coin flips *)
  let test0 () = let f=flipper () in List.map f [1;2;3;2;1]

  let test1 () =  
    let x=dist [1%5,1;4%5,2] in 
    match x with 
    | 1 -> uniform [1;2]::x::[] 
    | 2 -> let y =uniform [1;2;3;4;5;6;7;8] in 
        if y>2 then fail (); y::x::[]

  let test2 () =
    match uniform [1;2;3;4] with
    | 1 -> [1;uniform [1;2]]
    | 2 -> 
      (match dist [1%4,1; 1%4,2; 1%2,3] with
      | 1 -> [2;1]
      | 2 -> let z = uniform [1;2] in fail ()
      | 3 -> fail ())
    | 3 -> [3;1]
    | 4 -> [3;2]

  (* let rec iterate n f x = *) 
  (*   if n=0 then x *) 
  (*   else (Printf.printf "it %d\n" n; *) 
  (*         iterate (n-1) f (f x)) *)

  let big_test n () =
    iterate n (fun n -> Printf.printf "thinking...\n"; (n + die ()) mod 6) 0


  let roller () = memo (fun k -> let n = die () in printf "rolled a %d.\n" n; n)

  let test_nest () = roller () 1
end

module F = Format

(* Lots of PROB implmentations! *)
open Probimps
(* module P = ProbTree *)
(* module P = Make (TreeM) *)
(* module P = MakeRef (TreeM) *)
module P = MakeRef1 (WTreeAltM)
(* module P = MakeRef2 (TreeM) *)
(* module P = Make (TreeM) *)
(* module P = ProbTree *)
(* module P = ProbTreeRef *)
(* module P = ProbTreeRef1 *)

module I = Inference2.Make (P)

module SS = I.Sampler (Make(Monads.SampleEM))
module ST = I.Sampler (Make(TreeM))
module SI = I.Sampler (ImmediateProb)
module T = Test(I)
open I
open T

let int_list = F.list " " F.int
let int_pair = F.pair "," F.int F.int
let ( *|* ) = fmap_sampler

let get_samples n thunk = 
  SS.xreify_sample_collector n 
    (accum_simple *|* SS.sample_rejection) 
    thunk ()

let get_samples' n thunk = 
  SS.xreify_sampler 
    (I.collect' n SS.sample_rejection_mdist) 
    (reify thunk) ()

let get_samples'' n thunk = 
  SI.xreify_sampler 
    (I.collect' n SI.sample_rejection_mdist) 
    (reify thunk) 

let importance_sample m n thunk =
  SS.xreify_sample_collector n
    (SS.sample_importance_mdist m) 
    thunk ()

let importance_sample' m n thunk =
  SS.xreify_sample_collector n
    (accum_weighted *|* SS.sample_importance m) 
    thunk ()

let importance_tree m thunk =
  SS.xreify_sampler (SS.sample_importance_tree m) (reify thunk) ()

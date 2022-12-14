let expensive_f x = Printf.printf "expensive function\n"; x

type 'a lcons = LNil | LCons of (unit -> 'a) * 'a llist
and  'a llist = unit -> 'a lcons
;;

let nil  = fun () -> LNil;;
let cons h t = fun () -> LCons (h,t);;

let rec lappend (y : 'a llist) (z : 'a llist) =
  letlazy (fun () -> 
  match y () with
  | LNil -> z ()
  | LCons (h,t) -> LCons (h, lappend t z));;

let lhead (x : 'a llist) = 
  match x () with LCons (h,_) -> h | LNil -> fail ()
;;

let ltail (x : 'a llist) = 
  match x () with LCons (_,t) -> t | LNil -> fail ()
;;

let lreflect x = x ();;


(* A simple illustration and test of lazy lists, due to Ken *)
let rec list_length_at_most max l = 
  if max <= 0 then 0 else 
  match l () with
    | LNil -> 0
    | LCons (_,thunk) -> 1 + list_length_at_most (pred max) thunk
;;

let test_ll_at_most () =
  let rec count n () =
    dist [(0.5, LNil); 
	  (0.5, LCons ((fun () -> n), letlazy (count (succ n))))] in
  list_length_at_most 5 (letlazy (count 0))
;;
(* let () = assert ( *)
(*   exact_reify test_ll_at_most *)
(*    = [(0.03125, V 5); (0.03125, V 4); (0.0625, V 3); (0.125, V 2); *) 
(*       (0.25, V 1); (0.5, V 0)] *)
(* );; *)



let pcfg_model () =
  let noun () = 
    let x = letlazy (fun () -> dist [(0.4, "flies"); (0.6, "ants")])
    in LCons (x, nil) in
  let rec np () = let np = letlazy np in
                  dist [ (0.7, noun); (0.3, lappend noun np)] () in
  np ();;

(* Various warm-up tests *)
let pcfg11 () =
  let np = pcfg_model () in
  (lreflect (lhead (fun () -> np)),
   lreflect (lhead (fun () -> np)));;

(* let () = assert ( *)
(*   exact_reify pcfg11 *)
(*  =  [(0.399999999999999967, V ("flies", "flies")); (0.6, V ("ants", "ants"))] *)
(*  );; *)
(* Indeed, this is the probability of just flies vs ants, see noun. 
   IBAL gives the same result on this example.
*)


let pcfg12 () =
  let np = pcfg_model () in
  (lreflect (lhead (ltail (fun () -> np))),
   lreflect (lhead (ltail (fun () -> np))));;

(* let () = assert ( *)
(*   exact_reify pcfg12 *)
(*  = [(0.12, V ("flies", "flies")); (0.18, V ("ants", "ants"))]);; *)

let pcfg13 () =				(* a simpler example *)
  let np = pcfg_model () in
  (lreflect (lhead (ltail (fun () -> np))),
   lreflect (lhead (ltail (fun () -> np))),
   lreflect (lhead (fun () -> np)),
   lreflect (lhead (fun () -> np)));;

(* let () = assert ( *)
(*   exact_reify pcfg13 *)
(* = *) 
(* [(0.048, V ("flies", "flies", "flies", "flies")); *)
(*  (0.0720000000000000084, V ("flies", "flies", "ants", "ants")); *)
(*  (0.072, V ("ants", "ants", "flies", "flies")); *)
(*  (0.108, V ("ants", "ants", "ants", "ants"))]);; *)

(* Memoization seems to be working. Now we try the full example. *)

let pcfg () =
  let x = observe (fun x -> lreflect (lhead (const x)) = "flies")
                  pcfg_model in
  (lreflect (lhead (const x)),
   lreflect (lhead (ltail (const x))))
;;

(* let () = assert ( *)
(*   exact_reify pcfg *)
(* = [(0.048, V ("flies", "flies")); (0.072, V ("flies", "ants"))]);; *)

(* Notice that IBAL gives the same result: 0.4 *. 0.18 = 0.072.
   IBAL gives the rejection probability 0.4 whereas we give
   0.048 + 0.072 = 0.12. The factor 0.3 is because our test
   (lhead (ltail (fun () -> x))) reports failure when the list
   has only one element, whereas IBAL takes it as mere FALSE.

   The exploration/reification/memoization
   gives quite a more precise result, by exploring only 9 worlds
*)

(* The following is essentially the exact solution *)
(* let () = assert ( *)
(*   sample_importance (random_selector 1) 100 pcfg *)
(* = *)
(* [(0.0480000000000000357, V ("flies", "flies")); *)
(*  (0.0720000000000000501, V ("flies", "ants"))]);; *)

(* without shallow_explore 3:
 = [(0.0544000000000000386, V ("flies", "flies"));
    (0.0816000000000000614, V ("flies", "ants"))]);;
*)

(* ------------------------------------------------------------------------
 * Example illustrating laziness and memoization, and motivating lazy
 * data structures. The example has the flavor of the IBAL music example:
 * computing a data structure (a list) and comparing the result
 * with the observed value. The mis-match in one field means the disagreement
 * with the experiment; the other fields don't need to be computed at all.
 * We also demonstrate that memoization of a search tree is not always
 * beneficial (and iin any case, memoization of the search tree 
 * is different from lazy data strcutures).
 *)

(* The running example: uniform distribution of n-digit numbers.
   Each number is represented as a sequence of digits.
   We first use ordinary lists.
   Our observation: a number with all ones.
   See the corresponding example in probM.hs
*)

let rec full_10tree = function 
    | 1 -> [uniform_nat 10]
    | n -> let x  = uniform_nat 10 in
	   let xs = full_10tree (pred n) in
	   x::xs
;;

let rec ones n l =
    match (n,l) with
    | (0,[])     -> true
    | (n,(1::r)) -> ones (pred n) r
    | _          -> false
;;


let full_10tree_obs n () = 
  if ones n (full_10tree n) then () else fail ()
;;


(* let [(0.12, V ())] = *) 
(*   sample_rejection (random_selector 17) 100 (full_10tree_obs 1);; *)

(*
The following finished within a minute, and seem to run with constant
memory; the total OCaml heap was 5MB. In constrast, the corresponding
Haskell code required 1.1GB, more then 5 minutes, and still didn't finish.

sample_reify 17 20000 (full_10tree_obs 10);;
- : unit pV = []
*)

(* The instrumented version showing that the whole list is being
   built first, and only then compared againts the observation.
*)
let rec full_10tree = function 
    | 1 -> Printf.printf "Building a leaf\n";
	   [uniform_nat 10]
    | n -> Printf.printf "Building a node at level %d\n" n;
	   let x  = uniform_nat 10 in
	   let xs = full_10tree (pred n) in
	   x::xs
;;

let full_10tree_obs n () = 
  let t = full_10tree n in
  Printf.printf "Evaluating tree\n";
  if ones n t then () else fail ()
;;

(*
sample_rejection (random_selector 17) 20 (full_10tree_obs 4);;

shows that we alsways build the whole list before evaluating it against
the experiment.
*)


(* The output of the following

sample_importance (random_selector 17) 20 (full_10tree_obs 4);;

demonstrates the look-ahead beam and `bundling' of the evaluation decisions.
Still, the probability is too low to be detected by either sampling.

20 samples is too few to estimate probability for 10^(-4)
*)

(* Now we build a lazy list *)

let rec full_10ltree = function 
    | 1 -> Printf.printf "Building a leaf\n";
	   let x = letlazy (fun () -> uniform_nat 10) in
	   LCons (x, fun () -> LNil)
    | n -> Printf.printf "Building a node at level %d\n" n;
	   let x  = letlazy (fun () -> uniform_nat 10) in
	   let xs = letlazy (fun () -> full_10ltree (pred n)) in
	   LCons (x, xs)
;;

let rec lones n l =
    match (n,l ()) with
    | (0,LNil) -> true
    | (n,LCons (h,t))   -> h () = 1 && lones (pred n) t
;;

let full_10ltree_obs n () = 
  let t = full_10ltree n in
  Printf.printf "Evaluating tree\n";
  if lones n (fun () -> t) then lhead (fun () -> t) () else fail ()
;;

(*
sample_rejection (random_selector 17) 20 (full_10ltree_obs 4);;
Building a node at level 4
Evaluating tree
Building a node at level 3
Building a node at level 3
Building a node at level 3
Building a node at level 3
Building a node at level 3
rejection_sample: done 20 worlds

This shows that the full list has never been constructed: we fail already
at checking the first element of the list
*)

(* let [(0.000100000000000000032, V 1)] *) 
(*     = sample_importance (random_selector 17) 1 (full_10ltree_obs 4);; *)
(* (1* Now, we arrive at the exact probability by sampling only 1 worlds *1) *)

(* A simplification of the example above, from digits to bools *)

let rec flips p = function
    | 0 -> []
    | n -> let x  = flip p in
           let xs = flips p (n - 1) in
           x :: xs

let rec trues n xs = match (n, xs) with
    | (0, [])      -> true
    | (n, (x::xs)) -> x && trues (n - 1) xs

(* let [] = sample_importance (random_selector 17) 2000 *)
(*             (fun () -> if trues 20 (flips 0.5 20) then () else fail ());; *)

(* let rec flips p = function *)
(*     | 0 -> LNil *)
(*     | n -> let x  = letlazy (fun () -> flip p) in *)
(*            let xs = letlazy (fun () -> flips p (n - 1)) in *)
(*            LCons (x, xs) *)

(* let rec trues n xs = match (n, xs) with *)
(*     | (0, LNil)         -> true *)
(*     | (n, LCons (x,xs)) -> x () && trues (n - 1) (xs ()) *)
(* ;; *)

(* let () = *)
(* let [(p, V ())] = sample_importance (random_selector 17) 1 *)
(*             (fun () -> if trues 20 (flips 0.5 20) then () else fail ()) *)
(* in assert (p = 1. /. 2. ** 20.);; *)

(* let [(p, V true)] = sample_importance (random_selector 17) 1 *)
(*             (fun () -> let ts = flips 0.5 20 in *) 
(* 	               if trues 20 ts then lhead (fun () -> ts) () else fail ()) *)
(* in assert (p = 1. /. 2. ** 20.);; *)

let test1m () =
  let f x = dist [ (0.5,x); (0.5, x+1) ] in
  let c = flip 0.5 in
  if c then
    (c, f 1, f 1, f 2, f 2)
  else
    (c, f 2, f 2, f 1, f 1)
;;

(* Without memoization, two applications of f 1 can give two different
   results, even in the same world.
*)

(* let *)
(* [(0.03125, V (true, 2, 2, 3, 3)); (0.03125, V (true, 2, 2, 3, 2)); *)
(*  (0.03125, V (true, 2, 2, 2, 3)); (0.03125, V (true, 2, 2, 2, 2)); *)
(*  (0.03125, V (true, 2, 1, 3, 3)); (0.03125, V (true, 2, 1, 3, 2)); *)
(*  (0.03125, V (true, 2, 1, 2, 3)); (0.03125, V (true, 2, 1, 2, 2)); *)
(*  (0.03125, V (true, 1, 2, 3, 3)); (0.03125, V (true, 1, 2, 3, 2)); *)
(*  (0.03125, V (true, 1, 2, 2, 3)); (0.03125, V (true, 1, 2, 2, 2)); *)
(*  (0.03125, V (true, 1, 1, 3, 3)); (0.03125, V (true, 1, 1, 3, 2)); *)
(*  (0.03125, V (true, 1, 1, 2, 3)); (0.03125, V (true, 1, 1, 2, 2)); *)
(*  (0.03125, V (false, 3, 3, 2, 2)); (0.03125, V (false, 3, 3, 2, 1)); *)
(*  (0.03125, V (false, 3, 3, 1, 2)); (0.03125, V (false, 3, 3, 1, 1)); *)
(*  (0.03125, V (false, 3, 2, 2, 2)); (0.03125, V (false, 3, 2, 2, 1)); *)
(*  (0.03125, V (false, 3, 2, 1, 2)); (0.03125, V (false, 3, 2, 1, 1)); *)
(*  (0.03125, V (false, 2, 3, 2, 2)); (0.03125, V (false, 2, 3, 2, 1)); *)
(*  (0.03125, V (false, 2, 3, 1, 2)); (0.03125, V (false, 2, 3, 1, 1)); *)
(*  (0.03125, V (false, 2, 2, 2, 2)); (0.03125, V (false, 2, 2, 2, 1)); *)
(*  (0.03125, V (false, 2, 2, 1, 2)); (0.03125, V (false, 2, 2, 1, 1))] *)
(*  = *)
(*   exact_reify test1m;; *)

let test2m () =
  let f' x = dist [ (0.5, x); (0.5, x+1) ] in
  let f = memo f' in
  let c = flip 0.5 in
  if c then
    (c, f 1, f 1, f 2, f 2)
  else
    (c, f 2, f 2, f 1, f 1)
;;

(* With memoization, f 1 always gives the same result, in the same world. *)
(* let *)
(* [(0.125, V (true, 2, 2, 3, 3)); (0.125, V (true, 2, 2, 2, 2)); *)
(*  (0.125, V (true, 1, 1, 3, 3)); (0.125, V (true, 1, 1, 2, 2)); *)
(*  (0.125, V (false, 3, 3, 2, 2)); (0.125, V (false, 3, 3, 1, 1)); *)
(*  (0.125, V (false, 2, 2, 2, 2)); (0.125, V (false, 2, 2, 1, 1))] *)
(*  = *)
(*   exact_reify test2m;; *)

(* nested memoization *)
let test3m () =
  let f' x = dist [ (0.5,x); (0.5, x+1) ] in
  let f = memo f' in
  let g = memo (fun x -> dist [ (0.5, let u = f x in fun () -> u); 
				(0.5, fun () -> f x) ] ()) in
  let c = flip 0.5 in
  if c then
    (c, f 1, g 1, f 1, g 1)
  else
    (c, g 1, f 1, g 1, f 1)
;;

(* let *)
(* [(0.25, V (true, 2, 2, 2, 2)); (0.25, V (true, 1, 1, 1, 1)); *)
(*  (0.25, V (false, 2, 2, 2, 2)); (0.25, V (false, 1, 1, 1, 1))] *)
(* = *)
(*   exact_reify test3m;; *)


(* The famous sprinkle example:  given that the grass is wet on a given
    day, did it rain (or did the sprinkler come on)? 
*)

let rain_str = 0.9 
and rain_prior = 0.3 
and sprinkler_str = 0.8 
and sprinkler_prior = 0.5
and grass_baserate = 0.1
;;

let rain day = flip rain_prior;;
let sprinkler day = flip sprinkler_prior;;

let noisy_or a astrength b bstrength baserate =
  (flip astrength && a ()) ||
  (flip bstrength && b ()) ||
  flip baserate;;

let grass_model0 () =
  let rain         = memo rain 
  and sprinkler    = memo sprinkler in
  let grass_is_wet = memo (fun day ->
    noisy_or
      (fun () -> rain day) rain_str
      (fun () -> sprinkler day) sprinkler_str
      grass_baserate) in
  grass_is_wet 2 = grass_is_wet 2
;;

(* let [(1., V true)] = exact_reify grass_model0;; *)
(* (1* 11 worlds are examined *1) *)

let grass_model1 () =
  let rain         = memo rain 
  and sprinkler    = memo sprinkler in
  let grass_is_wet = memo (fun day ->
    noisy_or
      (fun () -> rain day) rain_str
      (fun () -> sprinkler day) sprinkler_str
      grass_baserate) in
  observe (fun _ -> grass_is_wet 2) (fun () -> rain 2)
;;

(* let [(0.2838, V true); (0.322, V false)] = *)
(*   exact_reify grass_model1;; *)
(* reify: done; 10 accepted 6 rejected 0 left *)


(* ------------------------------------------------------------------------
 * Lazy vs. delayed evaluation
 *
 * Lazy evaluation means that an expression whose result is not used
 * is not evaluated. That strategy is only sound if the left unevaluated
 * expression could not have failed, that is, it is either deterministic
 * or its cumulative probability is 1.0. If an expression may fail,
 * we have to evaluate it anyway, to properly account for its weight
 * in the final probability of evidence. 
 *
 * Thus lazy evaluation is a semi-unsound optimization. 
 * Lazy evaluation is sound if `observe' (which may fail) appears only 
 * at the end of the program and no intermediate computations include 
 * `observe'. Lazy evaluation is sound if we are only interested in 
 * the ratios of final probabilities rather than their absolute values, 
 * and we don't care of the exact probability of evidence.
 * On all other occassions, we should use delayed evaluation.
 *)

let testd1 () =
   let u = letlazy (fun () -> dist [(0.5, 1); (0.5, 2)]) in
   let x = letlazy (fun () -> 
     observe (fun u -> u = 1) (fun () ->
     expensive_f (dist [ (0.5, let u' = u() in fun () ->u'); 
                         (0.5, u)] ()))) in
   dist [ (0.5, fun () -> (u(),u())); 
	  (0.5, fun () -> Printf.printf "here\n"; (x() ,x ()))] ()
;;

(* let [(0.25, V (2, 2)); (0.5, V (1, 1))] *)
(*  = *)
(*   exact_reify testd1;; *)
(* Expensive function is printed 4 times; 
reify: done; 4 accepted 2 rejected 0 left
*)

(* The corresponding IBAL code:

1st attempt:
 let u () = dist [ 0.5: 1, 0.5: 2 ] in
 let x () = observe 1 in dist [ 0.5: u(), 0.5: u() ] in
 dist [ 0.5: u(), 0.5: x() ]

./sample delayed.ibl 5
Number of samples = 1152717
Probability of evidence = 0.750322
1 : 0.666417
2 : 0.333583

One can say that IBAL is lazy, and so the IBAL translation should look
as follows:

 let u = dist [ 0.5: 1, 0.5: 2 ] in
 let x = observe 1 in dist [ 0.5: u, 0.5: u ] in
 dist [ 0.5: u, 0.5: x ]

Number of samples = 936188
Probability of evidence = 0.749521
1 : 0.666906
2 : 0.333094

That doesn't seem to affect the results though...
OK, we are in agreement so far.
*)

(* Now, the results are going to be different. *)
let testd2 () =
   let u = letlazy (fun () -> dist [(0.5, 1); (0.5, 2)]) in
   let x = letlazy (fun () -> 
     observe (fun u -> u = 1) (fun () ->
     expensive_f (dist [ (0.5, let u' = u() in fun () ->u'); 
                         (0.5, u)] ()))) in
   let z = (u,x) in
   fst z ()
;;


(* let [(0.5, V 2); (0.5, V 1)] = *)
(*   exact_reify testd2;; *)

(* We have built a data structure that includes unevaluated computation, x.
   We then checked for some other field. So, the result of x () was not
   needed, and so it has not been evaluated. Therefore, the failure in
   it has not been apparent.
 The corresponding IBAL code:
 let u () = dist [ 0.5: 1, 0.5: 2 ] in
 let x () = observe 1 in dist [ 0.5: u(), 0.5: u() ] in
 let z = [u (), x ()] in
 z.CAR

Probability of evidence = 1
1 : 0.500875
2 : 0.499125

Hmm, it is again in agreement with us..

And even if we re-write this as:

 let u = dist [ 0.5: 1, 0.5: 2 ] in
 let x = observe 1 in dist [ 0.5: u, 0.5: u ] in
 let z = [u, x] in
 z.CAR

Number of samples = 748655
Probability of evidence = 1
1 : 0.500113
2 : 0.499887

That seems to be a problem with the version of IBAL we are using.
Ken observed that 

    let x = observe 1 in 2 in 3

should not have any samples, and the public (exact inference) IBAL
agrees with him (the syntax is "let one = 1 in observe one = 2 in 3"),
but the new, sampling IBAL says

    Number of samples = 802545
    Probability of evidence = 1
    3 : 1.000000

*)


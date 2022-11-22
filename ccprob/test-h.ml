open ProbM
open Inference
open Utils

(* to print:
  * DropBox - lazy-nondet.pdf
  * Current - prob - embedpp.pdf
  * delcont - DDBinding.pdf
  *)

module Balls = struct
  type colour = R | B

  let flip_colour = function | B -> R | R -> B

  let colour () = dist [0.5,B; 0.5,R]
  let noisy c = dist [0.8,c; 0.2,flip_colour c]
end

module BallsL = struct
  include Balls
  open List

  let rec rep n f = if n=0 then [] else f () :: rep (n-1) f

  let balls nballs ndraw =
    let ball_colours = rep nballs colour in
    let ball_colour = nth ball_colours in
    let obs_balls = rep ndraw (fun () -> uniform nballs) in
    map ball_colour obs_balls 

  let balls_exp maxballs obs =
    let nballs = 1 + uniform maxballs in 
    if obs=balls nballs (length obs) then nballs else fail ()
end

module BallsA = struct
  include Balls
  open Array

  let rep n f = init n (fun _ -> f ())
  let balls nballs ndraw =
    let ball_colours = rep nballs colour in
    let ball_colour = get ball_colours in
    let obs_balls = rep ndraw (fun () -> uniform nballs) in
    map ball_colour obs_balls 

  let balls_exp maxballs obsL =
    let obs = Array.of_list obsL in
    let nballs = 1 + uniform maxballs in 
    if obs=balls nballs (length obs) then nballs else fail ()
end

module LazyBalls = struct
  include Balls

  type 'a stream = Cons of 'a * (unit -> 'a stream)

  let rec map f st () = let Cons (x,st') = st () in Cons (f x,map f st')

  (* There is a problem with this. |balls| has type:
   *   balls : int -> unit -> 'a stream
   * If this stream leaks outside a prompt, forcing the tail of
   * the stream causes a 'no prompt set' error.
   *)

  let balls nballs =
    let ball_colour = memo (fun i -> colour ()) in
    let rec ball_stream () = Cons (uniform nballs, ball_stream)
    in map (noisy ** ball_colour) ball_stream

  let balls_exp maxballs obs =
    let rec match_stream_list str = function
      | [] -> ()
      | x::xs -> 
        let Cons (y,str') = str () in
        if not (x=y) then fail ();
        match_stream_list str' xs in
    let nballs = 1 + uniform maxballs in 
    match_stream_list (balls nballs) obs;
    nballs

  (* to do: try reification by sampling *)
end

module HMM = struct
  type state = int
  type obs = int

  let numstates = 5

  let probs_to_dist = 
    let rec p2d n = function | [] -> [] | p::ps -> (p,n) :: p2d (succ n) ps
    in p2d 0 

  let discrete ps = dist (probs_to_dist ps)
  let trans transmat k = discrete (Array.get transmat k) 
  let obs obsmat k = discrete (Array.get obsmat k)
end
    
module Test = struct

  type coin = Heads | Tails
  let string_of_coin = function Heads -> "heads" | Tails -> "tails"

  let die () = uniformly [|1;2;3;4;5;6|]
  let coin () = uniformly [|Heads;Tails|]
  let thrower k = let dom = Array.of_list (1--k) in memo (fun n -> uniformly dom)
  let flipper () = memo (fun n -> let c=coin () in Printf.printf "coin %d = %s\n" n (string_of_coin c); c)


  (* palindromic coin flips *)
  let test0 () = let f=flipper () in List.map f [1;2;3;2;1]

  let test1 () =  
    let x=dist [0.2,1;0.8,2] in 
    match x with 
    | 1 -> uniformly [|1;2|]::x::[] 
    | 2 -> let y =uniformly [|1;2;3;4;5;6;7;8|] in 
        if y>2 then fail (); y::x::[]

  let test2 () =
    let x=uniformly [|1;2|] in
    if x=1 then [1;uniformly [|1;2|]]
    else 
      let y = dist [0.25,1; 0.25,2; 0.5,3] in
      match y with
      | 1 -> [x;y]
      | 2 -> let z = uniformly [|1;2|] in fail ()
      | 3 -> fail ()

  let print string_of_val tree = 
    let open Ptypes in 
    let rec print_aux prefix (w,tree) = 
      Printf.printf "%s-%5.3f:" prefix w;
      match tree with
      | V x -> print_endline (" "^string_of_val x)
      | C tst -> print_endline "-\\"; List.iter (print_aux (prefix^"       |")) (tst ())
    in print_aux " " (1.0,C (const tree))
end

module F = Format

let hist k string_of_val dist =
  let open Ptypes in 
  let string_and_len = function 
    | (V x) -> let l=string_of_val x in (l,String.length l)
    | (C _) -> ("---",3) in
  let labdist = List.map (fun (w,v) -> (w,string_and_len v)) (snd (normalize dist)) in
  let label_width = List.fold_left max 0 (List.map (snd ** snd) labdist) in
  let print_row (w,(label,len)) =
    print_string label; print_string (String.make (label_width-len) ' ');
    print_string ":"; print_endline (String.make (int_of_float (k *. w)) '#') in
  List.iter print_row labdist

let hist100 = hist 100.0



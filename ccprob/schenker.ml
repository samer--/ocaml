open BatPervasives
open Utils
open Prob
open Monads
open Grammar
open Dist

(* module assignments *)
module BTree = Lazydata.BTree
module Mod12 = Modulo(struct let modulus=12 end)
module P = Probimps.ProbTreeRef1
module PG = Grammar.Make (P)
module PO = Prob.Ops (P)
module InfH = Inference2H
module Inf2 = Inference2
module SI = Inf2.Sampler (Probimps.ImmediateProb)
module IO = InfOps (P) (Inf2.Explore)


let un_option (Some x) = x
let importance_sample n f = MDist.to_dist (InfH.sample_dist n (P.reify f))
let importance_sample' m n f = SI.xreify_sampler (SI.sample_importance_dist n m) (P.reify f) ()

open Mod12
open PG
open PO
open P
open IO

type 'a set = 'a list
type 'a sequence = 'a list

type duration = int (* rational *)
type pitch = int
type pitch_class = int (* modulo 12 *)
type tie = O | T
type inheritance = First | Second | Either | Both | IV
type harmony = pitch_class set

type note = Rest | Note of tie * pitch

let penta = [0;3;5;7;10]
let minor = [0;2;3;5;7;8;10]
let major = [0;2;4;5;7;9;11]

let duration seq = sum (List.map fst seq)
let note dur p = (1, Note (O,p))
let pitch_class (p:int) : pitch_class = Mod12.fix p
let string_of_note = function 
  | Rest -> "rest"
  | Note (_,p) -> string_of_int p

let highest notes = 
  let higher x y = match (x,y) with
  | (Note (t1,p1), Note (t2,p2)) -> if p2>p1 then Note (t2,p2) else Note (t1,p1)
  | (Rest, Note (t1,p1)) -> Note (t1,p1) in
  List.fold_left higher Rest notes

(* selects the highest pitches from a sequence of chords *)
let topline surf = List.map (fun (dur,notes) -> (dur, highest notes))  surf

type 'a analysis = Term of duration * note | Prod of ('a * 'a analysis list)

let pprint string_of_info a = 
  let rec pp pref = function 
    | Term (dur,note) -> Printf.printf "%s %s %s %d:%s\n" 
        pref (string_of_note note) (String.make (20-String.length pref) '.') dur (string_of_note note)
    | Prod (info,sub) -> Printf.printf "%s %s\n" pref (string_of_info info);
        List.iter (pp (pref^" :")) sub; print_endline (pref ^ " ^"); in
  (print_endline ""; pp " " a; print_endline "")

let rec skeleton = let open BTree in function
  | Term _ -> Leaf
  | Prod (_, [a1;a2]) -> Node ((), skeleton a1, skeleton a2)

let rec fmap_analysis f = function
    | Term (d,n) -> Term (d,n)
    | Prod (info,ax) -> Prod (f info, List.map (fmap_analysis f) ax)

(* takes a monophonic line (=duration * note list) and produces a list of
 * duration * pitch events *)
let coalesce line =
  let step (prev,acc) (d,note) =
    match (prev,note) with
    | (Some (p0,d0), Note (O,p)) -> (Some (p,d), (d0,Some p0) :: acc)
    | (Some (p0,d0), Note (T,p)) -> if p0=p then (Some (p0,d0+d), acc) else failwith "Pitch mismatch"
    | (Some (p0,d0), Rest)       -> (None, (d0,Some p0) :: acc)
    | (None,         Note (T,_)) -> failwith "No previous note" 
    | (None,         Note (O,p)) -> (Some (p,d), acc) 
    | (None,         Rest)       -> (None, acc) 
  in List.rev (match List.fold_left step (None,[]) line with
            | (None, acc) -> acc
            | (Some (p0,d0), acc) -> (d0,Some p0) :: acc)


let sum_of k f () = sum (repeat k f)

let rec binomial_tree k = exact_reify (fun () -> 
  if k=0 then 0 else bernoulli 0.5 + reflect (binomial_tree (pred k)))

let rec binomial k = if k=0 then 0 else bernoulli 0.5 + variable_elim binomial (pred k)

let binomial_24 = binomial_tree 24


module type DURATION = sig
  type ldur

  val delay_dur : duration -> ldur
  val force_dur : ldur -> duration
  val split_duration : ldur -> ldur * ldur
end

module type PITCH = sig
  type lpitch

  val force_pitch : lpitch -> pitch
  val neighbour : lpitch -> lpitch
  val consonant : harmony -> lpitch -> lpitch
  val diff : lpitch -> lpitch -> lpitch
  val rand_pitch : harmony -> lpitch
  val rand_skip : harmony -> lpitch -> lpitch
end

module StrictPitch = struct
  type lpitch = pitch
  type lnote = LNote of tie * lpitch | LRest

  let force_pitch p = p
  let neighbour p  = p + uniform [-2;-1;1;2]
  let consonant h p = if List.mem (fix p) h then p else fail ()
  let diff p q = if p=q then fail () else q
  let rand_pitch harm = uniform harm + 12 * uniform_range 0 3
  let rand_skip harm p = 
    (* p + uniform harm + 12 * uniform_range (-1) 1 *)
    consonant harm (p + reflect binomial_24 - 12) 
end

module StrictDur = struct
  type ldur = duration

  let delay_dur d = d
  let force_dur d = d
  let split_duration d = 
    let d1 = uniform_range 0 ((d-1)/2) + uniform_range 1 (d/2) in (d1, d-d1)
    (* let d1 = uniform_range 1 (d-1) in (d1, d-d1) *)
end

module LazyPitch : PITCH = struct
  type lpitch = pitch thunk

  let force_pitch p = p ()
  let neighbour p     = letlazy (fun () -> StrictPitch.neighbour (p ()))
  let consonant h p   = letlazy (fun () -> StrictPitch.consonant h (p ()))
  let diff p q        = letlazy (fun () -> StrictPitch.diff (p ()) (q ()))
  let rand_pitch harm = letlazy (fun () -> StrictPitch.rand_pitch harm)
  let rand_skip harm p= letlazy (fun () -> StrictPitch.rand_skip harm (p ()))
end

module LazyDur = struct
  type ldur = duration thunk
  let delay_dur d () = d
  let force_dur d = d ()
  let split_duration d = 
    let ld = letlazy (fun () -> StrictDur.split_duration (d ())) in
    (fst ** ld, snd ** ld)
end

module StrictMonophonic : EQ = struct
  type t = duration * note
  let eq = ( = )
end

module LazyMonophonic : EQ = struct
  type t = duration thunk * note thunk
  let eq (d1,n1) (d2,n2) =
    if d1 () <> d2 () then false
    else n1 () <> n2 ()
end

module Schenker (W : GRAMMAR with type t = duration * note) = struct
  include DirectGrammar (W)
  open LazyPitch
  open LazyDur

  type lnote = LNote of tie * lpitch | LRest

  let force_note = function 
    | LRest -> Rest
    | LNote (t, p) -> Note (t, force_pitch p)

  (* only for parsing lists *)
  let term' (dur : ldur) (note : lnote) = 
    let matchd d dur = if d <> force_dur dur then fail () in
    let matchp p pp = if p <> force_pitch pp then fail () in
    let (d,n) = input () in
    match (n,note) with
    | Rest, LRest -> matchd d dur; Term (d,n)
    | Note (O,p), LNote (O,lp) -> matchd d dur; matchp p lp; Term (d,n)
    | _ -> fail ()
    
  let term dur note = 
    let (d,n) = input () in
    if d <> force_dur dur then fail ()
    else if n <> force_note note then fail ()
    else Term (d,n)

(*
  (* would work for list of lazy durations and notes
   * ie, type t = duration thunk * note thunk,
   * except it may not compile because thunks cannot be
   * compared for equality *)
  
  let term dur note = 
    let (d,n) = input () in
    if d () <> force_dur dur then fail ()
    else if n () <> force_note note then fail ()
    else Term (d,n)
 *)

(* 
  (* Works for parsing and generating *)
  let term dur note = 
    let n = force_note note in 
    let d = force_dur dur in 
    output (d,n); Term (d,n)
*)

  let top_note h = LNote (O,rand_pitch h)

  let appogiatura p h = ("appogg", LNote (O,neighbour p), LNote (O,p))
  let repetition p h = ("repeat", LNote (O,p), LNote (O,p))
  let delay p h = ("delay", LRest, LNote (O,p))
  let shortening p h = ("shorten", LNote (O,p), LRest)
  let consonant_skip p h = 
    if flip 0.5 then ("skip1", LNote (O,consonant h p), LNote (O,rand_skip h p)) 
    else ("skip2", LNote (O,rand_skip h p), LNote (O,consonant h p))

  let elabs = [ 0.2, consonant_skip
              ; 0.25, appogiatura
              ; 0.30, repetition
              ; 0.13, delay
              ; 0.11, shortening ]

  let elab_note harm note =
     let el = letlazy (fun () -> match note () with
                                 | LRest -> ("rest",LRest,LRest)
                                 | LNote (_,p)  -> dist elabs p harm) in
     let ll = letlazy (fun () -> let (l,_,_)=el () in l) in
     let n1 = letlazy (fun () -> let (_,n,_)=el () in n) in
     let n2 = letlazy (fun () -> let (_,_,n)=el () in n) in
     (ll,n1,n2)

  (* using lazy elaboration decisions, with rest splitting *)
  let rec segment (dur,note,harm) = 
    if flip 0.1 || force_dur dur < 2 then term' dur (note ())
    else 
      let (d1,d2) = split_duration dur in
      let (label,n1,n2) = elab_note harm note in
      let s1 = segment (d1, n1, harm) in 
      let s2 = segment (d2, n2, harm) in 
      Prod ((label, note), [s1;s2]) 

  (* using eager elaboration decisions, no rest splitting *)
  let rec segment' (dur,note,harm) = 
    if flip 0.1 || force_dur dur < 2 then term dur note
    else match note with
    | LRest -> term dur note
    | LNote (_,p) ->
      let (d1,d2) = split_duration dur in
      let (label,n1,n2) = dist elabs p harm in
      let s1 = segment' (d1, n1, harm) in 
      let s2 = segment' (d2, n2, harm) in 
      Prod ((label, note), [s1;s2]) 

  (* using eager elaboration decisions, with rest splitting *)
  let rec segment'' (dur,note,harm) = 
    if flip 0.1 || force_dur dur < 2 then term dur note
    else 
      let (d1,d2) = split_duration dur in
      let (label,n1,n2) = match note with
        | LRest -> ("rest",LRest,LRest)
        | LNote (_,p) -> dist elabs p harm in
      let s1 = segment'' (d1, n1, harm) in 
      let s2 = segment'' (d2, n2, harm) in 
      Prod ((label, note), [s1;s2]) 

  let start dur () = 
    let harm = penta in
    let note = letlazy (fun () -> top_note penta) in
    let force_info (l,n) = (l (), force_note (n ())) in
    fmap_analysis force_info (segment (delay_dur dur, note, harm))

  let start' dur () = 
    let harm = penta in
    let force_info (l,n) = (l, force_note n) in
    fmap_analysis force_info (segment' (delay_dur dur, top_note harm, harm))

  let start'' dur () = 
    let harm = penta in
    let force_info (l,n) = (l, force_note n) in
    fmap_analysis force_info (segment'' (delay_dur dur, top_note harm, harm))
end

module SegGen = RevListBuilder (struct type t = duration * note end)
module SegParse = ListParser (struct type t = duration * note let eq = (=) end) 
module SchG = Schenker (SegGen)
module SchP = Schenker (SegParse)

let gen dur n =
  iterate n (InfH.sample_rejection_mdist 
    (P.reify (fun () -> snd (SegGen.run (SchG.reify' (SchG.start dur) ())))))
    (0,MDist.empty) |> snd |> MDist.to_dist

let parse_with start s = SegParse.parse_all (SchP.reify (start (duration s))) s
let sample_parse pp n s = importance_sample n (fun () -> pp s)
let sample_parse' m pp n s = importance_sample' m n (fun () -> pp s)

let sample_trees m n head obs = 
  sample_parse' m (skeleton ** parse_with head) n (List.map (note 1) obs)

let test n data =
  let sampler head () = sample_trees 2 n head data in
  let run head seed = 
    Random.init seed;
    Printf.printf "\nSeed is %d" seed;
    timeit (sampler head); () in
  List.iter 
    (fun (label,head) -> Printf.printf "\n\n------ %s ------\n\n"  label; 
    List.iter (run head) [1972;1970;1601;1066;1212;808]) 
        ["lazy split", SchP.start]
        (* ["eager split (not rests)",SchP.start'; "eager split", SchP.start''; "lazy split", SchP.start] *)

(* samples over tree structures only - elaboration details are
 * marginalised out *)
let test_trees m n obs () = 
  List.iter (fun (w,a) -> Printf.printf "\n\np=%g.\n" w; BTree.draw a) 
            (List.sort compare (sample_trees m n SchP.start obs))

(* samples over reductions - elaboration labels are marginalised out *)
let test_analyses m n data () = 
  List.iter (fun (w,a) -> Printf.printf "\np=%g.\n" w; pprint string_of_note a) 
                          (* pprint (fun (l,n) -> (string_of_note n)^" >" ^ l) a) *) 
            (List.sort compare (sample_parse' m (fmap_analysis snd ** parse_with SchP.start) n data))

(* let gen () = *) 
(*   let results = sample_rejection (random_selector (Random.int 65535)) 10 *) 
(*       (fun () -> (snd (SegGen.run (SchG.reify' SchG.start ())))) in *)
(*   let (_, Ptypes.V x) :: _ = results in x *)

(* let parse s = SegParse.first_parse (SchP.reify' SchP.start) s *)
(* let parses n s = sample_importance (random_selector (Random.int 65535)) n *)
(*       (fun () -> SegParse.parse_all (SchP.reify SchP.start) s) *)

let mozart284 = "1[D4 D5] 1[A4 _D5] 1[F#4 _D5] 1[A4 _D5] 1[B3 C#5] 1[F#4 D5] 1[D4 E5] 1[F#4 F#5] 1[G3 G5] 1[E4 E5] 1[B3 G5] 1[E4 E5] 1[A3 D5] 1[G4 C#5] 1[E4 B4] 1[G4 A4] 1[D4 F#4 A5] 1[_D4 _F#4 D6] 1[G3 E4 B5] 1[_G3 _E4 G5] 1[A3 D4 F#5] 1[_A3 _D4 A5] 1[A3 C#4 G5] 1[_A3 _C#4 G4 E5] 2[D3 D4 G4 E5] 6[_D3 _D4 F#4 D5]"

let decimal = 
  let rec accum n = function 
  | [] -> n
  | d::dx -> accum (10*n + d) dx
  in accum 0

module AP1 (W : GRAMMAR with type t = char) = struct
  module GO = GrammarOps (W)
  open GO

  let digit () = let n = uniform_range 0 9 in 
                 let c = Array.get [|'0';'1';'2';'3';'4';'5';'6';'7';'8';'9'|] n in
                 output c >> return n

  let integer () = list_of digit >>= fun digits -> return (decimal digits)
  let nominal () = (* pitch class of base note in semitones up from A *)
    let (c,n) = uniform ['A',0;'B',2;'C',3;'D',5;'E',7;'F',8;'G',10] in
    output c >> return n

  let acc () = let (m,n) = uniform [ output '#',1; return (),0; output 'b',(-1) ]
               in m >> return n
  let pitch_class () = nominal () >>= fun n -> acc () >>= fun a -> return (n+a) 
  let pitch () = pitch_class () >>= fun pc -> digit () >>= fun o -> return (pc+12*o)
  let tie () = if flip 0.5 then output '_' >> return T else return O
  let note () = tie () >>= fun t -> pitch () >>= fun p -> return (Note (t,p))
  let bracket m = output '[' >> m >>= fun x -> output ']' >> return x
  let chord () = integer () >>= fun dur -> 
    bracket (if flip 0.5 then list_sep (output ' ') note else return []) >>= fun notes ->
      return (dur,notes)
  let seq () = list_sep (output ' ') chord 
end

(* Parser using direct style representation *)
module AP2 (W : GRAMMAR with type t = char) = struct
  include DirectGrammar (W)
  open P

  let term x () = output x
  let digit () = let n = uniform_range 0 9 in 
                 let c = List.nth ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9'] n in
                 output c; n

  let integer () = decimal (list_of digit)
  let nominal () = (* pitch class of base note in semitones up from A *)
    let (c,n) = uniform ['A',0;'B',2;'C',3;'D',5;'E',7;'F',8;'G',10] in
    output c; n

  let acc () = uniform [ (fun () -> pplus 0.02 (term '#'))
                       ; (fun () -> - pplus 0.02 (term 'b')) 
                       ; (fun () -> 0) ] ()
  let pitch_class () = let n = nominal () in let a = acc () in (n+a)
  let pitch () : pitch = let pc = pitch_class () in let o =  digit () in pc + 12*o
  let tie () = if flip 0.5 then (output '_'; T) else O
  let note () = let t = tie () in let p =  pitch () in (t,p)
  let bracket m = output '['; let x = m () in output ']'; x
  let chord () = let dur : duration = integer () in 
                 (dur, bracket (fun () -> if flip 0.5 then list_sep (term ' ') note else []))
  let seq () = list_sep (term ' ') chord
end

module TChar = struct type t = char end
module CharGen = RevListBuilder (TChar)
module StrP = StringParser
module MP1 = AP1 (StrP)
module MP2 = AP2 (StrP)
module MG1 = AP1 (CharGen)
module MG2 = AP2 (CharGen)

let parse_bf s = un_option $ InfH.Explore.search_bf (P.reify (fun () -> StrP.parse_all (MP1.seq ()) s))
let parse_df s = un_option $ InfH.Explore.search_df (P.reify (fun () -> StrP.parse_all (MP1.seq ()) s))

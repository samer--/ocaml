(* Corpus tests for Utils.pairs (gravity/lib/utils.ml).
   Checks the real OCaml pairs on small lists against hand-computed
   expectations: right count, no self-pairs, coverage, no duplicates.
   Uses only Stdlib arithmetic (no shadowing from symbolic operators). *)

module U = Gravlib.Utils

let failures = ref 0
let count label ok =
  if ok then Printf.printf "ok   %s\n%!" label
  else (incr failures; Printf.printf "FAIL %s\n%!" label)

let length = List.length
let mem = List.mem
let rec distinct = function
  | [] -> true
  | x::xs -> not (mem x xs) && distinct xs

let rec no_duplicates = function
  | [] -> true
  | p::ps -> not (mem p ps) && no_duplicates ps

let rec occurs_before x y = function
  | [] -> false
  | z::zs -> (z = x && mem y zs) || occurs_before x y zs

let () =
  let t0 = U.pairs [] in
  count "empty" (t0 = []);

  let t1 = U.pairs [1] in
  count "singleton" (t1 = []);

  let t2 = U.pairs [1; 2] in
  count "two elements count" (length t2 = 1);
  count "two elements pair" (t2 = [(1, 2)]);

  let t3 = U.pairs [1; 2; 3] in
  count "three elements count" (length t3 = 3);
  count "three elements coverage" (mem (1, 2) t3 && mem (1, 3) t3 && mem (2, 3) t3);
  count "three elements no self" (not (mem (1, 1) t3) && not (mem (2, 2) t3) && not (mem (3, 3) t3));
  count "three elements no duplicates" (no_duplicates t3);

  let t4 = U.pairs [1; 2; 3; 4] in
  count "four elements count" (length t4 = 6);
  count "four elements coverage"
    (mem (1, 2) t4 && mem (1, 3) t4 && mem (1, 4) t4 &&
     mem (2, 3) t4 && mem (2, 4) t4 && mem (3, 4) t4);
  count "four elements no self" (not (mem (1, 1) t4));
  count "four elements no duplicates" (no_duplicates t4);

  let t5 = U.pairs [5; 6; 7; 8; 9] in
  count "five elements count" (length t5 = 10);
  count "five elements no duplicates" (no_duplicates t5);

  (* test on a non-distinct list: duplicates should appear *)
  let t_dup = U.pairs [1; 1; 2] in
  count "dup list has dup pairs" (not (no_duplicates t_dup));

  if !failures = 0 then print_endline "PASS"
  else (Printf.printf "%d FAILURES\n%!" !failures; exit 1)

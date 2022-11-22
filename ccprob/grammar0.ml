(* Grammar0 - Straightforward approach to generating and parsing from pCFG *)
open Utils
open ProbM

(* Grammar tree - type for defining grammar rules *)
type 'a gtree = Phrase of string * 'a gtree thunk list 
              | Term of 'a

(* Parse tree - for representing result of parsing *)
type 'a ptree = Node of string * 'a ptree list
              | Leaf of 'a

type 'a difflist = 'a list -> 'a list

let rec list_of_ptree tree tail = 
  let rec do_trees tail  = (function
    | [] -> tail
    | t::tx -> list_of_ptree t (do_trees tail tx))
  in match tree with
  | Leaf x -> x::tail
  | Node (_,trees) -> do_trees tail trees

let print_ptree string_of_val tree = 
  let rec print_aux prefix tree = 
    Printf.printf "%s-" prefix;
    match tree with
    | Leaf x -> print_endline (" "^string_of_val x)
    | Node (lab,ts) -> print_endline (" "^lab ^" \\"); 
                    let pad = String.make (String.length lab) ' ' in
                    List.iter (print_aux (prefix^pad^"    |")) ts
  in print_aux " " tree


(* generate difference list *)
let rec generate (head : 'a gtree thunk) : 'a ptree * 'a difflist = 
  let rec gen_x (cont,dl1) = (function
    | [] -> (cont [], dl1)
    | h::hx -> let (ptree,dl2) = generate h in
               gen_x (cont ** cons ptree, dl2 ** dl1) hx) in
  match head () with
  | Phrase (l,t) -> gen_x ((fun tx -> Node (l,tx)),id) t
  | Term x     -> (Leaf x,cons x)

(* generate syntax tree and match with obs, tail recursive(ish), 
 * difference list to generate parse tree nodes.  *)
let rec parse1 : 'a gtree thunk -> 'a list -> 'a ptree * 'a list = 
  let rec parse_x cont heads input = match heads with
    | [] -> (cont [],input)
    | h::hx -> let (ptree,rem) = parse_1 h input in
               parse_x (cont ** cons ptree) hx rem 
  and     parse_1 head = match head () with
    | Phrase (l,t) -> parse_x (fun tx -> Node (l,tx)) t
    | Term x -> function 
             | y::ys when x=y -> (Leaf x,ys)
             | _ -> fail ()
  in parse_1

(* useful to check if parse1 consumed all the input *)
let complete ((t,r) : 'b * 'a list) : 'b = if r=[] then t else fail ()

(* parse without generating syntax tree, just return 
 * remaining unparsed input.  *)
let rec parse3 : 'a gtree thunk -> 'a list -> 'a list = 
  let rec parse_1 head input = match head () with
    | Term x -> (match input with | y::ys when x=y -> ys | _ -> fail ())
    | Phrase (l,hx) -> List.fold_left (fun i h -> parse_1 h i) input hx
  in parse_1

(*
open Grammar0
module G1 = struct
  let term x _ = Term x
  let gseq label ts = Phrase (label,ts)
  let (-->) = gseq

  let rec s _ = "S" --> [a;b;a]
  and     a _ = "A" --> dist [0.5,[c;c;c]; 0.5,[d;d;d]]
  and     c _ = "C" --> map term (dist [0.35,[0;0]; 0.35,[1;1]; 0.15,[0;1]; 0.15,[1;0]]) 
  and     d _ = "D" --> map term (dist [0.35,[1;0]; 0.35,[0;1]; 0.15,[0;0]; 0.15,[1;1]])
  and     t x _ = "T" --> [term x]
  and     i n _ = "I" --> match n with 
                          | 0 -> let k = uniform_range 1 5 in
                                 dist [ 0.5, [t n] 
                                      ; 0.25, [i k; i (-k)]
                                      ; 0.25, [i (-k); i k]]
                          | 2 -> dist [ 0.2, [t 2]
                                      ; 0.4, [i 1; i 1]
                                      ; 0.4, [i 2; i 0]
                                      ]
                          | _ -> dist [ 0.7, [t n]
                                      ; 0.3, [i n; i 0]
                                      ] 
                                 (* let m = uniform_bp 0 n in *) 
                                 (* dist [ 0.5, [t n] *)
                                 (*      ; 0.5, [i m; i (n-m) ]] *)
  and     b _ = "B" --> dist [ 0.2, [term 5]
                             ; 0.4, [term 5; b]
                             ; 0.4, [term 4; b]
                             ]
end
*)


(* Corpus tests for the deep simplification rewrite of Sym
   (gravity/lib/symbolic.ml).
   1. evaluation semantics preserved: eval (simplify t) env = eval t env
   2. idempotence on the corpus: simplify (simplify t) = simplify t
   3. the fixed and newly-covered cases, incl. a + (-a) cancellation and the
      0^0 inconsistency (pow 0.0 x = Const 1.0, matching 0.0 ** 0.0 = 1.0).

   NOTE: Sym is accessed qualified (module S) because Sym overloads the
   addition and multiplication operators for terms; arithmetic here stays
   Stdlib. *)

module S = Gravlib.Symbolic.Sym

module IntMap = Map.Make (Int)

let ( + ) = S.( + )
let ( * ) = S.( * )

let v0 = S.Var (0, "q0x")
let v1 = S.Var (1, "q1x")
let v2 = S.Var (2, "q1y")
let c2 = S.Const 2.0
let c3 = S.Const 3.0
let c6 = S.Const 6.0
let cq = S.Const 0.25

(* Evaluator mirroring Sym.lambda's eval, over a total env by var id. *)
let rec eval env = function
  | S.Add (a, b) -> eval env a +. eval env b
  | S.Mul (a, b) -> eval env a *. eval env b
  | S.Pow (n, x) -> eval env x ** n
  | S.Var (i, _) -> IntMap.find i env
  | S.Const x -> x

let env = IntMap.(add 0 1.2 (add 1 (-0.75) (add 2 3.125 empty)))

let failures = ref 0
let count label ok =
  if ok then Printf.printf "ok   %s\n%!" label
  else (incr failures; Printf.printf "FAIL %s\n%!" label)

let approx a b =
  let d = abs_float (a -. b) in
  let s = max (abs_float a) (abs_float b) in
  d <= 1e-9 *. max 1.0 s

(* ---- corpus of terms, built with the operators and with raw constructors ---- *)

let corpus =
  [ v0; cq; v0 + v1; v0 * v1; v0 * v0; v0 + v1 + v0; v0 + c2; c3 * v0
  ; S.neg v0
  ; v0 + S.neg v1
  ; v0 * S.neg v0
  ; S.Add (v0, S.Mul (S.Const (-1.0), v0))         (* a + (-a), raw *)
  ; S.Add (S.Add (v0, v1), v2)
  ; S.Add (v0, S.Add (v1, v2))
  ; S.Mul (S.Mul (v0, v1), v2)
  ; S.Mul (c2, S.Mul (c3, v0))
  ; S.Mul (S.Mul (c3, v0), c2)
  ; S.Mul (c2, S.Mul (c3, S.Mul (c6, v1)))
  ; S.pow 2.0 v0; S.pow 3.0 v0; S.pow 0.5 v0; S.recip v0
  ; S.pow 2.0 (S.pow 3.0 v0)
  ; S.Pow (2.0, S.Pow (3.0, v0))
  ; S.Pow (0.0, v0)
  ; S.Pow (0.0, S.Const 0.0)                        (* the 0^0 case *)
  ; S.Pow (2.0, S.Const 0.0)
  ; S.Pow (1.0, v0)
  ; S.Add (S.Pow (2.0, v0), S.Pow (2.0, v0))
  ; v0 + v1 + v0 + v1
  ; (v0 * v1) + S.neg (v0 * v1)
  ; S.deriv (v0 * v1) v0                            (* d(x*y)/dx = y, simplified *)
  ; S.deriv (S.Pow (2.0, v0)) v0                    (* d(x^2)/dx = 2x *)
  ; S.simplify (S.Pow (0.0, S.Const 0.0))
  ]

let () =
  (* 1. semantics preserved *)
  List.iteri (fun i t ->
    count (Printf.sprintf "semantics corpus[%d]" i)
      (approx (eval env (S.simplify t)) (eval env t))) corpus;

  (* 2. idempotence on the corpus *)
  List.iteri (fun i t ->
    count (Printf.sprintf "idempotent corpus[%d]" i)
      (S.simplify (S.simplify t) = S.simplify t)) corpus;

  (* 3. fixed / newly covered cases *)
  count "a + (-a) cancels"
    (S.simplify (S.Add (v0, S.Mul (S.Const (-1.0), v0))) = S.Const 0.0);
  count "(-a) + a cancels"
    (S.simplify (S.Add (S.Mul (S.Const (-1.0), v0), v0)) = S.Const 0.0);
  count "a + a = 2a" (S.simplify (v0 + v0) = S.Mul (S.Const 2.0, v0));
  count "a * a = a^2" (S.simplify (v0 * v0) = S.Pow (2.0, v0));
  count "deep const folding 2*(3*v) = 6v"
    (S.simplify (S.Mul (c2, S.Mul (c3, v0))) = S.Mul (S.Const 6.0, v0));
  count "pow of pow folds (a^3)^2 = a^6"
    (S.simplify (S.Pow (2.0, S.Pow (3.0, v0))) = S.Pow (6.0, v0));
  count "0^0 = 1 (fixed)"
    (S.simplify (S.Pow (0.0, S.Const 0.0)) = S.Const 1.0);
  count "0^0 matches float eval"
    (approx (eval env (S.simplify (S.Pow (0.0, S.Const 0.0)))) (0.0 ** 0.0));
  count "0^2 = 0" (S.simplify (S.Pow (2.0, S.Const 0.0)) = S.Const 0.0);
  count "x^1 = x" (S.simplify (S.Pow (1.0, v0)) = v0);
  count "deriv d(x*y)/dx = y" (S.deriv (v0 * v1) v0 = v1);
  count "deriv d(x*x)/dx = 2x" (S.deriv (v0 * v0) v0 = S.Mul (S.Const 2.0, v0));
  count "deriv d(x^2)/dx = 2x" (S.deriv (S.Pow (2.0, v0)) v0 = S.Mul (S.Const 2.0, v0));
  count "deriv d(x^3)/dx = 3x^2"
    (S.deriv (S.Pow (3.0, v0)) v0 = S.Mul (S.Const 3.0, S.Pow (2.0, v0)));
  count "deriv d(x+y)/dx = 1" (S.deriv (v0 + v1) v0 = S.Const 1.0);
  count "deriv d(c)/dx = 0" (S.deriv (S.Const 7.0) v1 = S.Const 0.0);
  count "deriv d(x)/dx = 1" (S.deriv v0 v0 = S.Const 1.0);
  count "deriv d(x)/dy = 0 (x <> y)" (S.deriv v0 v1 = S.Const 0.0);

  if !failures = 0 then print_endline "PASS"
  else (Printf.printf "%d FAILURES\n%!" !failures; exit 1)
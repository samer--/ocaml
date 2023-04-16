open Algebra
open Utils
open Symbolic


(* ---- lambda and evaluator --- *)

module IntMap = Map.Make(Int)

let add_var = function (Sym.Var (i,_)) -> IntMap.add i | _ -> assert false

type ('a,'b) tree = ('a,'b) Tree.t
type term = Sym.term
type ('a,'b) tree_lambda = (term,'a) tree -> (term,'b) tree -> (float,'a) tree -> (float,'b) tree

(* These lambdas could be parameterised over two functors
 * for the expression and the formal/given arguments
 *)
let lambda aa expr xx  =
  let open Sym in
  let env = Tree.foldl (|>) IntMap.empty (Tree.map2 add_var aa xx) in
  let rec eval = function
    | Add (a,b) -> eval a +. eval b
    | Mul (a,b) -> eval a *. eval b
    | Pow (n,x) -> eval x ** n
    | Var (i,_) -> IntMap.find i env
    | Const x   -> x
  in Tree.map eval expr

let lambda2 : ('a,'b) tree_lambda = fun aa expr ->
  (* uses partially applied maps and folds to 'compile' all
   * the pattern matching away once first two arguments are
   * given. Not clear if its any faster *)
  let open Sym in
  let rec eval : (Sym.t -> float IntMap.t -> float) = function
    | Add (a,b) -> let ea, eb = eval a, eval b in fun env -> ea env +. eb env
    | Mul (a,b) -> let ea, eb = eval a, eval b in fun env -> ea env *. eb env
    | Pow (n,x) -> let ex = eval x in fun env -> ex env ** n
    | Var (i,_) -> IntMap.find i
    | Const x   -> fun _ -> x in
  let map_over_evals = Tree.flip_map (Tree.map eval expr) in
  let env_builder = Tree.papp_fold2 add_var aa in
  fun xx -> map_over_evals (apply_to (env_builder xx IntMap.empty))

(* Gravitational potential *)

module Gravity (V: VECTOR) = struct
  (* Gravitational Hamiltonian. Works for any vector space,
   * including vectors over a symbolic field. Masses is a list
   * of scalars, while positions and momenta are lists of vectors.
   *)
  open VectorOps (V) (* incudes types v(ector) and s(calar) *)
  open ScalarOps (Scalar) (* field of vector space *)
  open List

  let two = one + one
	let g = pow (-8.0) two (* arbitrary constant *)
	let kinetic m p = (p <*> p)/(two*m)

	let grav_pot ((m1,r1), (m2,r2)) =
    (* pure gravitational interaction, point masses *)
		let dr = r2 <-> r1 in
    neg (g*m1*m2/sqrt(dr <*> dr))

	let soft_pot r0 ((m1,r1), (m2,r2)) =
    (* no singularity at zero - quadratic at close range *)
		let dr = r2 <-> r1 in
    neg (g*m1*m2/sqrt((dr <*> dr) + pow 2.0 (of_float r0)))

	let bouncy_pot r0 ((m1,r1), (m2,r2)) =
    (* repulsive at short range *)
		let dr = r2 <-> r1 in
    let dr2 =dr <*> dr in
    g*m1*m2*(of_float r0 - sqrt(dr2))/dr2

	let hamiltonian (potential: (s*v)*(s*v) -> s) (masses: s list) (positions: v list) (momenta: v list): s =
    let sum xs = fold_left ( + ) zero xs in
    sum (map potential (pairs (combine masses positions))) + sum (map2 kinetic masses momenta)
end

let system (softness: float) bodies =
  let module ListFloat2D = VList (Float2D) in
  let module Integrator = Integrators.HamiltonianRungeKutta (ListFloat2D) in
  let module GravSym2D = Gravity (Vec2D (Sym)) in

  let ms, xs, vs = unzip3 bodies in
  let symbolic_system n =
    let indices = iota n in
    let kth prefix k = prefix ^ "_" ^ string_of_int k in
    let ms = List.map Sym.const ms in
    let qs, ps =
      let new_vec prefix k =
        let f = Sym.var % (kth (kth prefix k)) in (f 1, f 2) in
      ( (List.map (new_vec "q") indices),
        (List.map (new_vec "p") indices)
      ) in

    let ham = GravSym2D.hamiltonian (GravSym2D.soft_pot softness) ms qs ps in
    let dHam = Sym.deriv ham in

    let qq, pp = Tree.of_pairs qs, Tree.of_pairs ps in
    let qd, pd = Tree.map dHam pp, Tree.map dHam qq in
    let coors = Tree.Two (qq, pp) in
    let h    = lambda coors (Tree.One ham) in
    let dhdq = lambda coors qd in
    let dhdp = lambda coors pd in
    h, dhdq, dhdp in

  let h, dhdq', dhdp'         = symbolic_system (List.length bodies) in
  let pairlist_of_tree        = Tree.(List.map pair_of_two % list_of_seq) in
  let tree_of_list_pair (q,p) = Tree.(Two (of_pairs q, of_pairs p)) in
  let dhdq = pairlist_of_tree % dhdq' % tree_of_list_pair in
  let dhdp = pairlist_of_tree % dhdp' % tree_of_list_pair in
  ( (xs, List.map2 Float2D.( *> ) ms vs) (* initial state *)
  , Tree.(un_one % h % tree_of_list_pair)      (* energy_of_state *)
  , (fun dt -> iterate 16 (Integrator.step dhdq dhdp (dt/.16.0)))
  )

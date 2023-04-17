open Algebra

module VecTypes (V: VECTOR) = struct
  type c = V.t * V.t
  type s = V.Scalar.t
end

module type HAMILTONIAN_INTEGRATOR = sig
  module V : VECTOR (* the type of position and momentum vectors *)
  open VecTypes (V)
  val step : (c -> V.t) -> (c -> V.t) -> s -> s*c -> s*c
end

module RungeKutta (V: VECTOR) = struct
  (** Runge-Kutta integrator, 4th order
   *  Works for any vector space.
   *)
  open V
  open ScalarOps (Scalar)

	let two = one + one
	let six = two + two + two

	let step f h (t, x) =
		let h2 = h/two in
    let t_ = t + h2 in
    let t2 = t + h in
		let k1 = f t x in
		let k2 = f t_ (x <+> h2*>k1) in
		let k3 = f t_ (x <+> h2*>k2) in
		let k4 = f t2  (x <+> h *>k3) in
		(t2, x <+> (h/six)*>(k1 <+> two*>k2 <+> two*>k3 <+> k4))
end

module HamiltonianRungeKutta (V: VECTOR with module Scalar = Float)
  : HAMILTONIAN_INTEGRATOR with module V = V = struct
  module V = V
  module RK = RungeKutta (VSum (V) (V))

  let step dHdp dHdq dt (t,x) =
    let f _ x = (dHdp x, V.negV (dHdq x)) in
    RK.step f dt (t,x)
end

(*
  Symplectic integrators

  https://scicomp.stackexchange.com/questions/20533/test-of-3rd-order-vs-4th-order-symplectic-integrator-with-strange-result
  http://www.unige.ch/~hairer/software.html
  https://reference.wolfram.com/language/tutorial/NDSolveSPRK.html
  https://github.com/yl3dy/nbody_playground/blob/master/nbody_sim/engines/naive.py
*)

module HamiltonianVerlet (V:VECTOR with module Scalar = Float)
  : HAMILTONIAN_INTEGRATOR with module V = V = struct
  module V = V
  open VectorOps (V)
  open ScalarOps (Scalar)

  let step dHdp dHdq dt (t,(q,p)) =
		let d2 = 0.5*dt in
    let p1 = p  <-> d2 *> dHdq (q,p) in
    let q2 = q  <+> dt *> dHdp (q,p1) in
    let p2 = p1 <-> d2 *> dHdq (q2,p1) in
    (t + dt, (q2,p2))
end
module type COEFFICIENTS = sig val coeffs: (float * float) list end


let divl (y:float): float list -> float list = List.map (Utils.divby y)

module Sym2 = struct let coeffs = [1.0,0.5; 0.0,0.5] end
module Sym3 = struct
  let coeffs = List.combine ([ 2.; -2.;  3.] |> divl 3.)
                            ([ 7.; 18.; -1.] |> divl 24.)
end

module Sym4 = struct
  let coeffs =
    let r = Stdlib.Float.(pow 2. (1./.3.)) in
    List.combine ([1.; 1. -. r; 1. -. r; 1.] |> divl (2. -. r) |> divl 2.)
                 ([0.; 1.     ;    -. r; 1.] |> divl (2. -. r))
end

module Symplectic (C:COEFFICIENTS) (V:VECTOR with module Scalar = Float)
  : HAMILTONIAN_INTEGRATOR with module V = V = struct
  module V = V
  open VectorOps (V)
  open ScalarOps (Scalar)

  let step dHdp dHdq dt (t,(q,p)) =
    let thingy (q,p) (c,d) =
      let p1 = p  <-> (d*dt) *> dHdq (q,p) in
      let q1 = q  <+> (c*dt) *> dHdp (q,p1) in
      (* somehow dual version *)
      (* let q1 = q  <+> (d*dt) *> dHdp (q,p) in *)
      (* let p1 = p  <+> (c*dt) *> dHdq (q1,p) in *)
      (q1,p1) in

  (t + dt, List.fold_left thingy (q,p) C.coeffs)
end

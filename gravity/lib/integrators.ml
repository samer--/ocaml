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
module Sym2 = struct let coeffs = [1.0,0.5; 0.0,0.5] end
module Sym3 = struct
  let coeffs =
    let two_thirds, one_24 = (2.0/.3.0, 1.0/.24.0) in
    [ two_thirds,   0.25 +. one_24
    ; -.two_thirds, 0.75
    ; 1.0,          -.one_24
    ]
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
      (q1,p1) in

  (t + dt, List.fold_left thingy (q,p) C.coeffs)
end

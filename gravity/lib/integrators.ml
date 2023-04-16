open Algebra

module type HAMILTONIAN_INTEGRATOR = sig
  module V : VECTOR (* the type of position and momentum vectors *)
  type c = V.t * V.t
  type s = V.Scalar.t

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
  type c = V.t * V.t
  type s = float

  let step dHdp dHdq dt (t,x) =
    let f _ x = (dHdp x, V.negV (dHdq x)) in
    RK.step f dt (t,x)
end

module Verlet (V:VECTOR) = struct
  open V
  open ScalarOps (Scalar)

	let two = one + one
  let velocity_verlet f h (t1, (x1, v1)) =
		let h2 = h/two in

    let a1 = f t1 x1 in
    let t2 = t1 + h in
    let x2 = x1 <+> h *> (v1 <+> h2 *> a1) in
    let a2 = f t2 x2 in
    let v2 = v1 <+> h2 *> (a1 <+> a2) in
    (t2, (x2, v2))

  let velocity_verlet' f h (t1, (x1, v1)) =
		let h2 = h/two in

    let a1 = f t1 x1 v1 in
    let t2 = t1 + h in
    let x2 = x1 <+> h *> (v1 <+> h2 *> a1) in
    let a2 = f t2 x2 (v1 <+> h *> a1) in
    let v2 = v1 <+> h2 *> (a1 <+> a2)
    in (t2, (x2, v2))
end


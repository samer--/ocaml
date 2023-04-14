(* TODO
 * integrators
 * render to cairo (not gdk), then blit to drawing area
 * simplify algebra
 * Add MLI
 * attitude and thrust
 *)

(* type system = body list *)
(* type body = position * velocity * mass * thrust * visual *)

open Utils
open Algebra
open Symbolic
open Gtktools

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

module RK (V: VECTOR) = struct
  (** Runge-Kutta integrator, 4th order
   *  Works for any vector space.
   *)
  open V
  open ScalarOps (Scalar)

	let two = one + one
	let six = two + two + two

	let step f h (t, x) =
		let h2 = V.Scalar.(h/two) in
    let t_ = t + h2 in
    let t2 = t + h in
		let k1 = f t x in
		let k2 = f t_ (x <+> h2*>k1) in
		let k3 = f t_ (x <+> h2*>k2) in
		let k4 = f t2  (x <+> h *>k3) in
		(t2, x <+> (h/six)*>(k1 <+> two*>k2 <+> two*>k3 <+> k4))
end

(* Gravitational potential *)

module Gravity (V: VECTOR) = struct
  (* Gravitational Hamiltonian. Works for any vector space,
   * including vectors over a symbolic field. Masses is a list
   * of scalars, while positions and momenta are lists of vectors.
   *)
  open VectorOps (V)
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

	let hamiltonian potential masses positions momenta =
    let sum xs = List.fold_left ( + ) zero xs in
    sum (map potential (pairs (combine masses positions))) + sum (map2 kinetic masses momenta)
end

module Float2D     = Vector (Pair) (Float)
module GravSym2D   = Gravity (Vector (Pair) (Sym))


let system potential bodies =
  (* symbolic system description *)
  let symbolic_system n =
    let indices = iota n in
    let kth prefix k = prefix ^ "_" ^ string_of_int k in
    let ms = List.map (Sym.var -| kth "m") indices in
    let xs, ps =
      let new_vec prefix k =
        let f = Sym.var -| (kth (kth prefix k)) in (f 1, f 2) in
      ( (List.map (new_vec "x") indices),
        (List.map (new_vec "p") indices)
      ) in

    let ham = GravSym2D.hamiltonian potential ms xs ps in
    let dHam = Sym.deriv ham in

    let open Tree in
    let mm = from_scalars ms in
    let xx, pp = from2d xs, from2d ps in
    let xd, pd = map dHam pp, map (Sym.neg -| dHam) xx in
    let h = lambda (mm <> (xx <> pp)) (One ham) in
    let f = lambda (mm <> (xx <> pp)) (xd <> pd) in
    f, h, (xs, ps, xd, pd) in

  let f, h, _ = symbolic_system (List.length bodies) in
  let ms, xs, vs = unzip3 bodies in
  let ps = List.map2 Float2D.( *> ) ms vs in
  let open Tree in
  let mvals = from_scalars ms in
  ((fun state -> h (mvals <> state)),
   (fun _ state -> f (mvals <> state)),
   from2d xs <> from2d ps)

module RKAggVec = RK (Vector (Tree) (Float))


module RenderCairo = struct
  let two_pi = 8. *. atan 1.0
  let report name x = Printf.printf "\n%s = %f\n%!" name x; x

  exception IgnoredKey

  type 's state = { kt: float
                  ; dt: float
                  ; rt: float
                  ; kx: float
                  ; ds: float * 's
                  ; t_last: float
                  ; stop: bool
                  ; focus: int option
                  }

  type shape = Point of (float * float)
             | Disc of int * (float * float)

  let render (_t0,s0) =
    let open Tree in
    let render1 (Seq [One x; One y]) = Point (x,y) in
    let Two (Seq pos, _) = s0 in
    List.map render1 pos

  let fill_circle cr ((x,y), r) =
    Cairo.arc cr x y ~r ~a1:0. ~a2:two_pi;
    Cairo.Path.close cr;
    Cairo.fill cr


  let display cx cy kx (ox,oy) cr colours shapes =
    let pixel cr = uncurry max (Cairo.device_to_user_distance cr 4.0 4.0) in
    let display1 a_pixel (colour, shape) =
      let (r,g,b) = colour in begin
        Cairo.set_source_rgb cr r g b;
        fill_circle cr (match shape with
          | Point pt    -> (pt, a_pixel);
          | Disc (r,pt) -> (pt, float r))
        end in

    Cairo.save cr;
    Cairo.translate cr cx cy;
    Cairo.scale cr kx (~-.kx);
    Cairo.translate cr (~-.ox) (~-.oy);
    List.iter (display1 (pixel cr)) (List.combine colours shapes);
    Cairo.restore cr

  let position_of_nth s i =
    let open Tree in
    let (Two (Seq pos, _)) = s in
    let (Seq [One x; One y]) = List.nth pos i in
    (x, y)

  let state_machine (h,f,s0) colours dt t_start =
    let advance dt = iterate 16 (RKAggVec.step f (dt/.16.0)) in

    let draw (width,height) cr state =
      let t0,s0 = state.ds in
      let origin = match state.focus with
        | None -> (0.0,0.0)
        | Some i -> position_of_nth s0 i in
      state.ds |> render |> display (width/.2.) (height/.2.) state.kx origin cr colours;

      let Tree.One energy = h s0 in
      let t_now = get_time () in
      let fps = 1. /. (t_now -. state.t_last) in
      let text = Printf.sprintf "t=%6.2f, H=%8.5g, fps=%3.0f  \r" t0 energy fps in
      Cairo.set_source_rgb cr 0.9 0.5 0.05;
      Cairo.move_to cr 8. (height -. 8.);
      Cairo.set_font_size cr 28.;
      Cairo.show_text cr text;
      { state with rt=state.rt +. dt;
                   ds=advance (state.kt *. dt) state.ds;
                   t_last=t_now} in

    let handle s = function
      | 'q' -> {s with stop=true}
      | '<' -> {s with dt=(report "dt" (s.dt/.2.))}
      | '>' -> {s with dt=(report "dt" (s.dt*.2.))}
      | '[' -> {s with kt=(report "kt" (s.kt/.2.))}
      | ']' -> {s with kt=(report "kt" (s.kt*.2.))}
      | 'r' -> {s with kt=(report "kt" (~-.(s.kt)))}
      | '-' -> {s with kx=(report "kx" (s.kx/.2.))}
      | '=' -> {s with kx=(report "kx" (s.kx*.2.))}
      | 'i' -> {s with ds=(0.0,s0)}
      | '0' -> {s with focus=None}
      | '1' -> {s with focus=Some 0}
      | '2' -> {s with focus=Some 1}
      | '3' -> {s with focus=Some 2}
      | '4' -> {s with focus=Some 3}
      | _   -> raise IgnoredKey
    in

    let key_press s ev =
      let code, str = GdkEvent.Key.(keyval ev, string ev) in
      Printf.printf "keypress %d (%s)\n%!" code str;
      try handle s (Char.chr code), true
      with IgnoredKey -> s, false

    in ( {kt=1.0; dt=dt; rt=t_start; kx=80.0; ds=(0.0, s0); t_last=t_start; stop=false; focus=None},
         ignore, [ `KEY_PRESS; `KEY_RELEASE ],
         draw, [ link (fun cs -> cs#key_press)    key_press ])
    (* end of state_machine *)
  let stop sref = (!sref).stop
  let run dt colours def = get_time ()  +. 0.5 |> state_machine def colours dt |> animate_with_loop stop dt
end

(* numeric description *)
let zeroV = (0.0,0.0)
let unit1 = (1.0,0.0)
let unit2 = (0.0,1.0)

let red    = (1.0, 0.5, 0.5)
let yellow = (1.0, 1.0, 0.5)
let green  = (0.5, 1.0, 0.5)
let blue   = (0.5, 0.5, 1.0)
let white  = (1.0, 1.0, 1.0)

let sun_two_planets =
  Float2D.[ yellow, (500. , zeroV         , zeroV)
          ; blue,   (10.  , unit1       , 1.0 *> unit2)
          ; red,    (0.1  , negV (unit1), (-1.0)*> unit2)
          ]

let sun_contra_planets =
  Float2D.[ yellow, (500.0, zeroV          , zeroV)
          ; blue,   (2.0  , 1.00 *> unit1, 1.10 *> unit2)
          ; red,    (1.0  , (-1.) *> unit1, 1.00 *> unit2)
          ; green,  (1.0  , (-1.5) *> unit1, (1.)*> unit2)
          ]

let sun_planet_moons =
  Float2D.[ yellow, (500.0, zeroV          , (-0.02) *> unit2)
          ; blue,   (8.0  , 2.00 *> unit1, 1.00 *> unit2)
          ; red,    (0.1  , 2.10 *> unit1, 1.60 *> unit2)
          ; white,  (0.5  , 2.20 *> unit1, 1.40 *> unit2)
          ]

let binary_suns =
  Float2D.[ yellow, (300. ,   0.08  *> unit1, (-2.0) *> unit2)
          ; blue,   (300. , (-0.08) *> unit1, (2.0)   *> unit2)
          ; green,  (10.  , unit1       , 1.5 *> unit2)
          ; red,    (0.1  , negV (unit1), (-1.5)*> unit2)
          ]

let systems = [sun_two_planets; sun_contra_planets; sun_planet_moons; binary_suns]

let offline_run num_iter (h,f,s0) dt =
  let advance s =
    let Tree.One energy = h (snd s) in
    iterate 16 (RKAggVec.step f (dt/.16.0)) s in
  ignore (iterate num_iter advance (0.0, s0))

let main args =
  let colours, bodies = unzip (List.nth systems (int_of_string args.(1))) in
  let sys = system (GravSym2D.soft_pot (float_of_string args.(3))) bodies in
  if Array.length args > 4 then
    let open Core_bench in
    let run () = offline_run (int_of_string args.(4)) sys (float_of_string args.(2)) in
    Bench.bench [Bench.Test.create ~name: ("system " ^ args.(1)) run]
  else
    RenderCairo.run (float_of_string args.(2)) colours sys

let _ = if not !Sys.interactive then main Sys.argv else ()

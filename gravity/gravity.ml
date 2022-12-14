(* type system = body list *)
(* type body = position * velocity * mass * thrust * visual *)

open Utils
open Algebra
open Symbolic
open Gtktools

module Verlet (V:VECTOR) = struct
  module VO = VectorOps(V)
  open VO
  open F

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
  module VO = VectorOps(V)
  open VO
  open F

	let two = one + one
	let six = two+two+two

	let rk4 f h (t, x) =
		let h2 = h/two in
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
	module VO = VectorOps(V)
  open VO
  open F
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
    sum (map potential (pairs (combine masses positions))) + sum (map2 kinetic masses momenta)
end

module List2       = ListN (struct let n=2 end)
module Float2D     = FunctorVector (List2) (Float)
module Sym2D       = FunctorVector (List2) (Sym)
module GravSym2D   = Gravity (Sym2D)

let system_variables num_dimensions n =
  let new_vec prefix k = List.map (fun i -> Sym.var (prefix ^ string_of_int k ^ string_of_int i)) 
                                  (iota num_dimensions) in
  let new_mass k = Sym.var ("m" ^ string_of_int k) in
  ( (iota n |> List.map (new_mass)), 
    (iota n |> List.map (new_vec "x")),
    (iota n |> List.map (new_vec "p"))
  )


(* symbolic system description *)
let symbolic_system pot n =
  let ms, xs, ps = system_variables 2 n in
  let ham = GravSym2D.(hamiltonian pot ms xs ps) in
  let dHam = Sym.deriv ham in

  let open Agg in 
  let mm = from1d ms in
  let xx, pp = from2d xs, from2d ps in
  let xd, pd = map dHam pp, map (Sym.neg -| dHam) xx in
  let h = lambda2 (mm <> (xx <> pp)) (One ham) in
  let f = lambda2 (mm <> (xx <> pp)) (xd <> pd) in
	f, h, (xs, ps, xd, pd)


let system grav_pot bodies =
  let f, h, (xs, ps, xd, pd) = symbolic_system grav_pot (List.length bodies) in
  let ms, xs, vs = unzip3 bodies in
  let ps = List.map2 Float2D.( *> ) ms vs in
  let open Agg in 
  let mvals = from1d ms in
  ((fun state -> h (mvals <> state)),
   (fun _ state -> f (mvals <> state)), 
   from2d xs <> from2d ps)

module RKAggVec = RK (FunctorVector (Agg) (Float))

type shape = Point of (float * float)
           | Disc of int * (float * float)

let render (t0,s0) =
  let open Agg in
  let render1 (Seq [One x; One y]) = Point (x,y) in
  let Two (Seq pos, _) = s0 in
  List.map render1 pos

let report name x = Printf.printf "\n%s = %f\n" name x; x

module RenderGraphics = struct

  let with_display w h =
    setup_call_cleanup
      (fun () -> Graphics.open_graph (Printf.sprintf " %dx%d" w h))
      (fun _ -> Graphics.close_graph ())

  let displayer scale ox oy =
    let open Graphics in
    let int_of_coor x = int_of_float (scale *. x) in
    let xform x y = ox + int_of_coor x, oy + int_of_coor y in
    let display1 = function
      | Point (x,y) -> let i, j = xform x y in plot i j;
      | Disc  (r,(x,y)) -> let i, j = xform x y in fill_circle i j r;
    in fun shapes -> 
      clear_graph (); 
      List.iter display1 shapes;
      synchronize ()

  let dloop dt (h,f,s0) =
    let advance = RKAggVec.rk4 f in
    let display = displayer 80.0 250 250 in
    let t_start = get_time () +. 0.5 in

    let rec loop kt dt rt (t0,s0) = 
      let open Graphics in 
      let Agg.One energy = h s0 in
      sleep_until rt; 
      (t0,s0) |> render |> display;
      Printf.printf "t=%6.3f, E=%8.7g  \r" t0 energy; flush stdout;
      if key_pressed () then
        handle kt dt rt (t0,s0) (read_key ())
      else
        loop_adv kt dt rt (t0,s0)

    and loop_adv kt dt rt state = loop kt dt (rt +. kt *. dt) (advance dt state)
    and handle kt dt rt state = function
      | 'q' -> ()
      | '<' -> loop_adv kt (report "dt" (dt/.2.)) rt state
      | '>' -> loop_adv kt (report "dt" (dt*.2.)) rt state
      | '[' -> loop_adv (report "kt" (kt/.2.)) dt rt state
      | ']' -> loop_adv (report "kt" (kt*.2.)) dt rt state
      | 'r' -> loop kt dt rt (0.0,s0)
      | _ -> loop_adv kt dt rt state

    in with_display 500 500
      (fun _ -> Graphics.auto_synchronize false; 
                loop 1.0 dt t_start (0.0,s0))
end

module RenderCairo = struct
  let two_pi = 8. *. atan 1.0
  type 's state = { kt: float
                  ; dt: float
                  ; rt: float
                  ; kx: float
                  ; ds: float * 's
                  ; t_last: float 
                  ; stop: bool
                  ; focus: int option
                  } 

  let fill_circle cr (x,y) r =
    Cairo.arc cr x y r 0. two_pi;
    Cairo.Path.close cr;
    Cairo.fill cr

  let pixel cr = 
    let ux, uy = Cairo.device_to_user_distance cr 2. 2. in 
    max ux uy

  let display1 cr = function
    | Point pt   -> fill_circle cr pt (pixel cr);
    | Disc  (r,pt) -> fill_circle cr pt (float r)

  let display cx cy kx (ox,oy) cr shapes =
    Cairo.save cr;
    Cairo.translate cr cx cy;
    Cairo.scale cr kx (~-.kx);
    Cairo.translate cr (~-.ox) (~-.oy);
    Cairo.set_source_rgb cr 1.0 1.0 1.0;
    List.iter (display1 cr) shapes;
    Cairo.restore cr

  let position_of_nth s i = 
    let open Agg in
    let (Two (Seq pos, _)) = s in 
    let (Seq [One x; One y]) = List.nth pos i in
    (x, y) 

  let system (h,f,s0) dt t_start = 
    let advance dt = iterate 10 (RKAggVec.rk4 f (dt/.10.)) in

    let draw width height cr state = 
      let t0,s0 = state.ds in 
      let origin = match state.focus with
        | None -> (0.0,0.0)
        | Some i -> position_of_nth s0 i in
      state.ds |> render |> display (width/.2.) (height/.2.) state.kx origin cr;
      let Agg.One energy = h s0 in
      let t_now = get_time () in 
      let fps = 1. /. (t_now -. state.t_last) in
      let text = Printf.sprintf "t=%6.2f, H=%8.5g, fps=%5.1f  \r" t0 energy fps in
      Cairo.set_source_rgb cr 0.9 0.5 0.5;
      Cairo.move_to cr 8. (height -. 8.);
      Cairo.set_font_size cr 14.;
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
    in

    let key_press s ev = 
      let code, str = GdkEvent.Key.(keyval ev, string ev) in 
      Printf.printf "keypress %d (%s)\n%!" code str; 
      try handle s (Char.chr code), true
      with e -> s, false

    in ( {kt=1.0; dt=dt; rt=t_start; kx=80.0; ds=(0.0, s0); t_last=t_start; stop=false; focus=None},
         ignore, [ `KEY_PRESS; `KEY_RELEASE ], 
         draw, [ link (fun cs -> cs#key_press)    key_press ])
  let stop sref = (!sref).stop 
  let run dt def = () |> get_time |> ( +. ) 0.5 |> system def dt |> animate_with_loop stop dt
end

(* numeric description *)
let zeroV = rep 2 0.0 
let unitV i = rep (i-1) 0.0 @ [1.0] @ rep (2-i) 0.0

let sun_two_planets = Float2D.[ 500., zeroV         , zeroV
                              ; 10.  , unitV 1       , 1.0 *> unitV 2
                              ; 0.1  , negV (unitV 1), (-1.0)*> unitV 2
                              ]

let sun_contra_planets = Float2D.[ 500.0, zeroV          , zeroV
                                 ; 2.0  , 1.00 *> unitV 1, 1.10 *> unitV 2
                                 ; 1.0  , (-1.) *> unitV 1, 1.00 *> unitV 2
                                 ; 1.0  , (-1.5) *> unitV 1, (1.)*> unitV 2
                                 ]

let sun_planet_moons = Float2D.[ 500.0, zeroV          , (-0.02) *> unitV 2
                               ; 8.0  , 2.00 *> unitV 1, 1.00 *> unitV 2
                               ; 0.1  , 2.10 *> unitV 1, 1.60 *> unitV 2
                               ; 0.5  , 2.20 *> unitV 1, 1.40 *> unitV 2
                               ]

let binary_suns = Float2D.[ 300. ,   0.08  *> unitV 1, (-2.0) *> unitV 2
                          ; 300. , (-0.08) *> unitV 1, (2.0)   *> unitV 2
                          ; 10.  , unitV 1       , 1.5 *> unitV 2
                          ; 0.1  , negV (unitV 1), (-1.5)*> unitV 2
                          ]

let systems = [sun_two_planets; sun_contra_planets; sun_planet_moons; binary_suns]

let main args = 
  RenderCairo.run (float_of_string args.(2)) 
                  (system (GravSym2D.soft_pot (float_of_string args.(3))) 
                          ( List.nth systems (int_of_string args.(1))))

let _ = if not !Sys.interactive then main Sys.argv else ()

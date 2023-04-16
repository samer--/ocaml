(* TODO
 * integrators
 * render to cairo (not gdk), then blit to drawing area
 * simplify algebra
 * Add MLI
 * attitude and thrust
 *)

(* type system = body list *)
(* type body = position * velocity * mass * thrust * visual *)

open Gravlib
open Algebra


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
  Float2D.[ yellow, (500.0, zeroV          , (-0.1 *> unit2))
          ; blue,   (20.0  , 1.00 *> unit1, 1.10 *> unit2)
          ; red,    (10.0  , (-1.) *> unit1, 1.00 *> unit2)
          ; green,  (10.0  , (-1.5) *> unit1, (1.)*> unit2)
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


let main args =
  let open Utils in

  let colours, bodies = unzip (List.nth systems (int_of_string args.(1))) in
  let sys = Gravity.system (float_of_string args.(3)) bodies in

  if Array.length args > 4 then
    let open Core_bench in
    let energy_of_state, advance, s0 = sys in
    let offline_run num_iter dt =
      let advance' s =
        ignore (energy_of_state (snd s));
        advance dt s in
      ignore (iterate num_iter advance' (0.0, s0)) in

    let run () = offline_run (int_of_string args.(4)) (float_of_string args.(2)) in
    Bench.bench [Bench.Test.create ~name: ("system " ^ args.(1)) run]
  else
    let open Gtktools in
    with_system setup_pixmap_backing animate_with_loop
                (Nbodysim.gtk_system (float_of_string args.(2)) colours sys)

let _ = if not !Sys.interactive then main Sys.argv else ()

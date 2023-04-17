(* TODO
 * render to cairo (not gdk), then blit to drawing area
 * Add MLI files
 * attitude and thrust
 * load system spec from file
 * nice command line arguments
 *)

(* type system = body list *)
(* type body = position * velocity * mass * thrust * visual *)

open Gravlib
open Algebra.Float2D
open Integrators

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
  [ yellow, (500. , zeroV         , zeroV)
  ; blue,   (10.  , unit1       , 1.0 *> unit2)
  ; red,    (0.1  , negV (unit1), (-1.0)*> unit2)
  ]

let sun_contra_planets =
  [ yellow, (500.0, zeroV          , (-0.1 *> unit2))
  ; blue,   (20.0  , 1.00 *> unit1, 1.10 *> unit2)
  ; red,    (10.0  , (-1.) *> unit1, 1.00 *> unit2)
  ; green,  (10.0  , (-1.5) *> unit1, (1.)*> unit2)
  ]

let sun_planet_moons =
  [ yellow, (500.0, zeroV          , (-0.02) *> unit2)
  ; blue,   (8.0  , 2.00 *> unit1, 1.00 *> unit2)
  ; red,    (0.1  , 2.10 *> unit1, 1.60 *> unit2)
  ; white,  (0.5  , 2.20 *> unit1, 1.40 *> unit2)
  ]

let binary_suns =
  [ yellow, (300. ,   0.08  *> unit1, (-2.0) *> unit2)
  ; blue,   (300. , (-0.08) *> unit1, (2.0)   *> unit2)
  ; green,  (10.  , unit1       , 1.5 *> unit2)
  ; red,    (0.1  , negV (unit1), (-1.5)*> unit2)
  ]

let three_body =
  (* https://joemcewen.github.io/_pages/codes/3body/ *)
  let a, b, v = (0.97000436, 0.24308753, (-.0.46620368, -.0.4323657)) in
  [ yellow, (256., (-.a,  b), v)
  ; green,  (256., (  a,-.b), v)
  ; red,    (256., zeroV, (0.93240737, 0.8647314))
  ]

let systems = [sun_two_planets; sun_contra_planets; sun_planet_moons; binary_suns; three_body]

let integrators : (module INTEGRATOR) list =
  [ (module HamiltonianRungeKutta)
  ; (module HamiltonianVerlet)
  ; (module Symplectic (Sym2))
  ; (module Symplectic (Sym3))
  ; (module Symplectic (Sym4))
  ]

let main args =
  let open Utils in
  let module GravSim = Gravity.Sim2D (val (List.nth integrators (int_of_string args.(1)))) in
  let colours, bodies = unzip (List.nth systems (int_of_string args.(2))) in
  let sys = GravSim.system (float_of_string args.(4)) bodies in

  if Array.length args > 5 then
    let open Core_bench in
    let energy_of_state, advance, s0 = sys in
    let offline_run num_iter dt =
      let advance' s =
        ignore (energy_of_state (snd s));
        advance dt s in
      ignore (iterate num_iter advance' (0.0, s0)) in

    let run () = offline_run (int_of_string args.(5)) (float_of_string args.(3)) in
    Bench.bench [Bench.Test.create ~name: ("system " ^ args.(2)) run]
  else
    let open Gtktools in
    with_system setup_pixmap_backing animate_with_loop
                (Nbodysim.gtk_system (float_of_string args.(3)) colours sys)

let _ = if not !Sys.interactive then main Sys.argv else ()

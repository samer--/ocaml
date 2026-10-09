(* Gravitational motion simulator
   Run with --help for usage information.

   TODO
   - attitude and thrust
   - load system spec from file
 *)

open Gravlib
open Algebra.Float2D
open Integrators

(* Colours are (r, g, b) triples in 0..1. *)

let red    = (1.0, 0.5, 0.5)
let yellow = (1.0, 1.0, 0.5)
let green  = (0.5, 1.0, 0.5)
let blue   = (0.5, 0.5, 1.0)
let white  = (1.0, 1.0, 1.0)

(* ---- Predefined systems ----
   Each system is a list of (colour, (mass, position, velocity)) tuples.
   Positions and velocities are 2D vectors. *)

let zeroV = (0.0, 0.0)
let unit1 = (1.0, 0.0)
let unit2 = (0.0, 1.0)

let sun_two_planets =
  [ yellow, (500., zeroV          , zeroV)
  ; blue,   (10. , unit1          ,  1.0 *> unit2)
  ; red,    (0.1 , negV (unit1)   , -1.0 *> unit2)
  ]

let sun_contra_planets =
  [ yellow, (500.0, zeroV         , -0.15 *> unit2)
  ; blue,   (50.0 ,  1.00 *> unit1,  1.10 *> unit2)
  ; red,    (20.0 , -1.00 *> unit1,  1.00 *> unit2)
  ; green,  (20.0 , -1.50 *> unit1,  1.00 *> unit2)
  ]

let sun_planet_moons =
  [ yellow, (500.0, zeroV           , -0.02 *> unit2)
  ; blue,   (  8.0,  2.00 *> unit1  ,  1.00 *> unit2)
  ; red,    (  0.1,  2.10 *> unit1  ,  1.60 *> unit2)
  ; white,  (  0.5,  2.20 *> unit1  ,  1.40 *> unit2)
  ]

let binary_suns =
  [ yellow, (300.,   0.08  *> unit1, -2.0 *> unit2)
  ; blue,   (300., (-0.08) *> unit1,  2.0 *> unit2)
  ; green,  ( 10.,  unit1          ,  1.5 *> unit2)
  ; red,    (  0.1, negV (unit1)   , -1.5 *> unit2)
  ]

let three_body =
  (* Stable figure-8 three-body orbit
     https://joemcewen.github.io/_pages/codes/3body/
     https://arxiv.org/abs/math/0011268 *)
  let a, b, v = (0.97000436, 0.24308753, (0.46620368, 0.4323657)) in
  [ yellow, (256., (-.a,   b), negV v)
  ; green,  (256., (  a, -.b), negV v)
  ; red,    (256., zeroV     , 2. *> v)
  ]

let systems = [sun_two_planets; sun_contra_planets; sun_planet_moons; binary_suns; three_body]

(* ---- Integrators ---- *)

let integrators : (module INTEGRATOR) list =
  [ (module HamiltonianRungeKutta)
  ; (module HamiltonianVerlet)
  ; (module Symplectic (Sym2))
  ; (module Symplectic (Sym3))
  ; (module Symplectic (Sym4))
  ]

(* ---- CLI argument definitions ---- *)

open Cmdliner

let system_choices =
  [ "sun-two-planets",   0, "1 star, 2 planets"
  ; "sun-contra-planets", 1, "1 star, 3 planets (one retrograde)"
  ; "sun-planet-moons",   2, "1 star, 1 planet, 1 moon, 1 spacecraft"
  ; "binary-suns",        3, "2 stars in tight orbit, 2 planets"
  ; "three-body",         4, "Stable figure-8 three-body orbit"
  ]

let integrator_choices =
  [ "rk4",    0, "Runge-Kutta 4th order (not symplectic)"
  ; "verlet", 1, "Hamiltonian Verlet (symplectic, 2nd order)"
  ; "sym2",   2, "Symplectic 2nd order (Yoshida)"
  ; "sym3",   3, "Symplectic 3rd order (Yoshida)"
  ; "sym4",   4, "Symplectic 4th order (Yoshida)"
  ]

let system =
  let doc = "Predefined system to simulate." in
  let docv = "SYSTEM" in
  let choices = Arg.enum (List.map (fun (n,i,_) -> (n,i)) system_choices) in
  Arg.(value & opt choices 2 & info ["system"; "s"] ~doc ~docv)

let integrator =
  let doc = "Numerical integration method." in
  let docv = "INTEGRATOR" in
  let choices = Arg.enum (List.map (fun (n,i,_) -> (n,i)) integrator_choices) in
  Arg.(value & opt choices 4 & info ["integrator"; "i"] ~doc ~docv)

let fps =
  let doc = "Initial frames per second." in
  Arg.(value & opt float 60.0 & info ["fps"] ~doc ~docv:"FPS")

let softness =
  let doc = "If positive, then softening parameter to avoid singularity at zero \
             distance (the gravitational potential smoothly transitions to a \
             quadratic well at this scale). If negative, then attraction turns \
             to repulsion at this scale." in
  Arg.(value & opt float 0.001 & info ["softness"] ~doc ~docv:"EPSILON")

let bench =
  let doc = "Run in offline benchmark mode with the given number of \
             iterations (no GUI window)." in
  Arg.(value & opt (some int) None & info ["bench"; "b"]
         ~doc ~docv:"ITERATIONS")

(* ---- Main ---- *)

let run system_idx integrator_idx fps0 softness bench_iters =
  let open Utils in
  let module GravSim = Gravity.Sim2D (val (List.nth integrators integrator_idx)) in
  let colours, bodies = unzip (List.nth systems system_idx) in
  let sys = GravSim.system softness bodies in

  match bench_iters with
  | Some num_iter ->
    let open Core_bench in
    let energy_of_state, advance, s0 = sys in
    let offline_run num_iter dt =
      let advance' s =
        ignore (energy_of_state (snd s));
        iterate 16 (advance (dt /. 16.)) s
      in
      ignore (iterate num_iter advance' (0.0, s0))
    in
    let name = Printf.sprintf "system %d" system_idx in
    let run () = offline_run num_iter (1.0 /. fps0) in
    Bench.bench [Bench.Test.create ~name run]
  | None ->
    let open Gtktools in
    with_system setup_pixmap_backing animate_with_loop
                (Nbodysim.gtk_system (1.0 /. fps0) colours sys)

let cmd =
  let doc = "Gravitational motion simulator with symbolic equation derivation." in
  let sdocs = Manpage.s_common_options in
  let exits = Cmd.Exit.defaults in
  let man = [
    `S Manpage.s_description;
    `P "Simulates the motion of massive objects under mutual \
        gravitational attraction. The equations of motion are derived \
        symbolically from the Hamiltonian at startup, then evaluated \
        numerically each frame.";
    `S "SYSTEMS";
    `P "$(b,sun-two-planets)       — 1 star, 2 planets";
    `P "$(b,sun-contra-planets)   — 1 star, 3 planets (one retrograde)";
    `P "$(b,sun-planet-moons)     — 1 star, 1 planet, 1 moon, 1 spacecraft";
    `P "$(b,binary-suns)          — 2 stars in tight orbit, 2 planets";
    `P "$(b,three-body)           — Stable figure-8 three-body orbit";
    `S "INTEGRATORS";
    `P "$(b,rk4)    — Runge-Kutta 4th order (not symplectic)";
    `P "$(b,verlet) — Hamiltonian Verlet (symplectic, 2nd order)";
    `P "$(b,sym2)   — Symplectic 2nd order (Yoshida)";
    `P "$(b,sym3)   — Symplectic 3rd order (Yoshida)";
    `P "$(b,sym4)   — Symplectic 4th order (Yoshida)";
    `S "KEYBOARD CONTROLS";
    `S "  q     quit";
    `S "  <     decrease frame rate and increase steps per frame (less frequent redraws)";
    `S "  >     increase frame rate and decrease steps per frame (more frequent redraws)";
    `S "  [     increase time per step and reduce steps per frame (coarser integration)";
    `S "  ]     decrease time per step and increase steps per frame (finer integration)";
    `S "  _     speed up simulated time approx preserving integration time step";
    `S "  +     slow down simulated time approx preserving integration time step";
    `S "  r     reverse time";
    `S "  -     zoom out";
    `S "  =     zoom in";
    `S "  i     return to initial positions and velocities";
    `S "  0     centre view on origin";
    `S "  1-4   centre view on body 1-4";
    `S Manpage.s_examples;
    `P "$(b,gravity --system sun-planet-moons --integrator verlet)";
    `P "$(b,gravity -s three-body -i sym4 --fps 50 --softness 0.002)";
    `P "$(b,gravity -s binary-suns --bench 1000)";
    `S Manpage.s_bugs;
    `P "Report bugs at https://github.com/samer--/ocaml/issues";
  ] in
  let info = Cmd.info "gravity" ~version:"1.1" ~doc ~sdocs ~exits ~man in
  Cmd.v info Term.(const run $ system $ integrator $ fps $ softness $ bench)

let () = if not !Sys.interactive then exit (Cmd.eval cmd) else ()

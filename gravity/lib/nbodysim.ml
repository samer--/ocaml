open Utils

let two_pi = 8. *. atan 1.0
let report name x = Printf.printf "\n%s = %f\n%!" name x; x

exception IgnoredKey

type 's state = { kt: float
                ; dt: float
                ; rt: float
                ; kx: float
                ; ds: float * 's
                ; t_last: float
                ; spf: float
                ; stop: bool
                ; focus: int option
                }

type shape = Point of (float * float)
           | Disc of int * (float * float)

let render (_t0,(pos, _)) =
  let render1 (x,y) = Point (x,y) in
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

let position_of_nth (pos,_) i = List.nth pos i

let state_machine (energy_of_state, advance, s0) colours dt t_start =

  let draw (width,height) cr state =
    let t0,s0 = state.ds in
    let origin = match state.focus with
      | None -> (0.0,0.0)
      | Some i -> position_of_nth s0 i in
    state.ds |> render |> display (width/.2.) (height/.2.) state.kx origin cr colours;

    let energy = energy_of_state s0 in
    let t_now = get_time () in
    let spf = 0.98 *. state.spf +. 0.02 *. (t_now -. state.t_last) in
    let fps = 1. /. spf in
    let text = Printf.sprintf "t=%6.2f, H=%8.5g, fps=%4.0f  \r" t0 energy fps in
    Cairo.set_source_rgb cr 0.9 0.5 0.05;
    Cairo.move_to cr 8. (height -. 8.);
    Cairo.set_font_size cr 28.;
    Cairo.show_text cr text;
    { state with rt=state.rt +. dt;
                 ds=advance (state.kt *. dt) state.ds;
                 t_last=t_now; spf=spf} in


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
    with IgnoredKey -> s, false in

  let stop state = state.stop in
  ( {kt=1.0; dt=dt; rt=t_start; kx=80.0; ds=(0.0, s0); spf=dt; t_last=t_start; stop=false; focus=None},
     dt, stop, draw, [ `KEY_PRESS; `KEY_RELEASE ], [ Gtktools.link (fun cs -> cs#key_press) key_press ])
  (* end of state_machine *)

let stop sref = (!sref).stop
let gtk_system dt colours def = state_machine def colours dt (get_time ()  +. 0.5)

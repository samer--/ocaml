open Utils

type 'e selector = GObj.event_signals -> callback:('e -> bool) -> GtkSignal.id
type 's link = | Link : 'e selector * ('s -> 'e -> 's * bool) -> 's link

let link sel h = Link (sel, h)

type 's painter = (float * float) -> Cairo.context -> 's -> 's
type 's system = 's              (* initial state *)
               * ('s -> float)   (* get target frame period in seconds *)
               * ('s -> bool)    (* state implies we should stop? *)
               * 's painter      (* action to paint Cairo context and update state *)
               * Gdk.Tags.event_mask list (* which events to respond to *)
               * 's link list    (* events to connect *)

type 's ui = {quit       : (unit -> unit)
             ;prepaint   : (unit -> unit)
             ;paint      : (unit -> unit)
             ;should_stop: (unit -> bool)
             ;frame_period: (unit -> float)
             }

let with_system setup (action: 's ui -> unit) (system: 's system) =
  let _ = GtkMain.Main.init () in
  let w = GWindow.window ~title:"Gravity" ~width:800 ~height:600
                         ~resizable:true ~focus_on_map:true () in
  let area = GMisc.drawing_area ~packing:w#add () in
  let quit _ = print_endline "Quitting"; GtkMain.Main.quit () in
  let initial_state, frame_period, stop, draw_cr, event_masks, links = system in
  let sref = ref initial_state in

  area#misc#set_can_focus true;
  area#misc#set_app_paintable true;

  ignore (w#connect#destroy ~callback:quit);
  ignore (area#event#add event_masks);

  let connect_stateful_handler (Link (select_event, handler)) =
    let callback ev =
      let state, continue = handler (!sref) ev in
      sref := state; continue
    in ignore (select_event area#event#connect ~callback) in

  List.iter connect_stateful_handler links;
  let prepaint, paint = setup connect_stateful_handler draw_cr area w sref in

  w#present ();
  area#misc#grab_focus ();
  Base.Exn.protect
    ~finally: w#destroy
    ~f: (fun () -> action { quit=GMain.quit; prepaint; paint
                          ; frame_period = (fun () -> frame_period !sref)
                          ; should_stop  = (fun () -> stop !sref)})


let setup_double_buffer _connect draw_cr area _ sref =
  let on_draw (ctx : Cairo.context) =
    let w = float area#misc#allocated_width in
    let h = float area#misc#allocated_height in
    Cairo.set_source_rgb ctx 0. 0. 0.;
    Cairo.paint ctx;
    sref := draw_cr (w, h) ctx !sref;
    true
  in
  ignore (area#misc#connect#draw ~callback:on_draw);
  ((fun () -> ()), (fun () -> area#misc#queue_draw ()))


let setup_pixmap_backing _connect draw_cr area _w sref =
  let backing = ref (Cairo.Image.create Cairo.Image.ARGB32 ~w:400 ~h:400) in

  let configure _window ev =
    let width = GdkEvent.Configure.width ev in
    let height = GdkEvent.Configure.height ev in
    if width > 0 && height > 0 then
      backing := Cairo.Image.create Cairo.Image.ARGB32 ~w:width ~h:height;
    true
  in

  let on_draw (ctx : Cairo.context) =
    Cairo.set_source_surface ctx !backing ~x:0. ~y:0.;
    Cairo.paint ctx;
    true
  in

  let paint_backing () =
    let cr = Cairo.create !backing in
    let w = float area#misc#allocated_width in
    let h = float area#misc#allocated_height in
    Cairo.set_source_rgb cr 0.0 0.0 0.0;
    Cairo.paint cr;
    sref := draw_cr (w, h) cr !sref;
    area#misc#queue_draw ()
  in

  area#misc#set_double_buffered false;
  ignore (area#event#connect#configure ~callback:(configure ()));
  ignore (area#misc#connect#draw ~callback:on_draw);
  (paint_backing, fun () -> area#misc#queue_draw ())


let animate_with_timeouts (ui: 's ui) =
  let animate () =
    if ui.should_stop () then ui.quit ();
    ui.prepaint (); ui.paint (); true
  in ignore (Glib.Timeout.add ~ms:(int_of_float (1000.0 *. ui.frame_period ())) ~callback:animate);
  GMain.main ()

let animate_with_loop (ui: 's ui) =
  let rec check_pending t =
    if not (Glib.Main.pending ()) then update t
    else if Glib.Main.iteration false && not (ui.should_stop ()) then check_pending t
    else ()
  and update t =
    ui.prepaint (); sleep_until t; ui.paint ();
    check_pending (t +. ui.frame_period ())
  in update (get_time ())

let animate_with_loop_max (ui: 's ui) =
  let rec check_pending () =
    if not (Glib.Main.pending ()) then update ()
    else if Glib.Main.iteration false && not (ui.should_stop ()) then check_pending ()
    else ()
  and update () = ui.prepaint (); ui.paint (); check_pending ()
  in update ()

(* ---- Frame-clock-synced animation ---- *)

(* Like setup_pixmap_backing, but the draw callback self-schedules:
   advance simulation, render to backing, blit, queue_draw.
   Synced to the display refresh rate via GTK3's compositor. *)
let setup_pixmap_draw_loop _connect draw_cr area _w sref =
  let backing = ref (Cairo.Image.create Cairo.Image.ARGB32 ~w:400 ~h:400) in

  let configure _window ev =
    let width = GdkEvent.Configure.width ev in
    let height = GdkEvent.Configure.height ev in
    if width > 0 && height > 0 then
      backing := Cairo.Image.create Cairo.Image.ARGB32 ~w:width ~h:height;
    true
  in

  let on_draw (ctx : Cairo.context) =
    (* Blit current backing to window *)
    Cairo.set_source_surface ctx !backing ~x:0. ~y:0.;
    Cairo.paint ctx;
    (* Advance simulation and render next frame to backing *)
    let cr = Cairo.create !backing in
    let w = float area#misc#allocated_width in
    let h = float area#misc#allocated_height in
    Cairo.set_source_rgb cr 0.0 0.0 0.0;
    Cairo.paint cr;
    sref := draw_cr (w, h) cr !sref;
    (* Self-schedule for next frame *)
    ignore (area#misc#queue_draw ());
    true
  in

  area#misc#set_double_buffered false;
  ignore (area#event#connect#configure ~callback:(configure ()));
  ignore (area#misc#connect#draw ~callback:on_draw);
  ((fun () -> area#misc#queue_draw ()), (fun () -> ()))

(* Animation mode that just kicks off the draw loop and enters the GTK main loop.
   No wall-clock pacing — frames are driven by the display compositor. *)
let animate_with_draw_loop (ui: 's ui) =
  let check_stop () =
    if ui.should_stop () then (ui.quit (); false)
    else true
  in
  ignore (Glib.Timeout.add ~ms:200 ~callback:check_stop);
  ui.prepaint ();  (* kick off first frame *)
  GMain.main ()
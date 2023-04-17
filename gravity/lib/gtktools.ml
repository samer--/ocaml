open Utils

type 'e selector = GObj.event_signals -> callback:('e -> bool) -> GtkSignal.id
type 's link = | Link : 'e selector * ('s -> 'e -> 's * bool) -> 's link

let link sel h = Link (sel,h)

type 's painter = (float * float) -> Cairo.context -> 's -> 's
type 's system = 's              (* initial state *)
               * float           (* target frame period in seconds *)
               * ('s -> bool)    (* state implies we should stop? *)
               * 's painter      (* action to paint Cairo context and update state *)
               * Gdk.Tags.event_mask list (* which events to resond to *)
               * 's link list    (* events to connect *)

type 's ui = {quit       : (unit -> unit)
             ;prepaint   : (unit -> unit)
             ;paint      : (unit -> unit)
             ;should_stop: (unit -> bool)
             ;dt         : float
             }

let with_system setup (action: 's ui -> unit) (system: 's system) =
  let _ = GtkMain.Main.init () in
  let w = GWindow.window ~title:"Test" ~width:400 ~height:400
                         ~allow_grow:true ~allow_shrink:true () in
  let area = GMisc.drawing_area ~packing:w#add () in
  let quit _ = print_endline "Quitting"; GtkMain.Main.quit () in
  let initial_state, dt, stop, draw_cr, event_masks, links = system in
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

  w#show ();
  Base.Exn.protect
    ~f: (fun () -> action {quit=GMain.quit; prepaint=prepaint; paint=paint; dt=dt; should_stop=fun () -> stop !sref})
    ~finally: w#destroy


let setup_double_buffer connect_stateful_handler draw_cr area _ _ =
  let expose state _ev =
    let size = (let a = area#misc#allocation in (float a.Gtk.width, float a.Gtk.height)) in
    let cr = Cairo_gtk.create area#misc#window in
    Cairo.set_source_rgb cr 0. 0. 0.;
    Cairo.paint cr;
    draw_cr size cr state, true in

  area#misc#set_double_buffered true; (* is default anyway *)
  connect_stateful_handler (link (fun cs -> cs#expose) expose);
  ((fun () -> ()), (fun () -> area#misc#draw None))



let setup_pixmap_backing _ draw_cr area w sref =
  let backing = ref (GDraw.pixmap ~width:400 ~height:400 ()) in
  let configure window ev =
      let width, height = GdkEvent.Configure.(width ev, height ev) in
      let pixmap = GDraw.pixmap ~width ~height ~window () in
      pixmap#set_foreground (`NAME "blue");
      pixmap#rectangle ~x:0 ~y:0 ~width ~height ~filled:true ();
      Printf.printf "Configuring window with size %d x %d\n%!" width height;
      backing := pixmap;
      true in

  let expose ev =
    let rect = GdkEvent.Expose.area ev in
    let x, y, w, h = Gdk.Rectangle.(x rect, y rect, width rect, height rect) in
    let drawable = new GDraw.drawable (area#misc#window) in
    (* Printf.printf "expose\n%!"; *)
    drawable#put_pixmap ~x ~y ~xsrc:x ~ysrc:y ~width:w ~height:h !backing#pixmap;
    true in

  let paint_backing () =
      let size = (let a = area#misc#allocation in float a.Gtk.width, float a.Gtk.height) in
      let cr = Cairo_gtk.create !backing#pixmap in
      Cairo.set_source_rgb cr 0.0 0.0 0.0;
      Cairo.paint cr;
      sref := draw_cr size cr !sref in

  area#misc#set_double_buffered false;
  ignore (area#event#connect#configure ~callback:(configure w));
  ignore (area#event#connect#expose    ~callback:expose);
  (paint_backing, fun () -> area#misc#draw None)


let animate_with_timeouts (ui: 's ui) =
  let animate () =
    if ui.should_stop () then ui.quit ();
    (* GtkBase.Widget.queue_draw area#as_widget; *)
    ui.prepaint (); ui.paint (); true
  in ignore (Glib.Timeout.add ~ms:(int_of_float (1000.0 *. ui.dt)) ~callback:animate);
  GMain.main ()

let animate_with_loop (ui: 's ui) =
  let rec check_pending t =
    if not (Glib.Main.pending ()) then update t
    else if Glib.Main.iteration false && not (ui.should_stop ()) then check_pending t
    else ()
  and update t =
    ui.prepaint ();
    sleep_until t;
    ui.paint ();
    check_pending (t +. ui.dt)
  in update (get_time ())

let animate_with_loop_max (ui: 's ui) =
  let rec check_pending () =
    if not (Glib.Main.pending ()) then update ()
    else if Glib.Main.iteration false && not (ui.should_stop ()) then check_pending ()
    else ()
  and update () = ui.prepaint (); ui.paint (); check_pending ()
  in update ()

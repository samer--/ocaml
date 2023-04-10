open Utils

type 'e signal = callback:('e -> bool) -> GtkSignal.id
type ('s, 'e) handler = 's -> 'e -> 's * bool
type 'e selector = GObj.event_signals -> 'e signal
type 's link = | Link : 'e selector * ('s, 'e) handler -> 's link

let link sel h = Link (sel,h)

type 's painter = (float * float) -> Cairo.context -> 's -> 's
type 's system = 's * (GMisc.drawing_area -> unit)
                    * Gdk.Tags.event_mask list
                    * 's painter
                    * 's link list

type 's live_system = 's painter * GMisc.drawing_area * 's ref

let with_system (system: 's system) (action: (unit -> unit) -> 's live_system -> unit) =
  let _ = GtkMain.Main.init () in
  let w = GWindow.window ~title:"Test" ~width:400 ~height:400
                         ~allow_grow:true ~allow_shrink:true () in
  let area = GMisc.drawing_area ~packing:w#add () in
  let quit _ = print_endline "Quitting"; GtkMain.Main.quit () in
  let initial_state, init, event_masks, draw_cr, links = system in
  let sref = ref initial_state in

  let expose state _ev =
    let size = (let a = area#misc#allocation in (float a.width, float a.height)) in
    let cr = Cairo_gtk.create area#misc#window in
    Cairo.set_source_rgb cr 0. 0. 0.;
    Cairo.paint cr;
    draw_cr size cr state, true in

  area#misc#set_can_focus true;
  area#misc#set_double_buffered true; (* is default anyway *)

  ignore (w#connect#destroy ~callback:quit);
  ignore (area#event#add event_masks);

  let connect_stateful_handler (Link (select_event, handler)) =
    let callback ev =
      let state, continue = handler (!sref) ev in
      sref := state; continue
    in ignore (select_event area#event#connect ~callback) in

  List.iter connect_stateful_handler
            (link (fun cs -> cs#expose) expose :: links);
  init area;

  w#show ();
  let result = action GMain.quit (draw_cr, area, sref) in
  w#destroy ();
  print_endline "Leaving..";
  result

let animate_with_timeouts stop_from_state_ref tau system =
  with_system system (fun quit live_system ->
    let _, area, sref = live_system in
    let animate () =
      if stop_from_state_ref sref then quit ();
      let _ = GtkBase.Widget.queue_draw area#as_widget in true
    in ignore (Glib.Timeout.add ~ms:(int_of_float (1000.0 *. tau)) ~callback:animate);
    GMain.main ())

let animate_with_loop stop_from_state_ref tau system =
  with_system system (fun _ live_system ->
    let _draw_cr, area, sref = live_system in
    let rec check_pending t =
      if not (Glib.Main.pending ()) then update t
      else if Glib.Main.iteration false && not (stop_from_state_ref sref) then check_pending t
      else ()
    and update t =
      sleep_until t;
      area#misc#draw None; (* synchronous paint *)
      check_pending (t +. tau)
    in update (get_time ()))

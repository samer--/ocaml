open Utils

type 'e signal = callback:('e -> bool) -> GtkSignal.id
type ('s, 'e) handler = 's -> 'e -> 's * bool
type 'e selector = GObj.event_signals -> 'e signal
type 's link = | Link : 'e selector * ('s, 'e) handler -> 's link

let link sel h = Link (sel,h)

type 's system = 's * (GMisc.drawing_area -> unit)
                    * Gdk.Tags.event_mask list
                    * (float -> float -> Cairo.context -> 's -> 's)
                    * 's link list


let with_system (system: 's system) action =
  let _ = GtkMain.Main.init () in
  let w = GWindow.window ~title:"Test" ~width:400 ~height:400
                         ~allow_grow:true ~allow_shrink:true () in
  let area = GMisc.drawing_area ~packing:w#add () in
  let quit _ = print_endline "Quitting"; GtkMain.Main.quit () in
  let initial_state, init, event_masks, draw_cr, links = system in
  let sref = ref initial_state in
  let cc s handler =
      let callback ev =
        let state, cont = handler (!sref) ev in
        sref := state; cont
      in ignore (s ~callback) in

  let expose state ev =
    let {Gtk.width=width; Gtk.height=height; _} = area#misc#allocation in
    let cr = Cairo_gtk.create area#misc#window in
    Cairo.set_source_rgb cr 0. 0. 0.;
    Cairo.paint cr;
    draw_cr (float width) (float height) cr state, true in

  area#misc#set_can_focus true;
  ignore (w#connect#destroy quit);
  ignore (area#event#add event_masks);
  List.iter (fun (Link (sel, h)) -> cc (sel area#event#connect) h)
            (link (fun cs -> cs#expose) expose :: links);
  init area;

  w#show ();
  let result = action area sref draw_cr GMain.quit in
  w#destroy ();
  print_endline "Leaving..";
  result

let animate_with_timeouts stop_from_state_ref tau system =
  with_system system (fun area sref _ quit ->
    let animate () =
      if stop_from_state_ref sref then quit ();
      let _ = GtkBase.Widget.queue_draw area#as_widget in true
    in ignore (Glib.Timeout.add (int_of_float (1000.0 *. tau)) animate);
    GMain.main ())

let animate_with_loop stop_from_state_ref tau system =
  with_system system (fun area sref draw_cr _quit ->
    let rec check_pending t =
      if not (Glib.Main.pending ()) then update t
      else if Glib.Main.iteration false && not (stop_from_state_ref sref) then check_pending t
      else ()
    and update t =
      let alloc = area#misc#allocation in
      let width, height = float alloc.Gtk.width, float alloc.Gtk.height in
      let cr = Cairo_gtk.create area#misc#window in
      sleep_until t;
      Cairo.set_source_rgb cr 0. 0. 0.;
      Cairo.paint cr;
      sref := draw_cr width height cr !sref;
      check_pending (t +. tau)
    in update (get_time ()))


open Utils

(** A module whose submodules implement a variety of lazy data structures. *)

module Tree = struct
  type 'a tree = Leaf of 'a | Node of 'a tree list thunk

  let leaf x = Leaf x
  let node d = Node (const d)

  (* iter :: ('a -> unit) -> 'a tree -> unit *)
  let rec iter f = function
    | Leaf x -> f x
    | Node ast -> List.iter (fun at -> iter f at) (ast ())

  (* print : ('a -> string) -> 'a tree -> unit
   * Draws a picture of the tree using [string_of_val] to render the leaves *) 
  let print string_of_val tree = 
    let rec print_aux prefix tree = 
      Printf.printf "%s:" prefix;
      match tree with
      | Leaf x -> print_endline (" "^string_of_val x)
      | Node tst -> print_endline "-\\"; List.iter (print_aux (prefix ^ "   |")) (tst ())
    in print_aux " " tree
end

module TreeAlt = struct
  type 'a tree = Leaf of 'a | Node of 'a tree thunk list

  (* iter :: ('a -> unit) -> 'a tree -> unit *)
  let rec iter f = function
    | Leaf x -> f x
    | Node tts -> List.iter (fun tt -> iter f (tt ())) tts
end


module WTree = struct
  (* This is rather like Tree, but with weighted edges, that is, each child
   * of a node is annotated with a weight.
   *)
  open Dist

  type 'a tree = Leaf of 'a | Node of 'a tree dist thunk
  (* NB equivalent to Node of (weight * 'a tree) list thunk *)

  (* Maybe these should be in the monad? *)
  let leaf x = Leaf x
  let node d = Node (const d)

  (* iter :: (weight -> 'a -> unit) -> weight -> 'a tree -> unit *)
  let rec iter f w0 = function
    | Leaf x -> f w0 x
    | Node ast -> List.iter (fun (w,at) -> iter f (w*.w0) at) (ast ())


  (* print : ('a -> string) -> 'a tree -> unit
   * Draws a picture of the tree using [string_of_val] to render the leaves *) 
  let print string_of_val tree = 
    let rec print_aux prefix (w,tree) = 
      let label = string_of_weight w in
      let pad = String.make (String.length label) ' ' in
      Printf.printf "%s-%s:" prefix label;
      match tree with
      | Leaf x -> print_endline (" "^string_of_val x)
      | Node tst -> print_endline "-\\"; List.iter (print_aux (prefix^pad^"   |")) (tst ())
    in print_aux " " (one,tree)

  module Cursor : sig
    type 'a cursor
    type 'a context

    val top : 'a tree -> 'a cursor

    (* these are all partial functions *)
    val down : 'a cursor -> 'a cursor
    val up : 'a cursor -> 'a cursor
    val left : 'a cursor -> 'a cursor
    val right : 'a cursor -> 'a cursor
    val children : 'a cursor -> 'a tree dist
    val value : 'a cursor -> 'a
    val node : 'a cursor -> 'a tree

  end = struct

    type 'a context = Top | Inner of 'a tree dist thunk * 'a context * weight * 'a tree dist * 'a tree dist
    type 'a cursor = C of 'a tree * 'a context 

    let top t = C (t, Top)
    let down  (C (Node th,path)) = let (w,t)::tx = th () in C (t, Inner (th,path,w,[],tx)) 
    let right (C (t,Inner (th, path, w, lx, (rw,rt)::rx))) = C (rt, Inner (th, path, rw, (w,t)::lx, rx))
    let left  (C (t,Inner (th, path, w, (lw,lt)::lx, rx))) = C (lt, Inner (th, path, lw, lx, (w,t)::rx))
    let up    (C (t,Inner (th, path, _, _, _))) = C (Node th, path)

    let children (C (Node th,_)) = th ()
    let value (C (Leaf x,_)) = x
    let node (C (n,_)) = n
  end
end

module WFTree = struct
  (* This is like WTree, but with an explicit failure constructor
   *)
  open Dist

  type 'a tree = Stump | Leaf of 'a | Node of 'a tree dist thunk

  (* iter :: (weight -> 'a -> unit) -> weight -> 'a tree -> unit *)
  let rec iter f w0 = function
    | Leaf x -> f w0 x
    | Node ast -> List.iter (fun (w,at) -> iter f (w*.w0) at) (ast ())
    | Stump -> ()

  (* depth first enumeration with optional depth limit *)
  let rec foldl_bounded depth f s0 t0 = 
    (* recursive bounded folder *)
    let rec bfold d w0 s0 (w,tree) = match tree with
      | Stump -> s0
      | Leaf x -> f s0 (w*.w0, Leaf x)
      | Node tst -> if d<=0 then f s0 (w*.w0, Node tst) 
                    else List.fold_left (bfold (d-1) (w*.w0)) s0 (tst ()) 

    (* recursive unbounded folder is a bit simpler *)
    in let rec ufold w0 s0 (w,tree) = match tree with
      | Leaf x -> f s0 (w*.w0, Leaf x)
      | Node tst -> List.fold_left (ufold (w*.w0)) s0 (tst ())
      | Stump -> s0

    (* choose bounded or unbounded depending on depth option *)
    in (match depth with
        | Some depth -> bfold depth 
        | None -> ufold) one s0 (one,t0)

  (* !!! to do:
    * think about breadth first search by list appending
    * print messages about dead ends and numbers of worlds?
    *)


  (* print : ('a -> string) -> 'a tree -> unit
   * Draws a picture of the tree using [string_of_val] to render the leaves *) 
  let print string_of_val tree = 
    let rec print_aux prefix (w,tree) = 
      Printf.printf "%s-%s:" prefix (string_of_weight w);
      match tree with
      | Leaf x -> print_endline (" "^string_of_val x)
      | Node tst -> print_endline "-\\"; List.iter (print_aux (prefix^"       |")) (tst ())
      | Stump -> print_endline ("-*")
    in print_aux " " (one,tree)
end

module WTreeAlt = struct
  open Dist

  type 'a tree = Leaf of 'a | Node of 'a tree thunk dist

  (* iter :: (weight -> 'a -> unit) -> weight -> 'a tree -> unit *)
  let rec iter f w0 = function
    | Leaf x -> f w0 x
    | Node tts -> List.iter (fun (w,tt) -> iter f (w*.w0) (tt ())) tts


  (* print : ('a -> string) -> 'a tree -> unit
   * Draws a picture of the tree using [string_of_val] to render the leaves *) 
  let print string_of_val tree = 
    let rec print_aux prefix (w,tt) = 
      let label = string_of_weight w in
      let pad = String.make (String.length label) ' ' in
      Printf.printf "%s-%s:" prefix label;
      match tt () with
      | Leaf x -> print_endline (" "^string_of_val x)
      | Node ts -> print_endline "-\\"; List.iter (print_aux (prefix^pad^"   |")) ts
    in print_aux " " (one,const tree)
end

module WFTreeAlt = struct
  open Dist

  type 'a tree = Stump | Leaf of 'a | Node of 'a tree thunk dist

  (* iter :: (weight -> 'a -> unit) -> weight -> 'a tree -> unit *)
  let rec iter f w0 = function
    | Leaf x -> f w0 x
    | Node tts -> List.iter (fun (w,tt) -> iter f (w*.w0) (tt ())) tts
    | Stump -> ()

  (* print : ('a -> string) -> 'a tree -> unit
   * Draws a picture of the tree using [string_of_val] to render the leaves *) 
  let print string_of_val tree = 
    let rec print_aux prefix (w,tt) = 
      let label = string_of_weight w in
      let pad = String.make (String.length label) ' ' in
      Printf.printf "%s-%s:" prefix label;
      match tt () with
      | Leaf x -> print_endline (" "^string_of_val x)
      | Stump  -> print_endline "-X" 
      | Node ts -> print_endline "-\\"; List.iter (print_aux (prefix^pad^"   |")) ts
    in print_aux " " (one,const tree)
end

module BTree = struct
(*
    /\        /\        /\        /\       /\
   /\ \      /\ \      / /\      / /\     /  \
  /\ \ \    / /\ \    / /\ \    / / /\   /\  /\
  *)
  
  type 'a btree = Leaf | Node of 'a * 'a btree * 'a btree

  let rec annotate = function
    | Leaf -> (1,Leaf)
    | Node (_, t1, t2) -> 
        let (n1,t1) = annotate t1 in
        let (n2,t2) = annotate t2 in
        let nn = n1+n2 in
        (nn,Node (nn,t1,t2))

  (* let l = Leaf *)
  (* let n t1 t2 = Node ((), t1, t2) *)

  let draw t =
    let plot x ch (pos,chars) = (x, ch :: iterate (x-pos-1) (cons ' ') chars) in
    let flush w (pos,chars) = List.rev (iterate (w-pos) (cons ' ') chars) in
    let left x = plot x '/' in
    let right x = plot (x+1) '\\' in

    (* update scan line, y is current height in diagram *)
    let scan y (s,dl) (dx,x,t) = match t with 
      | Node (yy,t1,t2) when yy=y -> ((+1,x+1,t2) :: (-1,x-1,t1) :: s, (right x ** left x) dl)
      | _ -> ((dx,x+dx,t) :: s, (if dx=1 then right else left) x dl) in

    let rec drawx = function
      | (1,_,raster) -> raster
      | (y,s,raster) ->
          let (s', line) = List.fold_left (scan y) ([],(0,[]))  s in
          drawx (y-1, List.rev s', line :: raster) in

    let (nn,ct) = annotate t in
    drawx (nn, [(0,nn-1,ct)], []) 
      |> List.map (flush (2 * pred nn)) |> List.rev
      |> List.iter (fun row -> List.iter print_char row; print_newline ()) 
end


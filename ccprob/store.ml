(* My version of Kiselyov's first-class storage. 
 * A store is an immutable, purely functional data structure representing a
 * map from integer keys or locators to arbitrary values. The store can hold
 * values of any type by using the Dynamic module from Utils to do some funny
 * business with mutable references, but all of that is hidden so that the
 * interface should appear pure.
 *)
open Utils

module Store : sig

  type t
  type 'a loc

  val empty : t
  val new_loc   : unit -> 'a loc 
  val get : 'a loc -> t -> 'a 
  val put : 'a loc -> 'a -> t -> t
  val upd : 'a loc -> ('a -> 'a) -> t -> t

end = struct

  (* module M = Map.Make(struct type t=int let compare = (-) end) *)
  module M = BatIMap

  open Utils.Dynamic

  (* the map is a standard map from integers to dyn values *)
  type map = dyn M.t

  (* the store is a map and the integer value of the next unused key *)
  type t =  map
  type 'a loc = int * ('a -> dyn) * (dyn -> 'a)

  let next_id = ref 0 (* for globally unique id's without accessing store *)

  let empty = M.empty (==)

  let get (j,_,outd) m = outd (M.find j m) 
  let put (j,ind,_) x m = M.add j (ind x) m
  let upd (j,ind,outd) f m = M.modify j (fun x -> ind (f (outd x))) m

  (* new_loc without initialisation *)
  let new_loc () =
    let i = !next_id in
    let _ = next_id := succ i in
    let (ind,outd) = newdyn () in (i,ind,outd)
end

(* This is the older version which keeps track of the next available
   location number as a value with the store. This means that a mutable
   reference is not required as above, but creating a new empty location
   becomes more expensive as we have to update the (int * map) pair
   used to represent the store.
 *)
module StoreAlt : sig

  type t
  type 'a loc

  val empty : t
  val new_loc   : t -> 'a loc * t
  val get : 'a loc -> t -> 'a 
  val put : 'a loc -> 'a -> t -> t
  val upd : 'a loc -> ('a -> 'a) -> t -> t

end = struct

  (* module M = Map.Make(struct type t=int let compare = (-) end) *)
  module M = BatIMap

  open Utils.Dynamic

  (* the map is a standard map from integers to dyn values *)
  type map = dyn M.t

  (* the store is a map and the integer value of the next unused key *)
  type t =  int * map
  type 'a loc = int * ('a -> dyn) * (dyn -> 'a)

  let empty = (0,M.empty (==))

  let get (j,_,outd) (_,m) = outd (M.find j m) 
  let put (j,ind,_) x (i,m) = (i,M.add j (ind x) m)
  let upd (j,ind,outd) f (i,m) = (i,M.modify j (fun x -> ind (f (outd x))) m)

  (* new_loc without initialisation *)
  let new_loc (i,m) =
    let (ind,outd) = newdyn () in ((i,ind,outd),(i+1,m))
end

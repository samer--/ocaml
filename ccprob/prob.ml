open Delimcc
open Utils
open Monads
open Monadreps
open Store
open Dist

type 'a mapdist = 'a MDist.t

module type PROB = sig
  (* A signature for direct representation of probabilistic effects combined
   * with state for memoisation *)

  type 'a m
  type 'a var

  val fail    : unit -> 'a
  val dist    : 'a dist -> 'a
  val reflect : 'a m -> 'a 
  val reify   : (unit -> 'a) -> 'a m
  val letlazy : (unit -> 'a) -> unit -> 'a
  val memo    : ('a -> 'b) -> 'a -> 'b

  val letvar : (unit -> 'a) -> 'a var
  val constrain : 'a var -> ('a -> unit) -> unit 
  val force : 'a var -> 'a
end

module type EXPLORE = sig
  type 'a m

  val flatten : int option -> 'a m -> 'a m
  val search_bf : 'a m -> 'a option
  val search_df : 'a m -> 'a option
  val accum : weight -> 'a m -> 'a mapdist -> 'a mapdist 
  val print : ('a -> string) -> 'a m -> unit
end

module InfOps (P : PROB) (I : EXPLORE with type 'a m = 'a P.m) = struct
  let exact_reify f = I.flatten None (P.reify f)
  let variable_elim f arg = P.reflect (I.flatten None (P.reify (fun () -> f arg)))
  let reify_to_mdist f = I.accum one (P.reify f) MDist.empty
  let reify_to_dist f = MDist.to_dist (reify_to_mdist f)
end

module ExploreOps (I : EXPLORE) = struct
  type ('a,'b) sampler = 'a I.m -> 'b
  type 'a mapsampler = ('a, 'a mapdist transformer) sampler

  exception Failure

  include I

  (* fmap_sampler : ('b -> 'c) -> ('a,'b) sampler -> ('a,'c) sampler *) 
  let fmap_sampler f sampler tree = f (sampler tree)

  let accum_simple x = MDist.accum (one,x)
  let accum_weighted = MDist.accum  

  (* collect with exception catching and counting *)
  let collect n sampler tree = 
    let open Pair in
    let acc' s = try sampler tree $> s with Failure -> succ <$ s in
    MDist.to_dist $>  iterate n acc'  (0,MDist.empty) 

  (* collect from failure counting function *)
  let collect' n sampler tree =
    let open Pair in
    MDist.to_dist $> iterate n (sampler tree) (0,MDist.empty) 

  (* collect from non-failure counting function *)
  let collect'' n sampler tree =
    (0,MDist.to_dist (iterate n (sampler tree) MDist.empty))
end

module type STATE = sig
  type t

  val get : unit -> t
  val put : t -> unit 
  val upd : (t -> t) -> unit
  val reflect : (t -> 'a * t) -> 'a
end

module State (S : TYPE) = struct
  (* Direct representation of state monad StateM *)
  module M = StateM(S)
  module R = Direct(M)

  type t = S.t

  let reify   = R.reify
  let reflect = R.reflect
  let put s   = reflect (M.put s)
  let get ()  = reflect (M.get)
  let upd f   = reflect (M.upd f)
end

module Memo (S : STATE with type t=Store.t) : sig 

  val memo : ('a -> 'b) -> 'a -> 'b
  val letlazy : 'b thunk -> 'b thunk

  type 'a var
  val letvar : (unit -> 'a) -> 'a var
  val force : 'a var -> 'a
  val constrain : 'a var -> ('a -> unit) -> unit 

end = struct

  let new_ref () = Store.new_loc ()
  let put loc x  = S.upd (Store.put loc x)
  let upd loc f  = S.upd (Store.upd loc f)
  let get loc    = Store.get loc (S.get ())

  let memo f = let loc = new_ref () in 
    put loc BatMap.empty;
    fun x ->
      try BatMap.find x (get loc)
      with Not_found -> let v = f x in 
        upd loc (BatMap.add x v); v

  let letlazy f = let loc = new_ref () in 
    fun () -> try get loc with Not_found -> 
      let v = f () in put loc v; v

  type 'a varstate = Unbound of 'a thunk | Bound of 'a
  type 'a var = 'a varstate Store.loc

  let letvar f = let loc = Store.new_loc () in put loc (Unbound f); loc
  let force v = match get v with
    | Bound x -> x
    | Unbound f -> let x = f () in put v (Bound x); x

  let filter g f () = let x = f () in g x; x
  let constrain v g = match get v with
    | Bound x -> g x 
    | Unbound f -> put v (Unbound (filter g f))
end


module Ops (P : PROB) = struct
  open P

  (* let check d = *) 
  (*   let tot = total d in *)
  (*   if tot > 1.00000000001 || tot < 0.9999999999 then *) 
  (*     print_endline ("dist': bad normalisation: ["^ (Format.list "," Format.float (weights d))) *)

  let dist' = function 
     | [] -> fail ()
     | [(_,x)] -> x
     | xs -> dist xs

  let uniform = function
    | [] -> fail ()
    | [x] -> x
    | xs -> let rec uni p = function | [] -> [] | x::t -> (p,x) :: uni p t in
            dist (uni (recip_int (List.length xs)) xs)

  let uniform_range n m = uniform (n--m)
  let uniform_nat m = uniform (0--(m-1))
  let bernoulli p = dist [p,1; one -. p,0]
  let flip p = dist [p,true; one -. p,false]
  let observe t f = let v=f () in if t v then v else fail ()
  let observe' t f () = let v=f () in if t v then v else fail ()
  let rec chain p f = if flip p then f () :: chain p f else []
  let geometric p =
    let rec proc n = if flip p then n else proc (succ n)
    in proc 0

  let rec repeat n f = 
    if n=0 then [] else f () :: repeat (pred n) f

  let rec map f = function
    | x :: xs -> f x :: map f xs
    | [] -> []

  let unify (_,wr) x = if wr x then () else fail ()
  let read (r,_) = r ()
end

(* for list-like data types *)
module type SEQ = sig
  type 'a l

  val equals    : 'a list -> 'a l -> bool
  val split_at  : int -> 'a l -> ('a l * 'a l)
  val length    : 'a l -> int
  val nil       : 'a l
  val from_list : 'a list -> 'a l
  val to_list   : 'a l -> 'a list
  val append    : 'a l -> 'a l -> 'a l
  val map       : ('a -> 'b) -> 'a l -> 'b l
end

(* SEQ using plain lists *)
module ListX : SEQ = struct
  open List

  type 'a l = 'a list

  let map = List.map
  let length = List.length
  let append = List.append
  let equals l ll = (ll=l) 
  let nil = []
  let from_list x = x
  let to_list x = x
  let rec split_at n lst =
    if n = 0 then (nil, lst)
    else match lst with
    | [] -> ([],[])
      | (h::t)  ->
        let (x1,x2) = split_at (pred n) t in (h::x1, x2)
end

(* Lazy Lists  *)
module LList (P : PROB) = struct
  module PO = Ops(P)
  open P
  open PO

  type 'a lcons = LNil | LCons of ('a thunk) * 'a llist
  and  'a llist = 'a lcons thunk

  type 'a l = 'a llist

  let nil  = fun () -> LNil;;
  let cons h t = fun () -> LCons (h,t);;
  let is_nil (l : 'a llist) = (l () = LNil)

  let rec append (y : 'a llist) (z : 'a llist) =
    letlazy (fun () -> 
    match y () with
    | LNil -> z ()
    | LCons (h,t) -> LCons (h, append t z));;

  let rec from_list = function
    | [] -> nil
    | (h::t) -> cons (fun () -> h) (from_list t);;


  let lreflect x = x ();;

  let rec to_list x = match x () with
    | LNil -> []
    | LCons (h,t) -> h () :: to_list t

  let rec length l = match l () with
    | LNil -> 0
    | LCons (_,t) -> 1 + length t

  let rec split_at n lst =
    if n = 0 then (nil, lst)
    else match lst () with
      | LNil -> (nil,nil)
      | LCons (h,t)  ->
        let (x1,x2) = split_at (pred n) t in
        (cons h x1, x2)

  let rec map' f = function
    | LNil -> LNil
    | LCons (h,t) -> LCons (letlazy (fun () -> f (h ())), map f t)
  and map f l = letlazy (fun () -> map' f (l ()))

  let rec equals l ll =
    match (ll (), l) with
    | (LNil,[]) -> true
    | (LCons (h1,t1), (h2::t2)) -> 
        if h1 () = h2 then equals t2 t1
        else false
    | _ -> false
end

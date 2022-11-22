
module type FIELD = sig
  type t

  val one  : t
  val zero : t
  val ( * ) : t -> t -> t
  val ( + ) : t -> t -> t
	val recip : t -> t
  val neg : t -> t
  val pow : float -> t -> t
end

module type VECTOR = sig
  type t
	type s

	module Field: FIELD with type t = s

  val ( *> ) : s -> t -> t
  val ( <+> ) : t -> t -> t
  val ( <*> ) : t -> t -> s
  val negV: t -> t
  (* val zeroV : t *)
end

module Float = struct
  type t = float
  let one = 1.0
  let zero = 0.0
  let ( * ) =  Pervasives.( *. )
  let ( + ) =  Pervasives.( +. )
  let recip x = Pervasives.(1.0 /. x)
  let neg x = Pervasives.(~-. x)
  let pow y x = x ** y
end

module type NAT = sig val n : int end

module type FUNCTOR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val fold2 : ('s -> 'a -> 'b -> 's) -> 's -> 'a t -> 'b t -> 's
  (* val fill : 'a -> 'a t *)
end

module ListN (N: NAT) = struct
  type 'a t = 'a list

  (* let fill x = rep N.n x *)
  let map = List.map
  let map2 = List.map2
  let fold2 = List.fold_left2
end

module FunctorVector (A:FUNCTOR) (F:FIELD) = struct
  type t = F.t A.t
  type s = F.t

  module Field = F
  open F

  let ( *> ) k = A.map (( * ) k)
  let ( <+> ) = A.map2 ( + )
  let ( <*> ) = A.fold2 (fun s x y -> s + x*y) zero 
  let negV = A.map neg
  (* let zeroV = A.fill zero *) 
end

module FieldOps (F:FIELD) = struct
	include F
	let ( / ) x y = x * recip y
	let ( - ) x y = x + neg y
  let sqrt = pow 0.5
	let sum xs = List.fold_left ( + ) zero xs
  let of_float k = pow (log k /. log 2.0) (one + one)
end

module VectorOps (V:VECTOR) = struct
  module F = FieldOps(V.Field)
  include V
  (* include F *)

  let ( </ ) x y = (F.recip y) *> x
  let ( <-> ) x y = x <+> negV y
end


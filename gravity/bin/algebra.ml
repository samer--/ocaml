
module type FIELD = sig
  (* A FIELD is a structure that supports two commutative groups,
     'addition' and 'multplication' over the same type. Hence, both
     operations have an identity element and inverse operations. In
     addition multiplication distributes over addition.
   *)
  type t

  val one  : t
  val zero : t
  val ( * ) : t -> t -> t
  val ( + ) : t -> t -> t
	val recip : t -> t
  val neg : t -> t
  val pow : float -> t -> t
  val of_float : float -> t
end

module type VECTOR = sig
  (* A vector space is defined over a FIELD. The vectors form an Abelian
     group under addition, and scalar multiplication satisfies certain rules.
     Defined below is actually an inner product space because we include the dot product
  *)
  type t (* the type of vectors *)
	type s (* the type of scalars *)

	module Field: FIELD with type t = s

  val ( *> ) : s -> t -> t   (* scalar multiplication *)
  val ( <+> ) : t -> t -> t  (* vector addition *)
  val ( <*> ) : t -> t -> s  (* dot product *)
  val negV: t -> t
  (* val zeroV : t *) (* should exist, but I don't need it apparently *)
end

module Float = struct
  (* Float is an instance of FIELD *)
  type t = float
  let one = 1.0
  let zero = 0.0
  let ( * ) =  Stdlib.( *. )
  let ( + ) =  Stdlib.( +. )
  let recip x = Stdlib.(1.0 /. x)
  let neg x = Stdlib.(~-. x)
  let pow y x = x ** y
  let of_float x = x
end

module type NAT = sig val n : int end

module type FUNCTOR = sig
  (* this looks a bit weird - more like Foldable + Applicative/Zip *)
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
  (* This is also bit weird - a vector defined as a containerish thing (Functor)
     of values from a FIELD *)
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
end

module VectorOps (V:VECTOR) = struct
  module F = FieldOps(V.Field)
  include V
  (* include F *)

  let ( </ ) x y = (F.recip y) *> x
  let ( <-> ) x y = x <+> negV y
end


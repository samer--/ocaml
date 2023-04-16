
module type SCALAR = sig
  (* A SCALAR is a field (ie with 'addition' and 'multplication')
   * and in addition the ability to raise to a float-valued power.
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

module ScalarOps (S:SCALAR) = struct
	include S
	let ( / ) x y = x * recip y
	let ( - ) x y = x + neg y
  let sqrt = pow 0.5
end

module type VECTOR = sig
  (* A vector space is defined over a field. The vectors form an Abelian
     group under addition, and scalar multiplication satisfies certain rules.
     Defined below is actually an inner product space because we include the dot product.
     We also require the field to be a SCALAR so we can have powers for differentiation.
  *)
  type t (* the type of vectors *)

	module Scalar: SCALAR

  val ( *> ) : Scalar.t -> t -> t   (* scalar multiplication *)
  val ( <+> ) : t -> t -> t         (* vector addition *)
  val ( <*> ) : t -> t -> Scalar.t  (* dot product *)
  val negV: t -> t
  (* val zeroV : t *) (* should exist, but I don't need it apparently *)
end

module Float : SCALAR with type t = float = struct
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

(* Direct sum of two vector spaces over same field, aka product in categorical sense *)
module VSum (V1:VECTOR) (V2:VECTOR with module Scalar = V1.Scalar)
  : VECTOR with type t = V1.t * V2.t and module Scalar = V1.Scalar
= struct
  type t = V1.t * V2.t
  module Scalar = V1.Scalar

  let ( *> ) k (x,y) = (V1.(k *> x), V2.(k *> y))
  let ( <+> ) (x1,y1) (x2,y2) = (V1.(x1 <+> x2), V2.(y1 <+> y2))
  let ( <*> ) (x1,y1) (x2,y2) = Scalar.(V1.(x1 <*> x2) + V2.(y1 <*> y2))
  let negV (x,y) = (V1.negV x, V2.negV y)
end

module VList (V:VECTOR): VECTOR with type t = V.t list and module Scalar = V.Scalar = struct
  type t = V.t list
  module Scalar = V.Scalar
  open Scalar
  open List

  let ( *> ) k xs = map (V.( *> ) k) xs
  let ( <+> ) = map2 V.(<+>)
  let ( <*> ) xs1 xs2 = fold_left (+) zero (map2 V.( <*> ) xs1 xs2)
  let negV = map V.negV
end

module Vec2D (S:SCALAR) : VECTOR with module Scalar = S and type t = S.t * S.t = struct
  type t = S.t * S.t

  module Scalar = S
  open S

  let ( *> ) k (x,y) = (k * x, k * y)
  let ( <+> ) (x1,y1) (x2,y2) = (x1 + x2, y1 + y2)
  let ( <*> ) (x1,y1) (x2,y2) = (x1 * x2) + (y1 * y2)
  let negV (x,y) = (neg x, neg y)
end

module VectorOps (V:VECTOR) = struct
  include V
  open ScalarOps (Scalar)
  type v = V.t
  type s = Scalar.t

  let ( </ ) x y = recip y *> x
  let ( <-> ) x y = x <+> negV y
end

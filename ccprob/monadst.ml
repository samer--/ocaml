(** Equivalents of Haskell's MonadRef type class - provides mutable references *)

open Monads
open Store
open Utils

(** A signature for monads that provided polypmorphic updatable references.
 * Modelled on Haskell's [Control.Monad.ST]. The underlying implementation,
 * whatever it is, is hidden. *)
module type MONADREF = sig
  include MONAD
  type 'a ref 

  val new_ref : 'a -> 'a ref m
  val put_ref : 'a ref -> 'a -> unit m
  val upd_ref : 'a ref -> ('a -> 'a) -> unit m 
  val get_ref : 'a ref -> 'a m 
end

(** Implementation of MONADREF using any functor that builds a MONADSTATE from a state type. 
 *  Internally, the [Store] module is used to manage an extensible polymorphic
 *  key-value store, which is threaded through computations using the provided
 *  MONADSTATE building functor.
 *)
module StoreRef (S : functor(T:TYPE) -> MONADSTATE with type state = T.t) = struct
    (* MONADREF with type 'a m = 'a S(Store).m val run 'a m -> 'a = struct *)
  module SS = S(Store)      (* state monad over stores *)
  module SO = MonadOps(SS)
  open SO
  
  type 'a m = 'a SS.m
  type 'a ref = 'a Store.loc

  let return = SS.return
  let bind = SS.bind

  let put_ref loc x  = SS.upd (Store.put loc x)
  let upd_ref loc f  = SS.upd (Store.upd loc f)
  let get_ref loc    = SS.get >>= SS.return ** Store.get loc 
  let new_ref x = let loc = Store.new_loc () in 
                  bind (put_ref loc x) (fun _ -> return loc)

  let run m = fst (m Store.empty)
end


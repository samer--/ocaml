(* Base monads *)
open Utils

(* This follows Filinkski's definitions from 
 *
 * A. Filinski. Representing layered monads. In Proceedings of the 26th ACM
 * SIGPLAN-SIGACT symposium on Principles of programming languages, pages
 * 175--188. ACM, 1999.
 *)

module type MONAD = sig
  type 'a m
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

(* Polymorphic signature: one module should be able to handle all types *)
module type PROBMONAD = sig
  include MONAD

  val choice : 'a Dist.dist -> 'a m
  val fail : 'a m
end

module type MONADPLUS = sig
  include MONAD

  val mzero : unit -> 'a m
  val mplus : 'a m -> 'a m -> 'a m
end

(** Signature for a functor representing a monad transformer that
 * provides nondeterminism with a given monad. *)
module type MONADPLUST = functor (M : MONAD) -> sig
  include MONADPLUS
  val lift : 'a M.m -> 'a m
  val fold : ('b -> 'a -> 'b M.m)  -> 'b -> 'a m -> 'b M.m
end

module MonadOps (M : MONAD) = struct
  open M

  let (>>=) = bind
  let (=<<) f m = bind  m f
  let (>>) m1 m2 = bind m1 (fun _ -> m2)
  let fmap f m = m >>= return ** f

  let rec sequence = function 
    | [] -> return []
    | m::ms -> m >>= (fun x -> sequence ms >>= (fun xs -> return (x::xs)))

  let sequence_ ms = sequence ms >> return ()

  let mapM f = sequence ** (List.map f)
  let mapM_ f = sequence_ ** (List.map f)
  let forM s f = mapM f s
  let forM_ s f = mapM_ f s
  let rec foldM f s = function
    | [] -> return s
    | x::xs -> f s x >>= fun s' -> foldM f s' xs

  let liftM op m1 = m1 >>= (fun x -> return (op x))
  let liftM2 op m1 m2 = m1 >>= (fun x -> m2 >>= (fun y -> return (op x y)))
end


module type MONADSTATE = sig
  include MONAD
  type state

  val get : state m
  val put : state -> unit m
  val upd : (state -> state) -> unit m
end

module StateM (State : TYPE) = struct
  (* Functional representation of state monad. *)
  type 'a m = State.t -> 'a * State.t 
  type state = State.t

  let return x s = (x,s)
  let bind m f s = let (x,s')=m s in f x s'

  let get s = (s,s)
  let put s _ = ((),s)
  let upd f s = ((),f s)
end

(* State monad transformer *)
module StateT (State : TYPE) (M : MONAD) = struct
  type 'a m = State.t -> ('a * State.t) M.m
  type state = State.t

  let return x s = M.return (x,s)
  let bind m f s = M.bind (m s) (uncurry f)

  let get s = M.return (s,s)
  let put s _ = M.return ((),s)
  let upd f s = M.return ((),f s)

  let lift m s = M.bind m (fun x -> M.return (x,s))
end

module ReaderM (Env : TYPE) = struct
  type 'a m = Env.t -> 'a 

  let return x e = x
  let bind m f e = f (m e) e

  let ask e = e
  let local e m _ = m e
end

module IdM = struct
  type 'a m = 'a
  let return x = x
  let bind m f = f m
end

module ListM = struct
  type 'a m = 'a list

  open List
  let return x = [x]
  let bind m f = concat (map f m)
  let fail = []
  let mplus = List.append
  let mzero () = []
end

module ListT (M : MONAD) : sig
  type 'a m = 'a list M.m
  type 'a b = 'a M.m

  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val mplus : 'a m -> 'a m -> 'a m
  val mzero : unit -> 'a m
  val lift : 'a b -> 'a m
  val fold : ('b -> 'a -> 'b M.m)  -> 'b -> 'a m -> 'b M.m

end = struct
  type 'a m = 'a list M.m
  type 'a b = 'a M.m
  module MO = MonadOps (M)
  open MO

  let return x = M.return [x]
  let bind m f = m >>= mapM f >>= (M.return ** List.concat)
  (* let bind m f = fmap List.concat (m >>= mapM f) *)
  let mplus f g = liftM2 (@) f g
  let mzero () = M.return []
  let lift m = M.bind m return
  let fold f s m = m >>= foldM f s
end

module SampleM = struct
  (* Monad for sampling using using implicit global state.
   * A computation in this monad is a thunk which may return None if the
   * sampling fails or Some x if it succeeds. 
   *)
  type 'a m = unit -> 'a option

  open List
  let fail = const None
  let return x = fun () -> Some x
  let bind m f = fun () -> match m () with | None -> None | Some x -> f x ()
  let choice xs = if xs=[] then fail else fun () -> Some (Dist.sample xs)
end

module SampleEM = struct
  (* Monad for sampling using using implicit global state.
   * A computation in this monad is a thunk which may throw an exception if the
   * sampling fails or x if it succeeds. 
   *)
  type 'a m = unit -> 'a
  exception Failure

  open List
  let fail () = raise Failure
  let return x = fun () -> x
  let bind m f = fun () -> f (m ()) ()
  let choice xs = if xs=[] then fail else fun () -> Dist.sample xs
end

module DistM = struct
  open Dist

  let return x = [one,x]
  let bind m f =
    let ext (w,x) = map_weights (mul w) (f x) in 
    List.concat (List.map ext m)
  let choice xs = xs
  let fail = []
end

(* confusingly, these are NOT of type MONAD *)
module ContM = struct
  type ('w,'a) m = {run: ('a -> 'w) -> 'w}

  let return x  = {run = fun k -> k x}
  let (>>=) m f = {run = fun k -> m.run (fun x -> (f x).run k)}
  let (>>) f g  = f >>= fun _ -> g
  let shift f   = {run = fun k -> (f (return ** k)).run id} 
  let reset f   = return (f.run id)
end

module ContT (W : sig type t end) (B : MONAD) = struct
  type w = W.t
  type 'a m = {run: ('a -> w B.m) -> w B.m}

  let return x  = {run = fun k -> k x}
  let (>>=) m f = {run = fun k -> m.run (fun x -> (f x).run k)}
  let (>>) f g  = f >>= fun _ -> g
  let shift f   = {run = fun k -> (f (return ** k)).run id} 
  let abort x   = {run = fun k -> x}
  let lift m    = {run = fun k -> B.bind m k}
end

(* alternative?
module ContM (W : TYPE) = struct
  type w = W.t

  type 'a m = ('a -> w) -> w 

  let return x k = k x 
  let bind m f k = m (fun x -> f x k) 
  let callcc f k = f (fun x _ -> k x) k 
  let run m = m
end
*)

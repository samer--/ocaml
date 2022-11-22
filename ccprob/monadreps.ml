open Monads
open Utils

(* Direct representation of monads using delimited continuations, as described
 * by Filinski [1], but implemented using Kiselyov's Delimcc library. 
 *
 * [1] A. Filinski. Representing layered monads. In Proceedings of the 26th ACM
 *     SIGPLAN-SIGACT symposium on Principles of programming languages, pages
 *     175--188. ACM, 1999.
 *)

module Direct (M : MONAD) : sig
  type 'a m = 'a M.m
  type w (* answer type *)

  val reflect : 'a m -> 'a 
  val abort : w m -> 'a
  val reify : (unit -> 'a) -> 'a m
end = struct
  open Dynamic
  open Delimcc

  type 'a m = 'a M.m
  type w = dyn (* functions as universal type *)
  
  let p = new_prompt ()
  let reflect m = shift0 p (M.bind m)
  let reify f = 
    let (ind,outd) = newdyn () in 
    let ret x = M.return (outd x) in
    M.bind (push_prompt p (fun () -> M.return (ind (f ())))) ret 
  let abort m = Delimcc.abort p m
end


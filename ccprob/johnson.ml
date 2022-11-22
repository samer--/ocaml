(** Trying out ideas from Johnson 1995:
  
     M. Johnson. Memoization in top-down parsing. Computational Linguistics, 21(3):405--417, 1995.

   This paper shows how to do memoisation with parser combinators in Lisp, using
   mutable variables. My O'Caml translation uses references to acheive the same effect.
   However, because of O'Caml's immutable let bindings, I had to implement my own
   fix-point combinator. This is quite good in a way, because it means that all
   I need to implement for each memoising approach is a [memoinc] function, an
   imcomplete recursive function as described by Bruce McAdam:

     B. J. Mcadam. That about wraps it up---using fix to handle errors without exceptions, 
     and other programming tricks.  Technical report, Laboratory for Foundations of Computer Science, 
     The University of Edinburgh, 1997.

   I implemented Johnson's left recursion handling by using Oleg Kiselyov's delimcc library to 
   replace Johnson's explicit continuation passing style.

   I'm also trying monadic implementations of the above.

   Non-left recursive, deterministic:

     State: MONADREF vs O'Caml refs
     Interface: monadic vs direct

     ( ref, direct  ) = RefMemo
     ( st,  monadic ) = StateMemoM

   Left-recursive:

     State: MONADREF vs O'Caml refs
     Nondet: List vs Arbitrary
     Cont:  ContT vs Delimcc
     Interface: monadic vs direct

     ( st,  list, cont,    monadic ) = ContMemoM, ContMemoTableM
     ( ref, list, delimcc, direct  ) = [will be fastest!]

     ( st,  arb,  delimcc, direct  ) = ContNondetStateMemo
     ( ref, arb,  delimcc, direct  ) = ContNondetMemo


   ( ref, none, 
   @author Samer Abdallah
 *)

open Utils
open Monads
open Store
open Treemonads
open Monadst

module ST = StoreRef (StateM) (* Provide mutable refs using state monad to manage store *)

(** Fixed point combinator. 
  To understand recursion and fixed point combinators, we have to establish the
  idea of an `incomplete' recursive function. This should define the recursive
  function normal way, but instead of calling itself directly, it should call a
  function which is passed as its first parameter, which will represent the
  desired recursive function. For example if we want to define a function
  f : 'a -> 'b, we should instead write a function 
  {[ f_inc : ('a -> 'b) -> 'a -> 'b ]}
  The first parameter to this function will be the desired recursive function
  [f].  [f_inc f x] should compute the value of [f x], calling the passed in 
  function [f] whenever a recursive call is needed. This means that [f_inc] is not
  itself a recursive function, [f = fix f_inc] will be the desired recursive
  function.
*)
let fix f = let rec p x = f p x in p

(** Dyadic fixed point combinator for mutually recursive functions. 
 *  To implement two mutually recursive functions, we elaborate the idea of an
 *  incomplete function to {e two} incomplete functions, whose first parameter
 *  will be a {e pair} of functions to be used for recursive calls to either
 *  of the mutually recursive pair. This could be extended to arbitrary numbers
 *  of mutually recursive functions but I won't bother with that here. *)
let fix2 (f,g) =
  let rec fp x = f (fp,gp) x
  and     gp x = g (fp,gp) x
  in (fp,gp)


(** Incomplete function wrapper to add tracing messages.
 * This takes any incomplete recursive function and returns a new incomplete
 * recursive function which computes the same thing but prints a message
 * whenever it is called. 
 *
 * @param to_string This function should format the parameter to the recursive
 *                  function as a string.
 * @param name      An arbitrary name for labelling messages from this function.
 * @param f         The original incomplete function.
 *)
let trace to_string name f comp x = 
  Printf.printf "evaluating: %s %s\n" name (to_string x);
  f comp x

let trace2 to_string name f comp x = 
  Printf.printf "evaluating: %s %s\n" name (to_string x);
  let y = f comp x in
  Printf.printf "result: %s %s = %s\n" name (to_string x) (to_string y);
  y
(**** MEMO utilities *****)

(** A module type for modules that provide memoisation as a computational
 *  effect. *) 
module type MEMO = sig
  (** An incomplete function transformer which takes an incomplete recursive
   * function and returns a new one which maintains a memo table and checks
   * it before each call to prevent repeated calls with the same parameter. *)
  val memoinc : ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
end

(** A module type for monads that provide memoisation as a monadic effect. *)
module type MONADMEMO = sig
  include MONAD
  (** A monadic computation that an incomplete recursive
   * monadic computation and returns a new one which maintains a memo table and checks
   * it before each call to prevent repeated calls with the same parameter. The
   * computations required to manage the memo table are expected to be monadic
   * and therefore pure and side-effect free. *)
  val memoinc : ('a -> 'b -> 'c m) -> ('a -> 'b -> 'c m) m
end

module type MONADMEMOTABLE = sig
  include MONAD
  module C : MONAD

  type ('a,'b) table
  val memoinc : ('c -> 'a -> 'b C.m) -> (('c -> 'a -> 'b C.m) * ('a,'b) table m) m
  val runC : 'b C.m -> 'b m
end

(** Given a module that provides memoisation as a computational effect, this
 * module provides some memoising fixed point combinators. *)
module MemoOps (M : MEMO) = struct
  let memo f = (M.memoinc (fun () x -> f x)) ()
  let memorec f = fix (M.memoinc f)
  let memorec2 (f,g)  = fix2 (M.memoinc f, M.memoinc g)
end

(** Given a monad that provides memoisation, this
 * module provides some monadic combinators that produce a memoising fixed-point
 * from an incomplete recursive monadic computation. *)
module MemoMonadOps (M : MONADMEMO) = struct
  include MonadOps(M)
  let memo f = M.memoinc (fun () x -> f x) >>= fun finc -> M.return (finc ())
  let memorec f = liftM fix (M.memoinc f)
  let memorec2 (f,g)  = liftM2 (curry fix2) (M.memoinc f) (M.memoinc g)
end


(** Basic memoiser using mutable state.
 * Simply uses an ordinary O'Caml reference to manage a memo table, which is
 * implemented using the polymorphic map modules from O'Caml with Batteries.
 * Thus, both [RefMemo.memoinc] {e and} the function it produces have
 * side-effects. *)
module RefMemo = struct
  let memoinc f = 
    let loc = ref BatMap.empty in
    fun comp x -> try BatMap.find x !loc
                  with Not_found -> let v = f comp x in
                                    loc := BatMap.add x v !loc; v
end


(* Monadic memoisation using arbitrary state monad 
 * From the outside it looks like a basic monad, but the monadic type is visible
 * as that of a MONADSTATE over stores.
 *)

(** Module for a monad which provides memoisation *)
module StateMemoM : MONADMEMO with type 'a m = 'a ST.m = struct
  module SO = MonadOps (ST)
  open SO
  open ST

  type 'a m = 'a ST.m
  let return = ST.return
  let bind = ST.bind

  (* memoinc :  ('a -> 'b -> 'c m) -> ('a -> 'b -> 'c m) m *)
  let memoinc f_inc =
    new_ref BatMap.empty >>= fun loc ->
    return (fun comp x ->
      get_ref loc >>= fun tab ->
          try return (BatMap.find x tab) 
          with Not_found -> 
            f_inc comp x >>= fun v ->
            upd_ref loc (BatMap.add x v) >> return v)
end



(** Memoisation of nondeterministic computation in a direct (not monadic)
 * style. Nondeterministic computation may be left-recursive as long as
 * there is an alternative branch that avoids immediate recursion.
 *
 * This was adapted from Johnson's CPS implementation. By using Delimcc,
 * I don't need to go into explicit continuation passing style, but
 * just use [shift] to implement nondetermism ([fail] and [alt]) and
 * the memoised incomplete function returned by [memoinc].
 * 
 * Once the continuation is captured, non-determinism is implemented
 * used an arbitrary instance of [MONADPLUS]. The memo tables are
 * managed using ordinary O'Caml references.
 *)

module ContNondetMemo (M : MONADPLUS) : sig
  val run  : (unit -> 'a) -> 'a M.m
  val fail : unit -> 'a
  val alt  : 'a -> 'a -> 'a
  val memoinc : ('c -> 'a -> 'b) -> 'c -> 'a -> 'b
end= struct
  type ('a,'b) entry = Entry of ('a list * ('a->'b) list)

  module MO = MonadOps(M)
  open Delimcc
  open Dynamic
  open MO

  let pr = new_prompt ()

  let fail () = shift pr (fun k -> M.mzero ())
  let alt x y = shift pr (fun k -> M.mplus (k x) (k y))

  let run f = 
    let (ind,outd) = newdyn () in
    fmap outd (push_prompt pr (M.return ** ind ** f))
    (* M.bind (push_prompt pr (fun () -> M.return (ind (f ())))) *) 
           (* (M.return ** outd) *)
           (* (fun x -> M.return (outd x)) *)
    (* MO.fmap outd (push_prompt pr (fun () -> M.return (ind (f ())))) *) 

  let memoinc finc =
    let loc = ref BatMap.empty in
    fun p x ->
      shift pr (fun k ->
        let table = !loc in
        try let Entry (res,conts) = BatMap.find x table in
            loc := BatMap.add x (Entry (res,k::conts)) table; (* update continuations list *)
            List.fold_left (fun s x -> M.mplus (k x) s) (M.mzero ()) res (* map k over results and mconcat them *)
        with Not_found -> (* first call *) (
          loc := BatMap.add x (Entry ([],[k])) table; (* initialise entry *)
          let y = finc p x in 
          let table' = !loc in
          let Entry (res,conts) = BatMap.find x table' in
          if (List.mem y res) then M.mzero () else (
            loc := BatMap.add x (Entry (y::res,conts)) table'; (* update results table *)
            List.fold_left (fun s k -> M.mplus (k y) s) (M.mzero ()) conts 
          ) 
        )
      )
end


(** Memoisation in direct style using delimited continuation, abitrary * monad transformer 
 * for nondeterminism over a base state monad for memo tables *)

module ContNondetStateMemo (NDT : MONADPLUST) = struct
  module M = NDT (ST)
  module MO = MonadOps (M)
  type ('a,'b) entry = Entry of ('a list * ('a->'b) list)
  type 'a nondet = 'a M.m

  open Delimcc
  open Dynamic
  open M
  open MO
  open Printf

  let pr = new_prompt ()

  (* return monadic form of direct style computation *)
  let run f = 
    let (ind,outd) = newdyn () in
    fmap outd (push_prompt pr (return ** ind ** f ))

  (* direct style API for nondeterminism *)
  let fail () = abort pr (mzero ())
  let alt x y = shift pr (printf "about to call shift\n"; (fun k -> (let sum = mplus (printf "applying k to 1st alt\n"; (k x)) 
                                                                                     (printf "applying k to 2nd alt\n"; (k y))
                                                                     in printf "returning monadic sum\n"; sum)))

  let trf f x = print_endline "resuming suspended StateM"; f x
  (* let reflectS m = shift pr (fun k -> ST.bind m k) *)
  let reflectS m = shift pr (fun k -> M.lift m >>= k)
  let ref x = reflectS (ST.new_ref x)
  let ( ! )  l = reflectS (ST.get_ref l)
  let ( := ) l x = reflectS (ST.put_ref l x)

  let memoinc finc = 
    let loc = ref BatMap.empty in
    (fun p x -> 
      shift pr (fun k -> 
        let _ = printf "in memoised function\n" in  
        let table = !loc in
        try let Entry (res,conts) = BatMap.find x table in
            let _ = printf "new consumer (previously %d)\n" (List.length conts) in
            loc := (BatMap.add x (Entry (res,k::conts)) table); (* update continuations list *)
            printf "sending %d values to new consumer\n" (List.length res);
            List.fold_left (fun s x -> M.mplus (let _ = printf "calling consumer continuation\n" in k x) s) (M.mzero ()) res
        with Not_found -> (* first call *) (
          let _ = printf "new producer\n" in 
          loc := (BatMap.add x (Entry ([],[k])) table); (* initialise entry *)
          let y = finc p x in 
          let _ = printf "producer got new value\n" in 
          let table' = !loc in
          let Entry (res,conts) = BatMap.find x table' in
          if (List.mem y res) then (let _ = printf "already got value\n" in M.mzero ()) else (
            let _ = printf "sending to consumers %d\n" (List.length conts) in 
            loc := (BatMap.add x (Entry (y::res,conts)) table'); (* update results table *)
            List.fold_left (fun s k -> M.mplus (let _ = printf "producer sending to consumer\n" in k y) s) (M.mzero ()) conts 
          ) 
        ) 
      )
    )
end

(* purely monadic implementation of continuation passing memoising nondet monad *)
module ContMemoM (NDT : MONADPLUST) : sig
  type 'a m

  val memoinc: ('a -> 'b -> 'c m) -> ('a -> 'b -> 'c m) m
  val return : 'a -> 'a m
  val bind   : 'a m -> ('a -> 'b m) -> 'b m
  val mzero  : unit -> 'a m
  val mplus  : 'a m -> 'a m -> 'a m
  val run    : 'a m -> 'a NDT(ST).m

end = struct
  module ND = NDT (ST)
  module CC = ContT (struct type t = Dynamic.dyn end) (ND) 
  open   CC

  (* type 'a m = (Dynamic.dyn, 'a) CC.m *)
  type 'a m = 'a CC.m

  let run m =
    let (ind,outd) = Dynamic.newdyn () in
    ND.bind (m.run (ND.return ** ind)) (ND.return ** outd)

  let return    = CC.return  
  let bind      = CC.(>>=) 
  let liftST m  = CC.lift (ND.lift m)
  let mzero ()  = {run = fun k -> ND.mzero ()}
  let mplus f g = {run = fun k -> ND.mplus (f.run k) (g.run k)}
  let msum      = List.fold_left mplus (mzero ()) 

  let memoinc finc = 
    liftST (ST.new_ref BatMap.empty) >>= (fun loc ->
    let upd_entry x entry table = liftST (ST.put_ref loc (BatMap.add x entry table)) in
    return (fun p x -> 
      liftST (ST.get_ref loc) >>= fun table ->
      try let (res,conts) = BatMap.find x table in 
        shift (fun k -> upd_entry x (res,k::conts) table >> 
                        msum (List.map k res))
      with Not_found -> 
        shift (fun k -> upd_entry x ([],[k]) table >> 
                        finc p x >>= fun y ->
                        liftST (ST.get_ref loc) >>= fun table' ->
                        let (res,conts) = BatMap.find x table' in
                        if List.mem y res then mzero ()
                        else upd_entry x (y::res,conts) table' >>
                             msum (List.map (fun k -> k y) conts))))
end


module ContMemoTableM : sig
  include MONAD with type 'a m = 'a ST.m
  module CC : MONADPLUS

  type ('a,'b) table = ('a * 'b list) list
  val memoinc : ('a -> 'b -> 'c CC.m) -> (('b,'c) table m * ('a -> 'b -> 'c CC.m)) ST.m
  val run : 'a CC.m -> 'a list m

end= struct
  module  ND  = ListT (ST)
  module  Set = BatSet
  module  Map = BatMap
  open    Dynamic
  include ST

  type ('a,'b) table = ('a * 'b list) list

  module CC = struct
    type ans = dyn ND.m
    type 'a m = ('a -> ans) -> ans

    let return x k = k x  
    let bind m f k = m (fun x -> f x k) 

    let mzero () _ = ND.mzero ()  
    let mplus f g k = ND.mplus (f k) (g k) 

    let liftST m = ND.bind (ND.lift m)
    let new_ref x = liftST (ST.new_ref x)
    let get_ref loc = liftST (ST.get_ref loc)
    let put_ref loc x = liftST (ST.put_ref loc x)

    let shift e k = e (fun x k' -> k' (k x)) id
  end

  let run m =
    let (ind,outd) = newdyn () in
    ND.bind (m (ND.return ** ind)) (ND.return ** outd)
        
  let memoinc finc = 
    bind (new_ref Map.empty) (fun loc ->
    let get_table = 
      let sanitize (x,(s,_)) = (x, Set.fold cons s []) in
      bind (get_ref loc) (return ** List.map sanitize ** Map.bindings) in

    return (get_table, fun p x -> 
      let module MO = MonadOps(CC) in
      let open CC in 
      let open MO in

      get_ref loc >>= fun table ->
      let update x e t = put_ref loc (Map.add x e t) in
      try let (ys,ks) = Map.find x table in 
        shift (fun k -> update x (ys, k::ks) table >> 
                        Set.fold (mplus ** k) ys (mzero ()))
      with Not_found -> 
        shift (fun k -> update x (Set.empty, [k]) table >> 
                        finc p x >>= fun y ->
                        get_ref loc >>= fun t ->
                        let (ys,ks) = Map.find x t in
                        if Set.mem y ys then mzero ()
                        else update x (Set.add y ys, ks) t >>
                             List.fold_left (fun l k -> mplus (k y) l) 
                                            (mzero ()) ks)))
end
(***** PARSING *****)

module Parse1 (Token : SHOW) = struct
  type t = Token.t
  type s = t list (* type of parser state *)
  type 'a m = 'a ListM.m (* non-determinism monad *)


  (* term : t -> s -> s m *)
  let term x = function
    | y :: ys when x=y -> [ys]
    | otherwise -> []

  let seq f g s = ListM.bind (f s) g
  let alt f g s = ListM.mplus (f s) (g s)
  let epsilon s = ListM.return s

  let ( || ) = alt
  let ( >> ) = seq
  let opt f     = epsilon || f
  let rec star f    = epsilon || f >> star f
end

module Parse2 (Token : SHOW) = struct
  type t = Token.t
  type s = t list (* type of parser state *)

  module M = StateT (struct type t = Token.t list end) (ListM)
  module MO = MonadOps (M)
  open M
  open MO

  let mzero () = M.lift (ListM.mzero ())
  let mplus f g s = ListM.mplus (f s) (g s)

  let term x = 
    get >>= (function
             | y::ys when x=y -> put ys >> return ()
             | _ -> mzero ())

  let epsilon = return ()

  let ( || ) = mplus
  let ( >> ) = MO.( >> )
  let opt f  = epsilon || f
  let rec star f    = epsilon || f >> star f
end

module Parse3 (Token : SHOW) = struct
  type t = Token.t
  type s = t list (* type of parser state *)

  module LS = ListT (StateM (struct type t = int end))
  module SLS = StateT (struct type t = Token.t list end) (LS)
  module MO = MonadOps (SLS)
  open SLS
  open MO

  let mzero () = SLS.lift (LS.mzero ())
  let mplus f g s = LS.mplus (f s) (g s)

  let term x = get >>= (function
                        | y::ys when x=y -> put ys >> return ()
                        | _ -> mzero ())

  let epsilon = return ()

  let ( || ) = mplus
  let ( >> ) = MO.( >> )
  let opt f  = epsilon || f
  let rec star f    = epsilon || f >> star f
end

(* Parsing using State monad on top of direct style nondet + memoing *)
module Parse4 (Token : SHOW) = struct
  type t = Token.t
  type s = t list (* type of parser state *)

  module NCM = ContNondetMemo (TreeM)
  module M = StateM (struct type t = Token.t list end) 
  module MO = MonadOps (M)
  include MemoOps (NCM)
  open NCM
  open M
  open MO

  let mzero () s = fail ()
  let mplus f g s = (alt f g) s

  let term x = 
    get >>= (function
             | y::ys when x=y -> put ys >> return ()
             | _ -> mzero ())

  let epsilon = return ()

  let memoinc = NCM.memoinc
  let run = NCM.run
  let ( >> ) = MO.( >> )
  let ( || ) = mplus
  let opt f  = epsilon || f
  let rec star f    = epsilon || f >> star f

  let run = NCM.run 
end


(* state T on ContMemoM for nondet and memoing *)
module Parse5 (Token : SHOW) = struct
  type t = Token.t
  type s = t list (* type of parser state *)

  module ContMemoM = ContMemoM (ListT)
  module SLS = StateT (struct type t = Token.t list end) (ContMemoM)
  module MO = MonadOps (SLS)
  module MMO = MemoMonadOps (ContMemoM)
  include MMO
  open SLS
  open MO

  let return = ContMemoM.return
  let mzero () = SLS.lift (ContMemoM.mzero ())
  let mplus f g s = ContMemoM.mplus (f s) (g s)

  let term x = get >>= (function
                        | y::ys when x=y -> put ys >> SLS.return ()
                        | _ -> mzero ())

  let epsilon = SLS.return ()

  let ( || ) = mplus
  let ( >> ) = MO.( >> )
  let opt f  = epsilon || f
  let rec star f    = epsilon || f >> star f

  let parse cat x = ContMemoM.run (ContMemoM.bind cat (fun s -> s x))
end

(******** TESTING *******)

(* from Hafiz and Frost
 
 1. s    = term `x` *> s *> s <+> empty
 2. sm   = memoize SM $ term `x` *> sm *> sm <+> empty
 3. sml  = memoize SML $ sml *> sml *> term `x` <+> empty
 4. smml = memoize SMML $ smml *> (memoize SMML` $ smml *> term `x`) <+> empty

 Input length No. of parses    s     sm     sml     smml
 -------------------------------------------------------
   6                 132      1.22    -      -       -
   12            208,012       *      -      -      0.02
   24          1.289e+12       *     0.08   0.13    0.06
   48          1.313e+26       *     0.83   0.97    0.80
*)

(** ordinary incomplete Fibonacci function *)
let fib_inc fib' = function
  | 0 -> 0
  | 1 -> 1
  | n -> fib' (n-1) + fib' (n-2)

(** functor for monadic Fibonacci function *)
module MonadicFib (M : MONAD) = struct
  module MO = MonadOps(M)
  open MO

  (* fib_inc_m : (int -> int m) -> (int -> int m) *)
  let fib_inc_m fib' = function
    | 0 -> M.return 0
    | 1 -> M.return 1
    | n -> liftM2 (+) (fib' (n-1)) (fib' (n-2))
end

module RecTest = struct
  module ContMemoM = ContMemoM (ListT)
  module ND = ContMemoM
  include MonadicFib (ContMemoM)
  include MonadOps(ND)
  include MemoMonadOps(ND)
  include ND

  let ( || ) = mplus

  (* link : 'a -> 'a m *)
  let link = function
             | 'a' -> return 'b'
             | 'b' -> return 'c' || return 'd'
             | 'c' -> return 'd'
             | 'e' -> return 'c'
             | _   -> mzero () 

  (* recursive functions : 'a -> 'a m *)
  let rec path x = link x || (path x >>= path) 
  let rec path' x = (return x || path' x) >>= link 
  let rec path'' x = link x >>= (fun y -> return y || path'' y)

  (* incomplete functions : ('a -> 'a m) -> 'a -> 'a m *)
  let path_inc p x = link x || (p x >>= p) 
  let flaz_inc p x = p x || (p x || if x=5 then return x else mzero ())

  let test f x = run (memorec f >>= apply_to x)
  let fib = test fib_inc_m

  let step i = return 1 || return (i+1)
  let rec stepN p = function | 0 -> return 0
                             | n -> p (n-1) >>= step
  let dups d = function | 0 -> return 1 
                        | n -> (return 1 || return 1) >> d (n-1)

end

module type NONDETMEMO = sig
  include MEMO
  type 'a nondet

  val alt : 'a -> 'a -> 'a
  val fail: unit -> 'a
  val run : (unit -> 'a) -> 'a nondet
end

module Path (M : NONDETMEMO) = struct
  open M
  open Printf

  let trv l v = printf "%s: %c\n" l v; v
  let trf l f x = printf "CALL: %s %c\n" l x;
                  let y = f x in
                  printf "RET: %s %c = %c\n" l x y;
                  y

  let ( || ) = alt
  let ( ||| ) f g = alt f g ()

  let link = function
             | 'a' -> 'b'
             | 'b' -> 'c' || 'd'
             | 'c' -> 'd'
             | 'e' -> 'c'
             | 'd' -> 'a'
             | 'f' -> 'g' || 'h'
             | 'g' -> 'i' || 'j'
             | 'i' -> 'j'
             | _ -> fail () 

  (* this is rather nice, I think *)
  let path_r1 p = (p || id) ** link
  let path_r  p = (id || p) ** link
  let path_l  p = link ** (id || p) 
  let path_lr p = link || p ** p  

  (* check distribution of ** over || *)
  let path_r'  p = trf "branch" (trf "link1" link || trf "recp" p ** trf "link2" link)
  let path_l'  p = trf "branch" (trf "link1" link || trf "link2" link ** trf "recp" p)
  let path_r'' p = p ** link || link

  (* bad - branches of || are evaluated eagerly before any value is returned,
   * unlike above, where branches of || are functions waiting to be applied *)
  let path_l_inc p x = link (trv "alt val" (x || (trf "reccall" p) (trv "recval" x))) (*(x || p x) *)
  let path_lr_inc' p x = p (p x) || link x
  let path_lr_inc p x = link x || p (p x) 
end

module TestContNondetMemo = struct
  module CNM = ContNondetMemo (ListM)
  module MO = MemoOps (CNM)
  include CNM
  include MO

  let ( || ) = alt
  let link = function
             | 'a' -> 'b'
             | 'b' -> 'c' || 'd'
             | 'c' -> 'd'
             | 'e' -> 'c'
             | 'd' -> 'a'
             | _ -> fail () 

  (* this is rather nice, I think *)
  let path_r  p = (id || p) ** link
  let path_l  p = link ** (id || p) 
  let path_lr p = link || p ** p  

  (* check distribution of ** over || *)
  let path_r'  p = link || p ** link
  let path_l'  p = link || link ** p 

  (* these result in deadlock as we have to call p recursively immediately.
   * Since we are not lazy, there is no way to defer the call until we actually
   * need the result, so even if there is an alternative which does not need
   * the value of [p x], the memoised call gets stuck waiting for itself to 
   * produce a value.

    let path_l_inc p x = link (x || p x) 
    let path_lr_inc' p x = p (p x) || link x
    let path_lr_inc p x = link x || p (p x) 
  *) 

  let test f x = run (fun () -> f x)
  let fib n = run (fun () -> let fib = memorec fib_inc in fib n)
end


module TestParse4 = struct
  module PString = Parse4 (STRING)
  open PString

  let tr = trace string_of_list

  let parse x =
    run (fun () -> 
      let v  = term "likes" || term "knows" in
      let det = term "every" || term "a" || term "the" || term "no" in
      let n = memorec (fun n -> term "fat" >> n || term "student" || term "professor" || term "fish") in
      let pn = term "Kim" || term "Sandy" in
      let np = memorec (fun np -> pn 
                               || term "fat" >> np 
                               || np >> term "with fries" 
                               || det >> n 
                               || term "fish") in
      let (vp,s) = 
        fix2 ( 
          tr "mem-vp" (memoinc (tr "vp" (fun (vp,s) -> v >> (np || s)))), 
          tr "mem-s" (memoinc (tr "s" (fun (vp,s) -> np >> vp)))
        ) in
      s x)
end

module TestParse5 = struct
  module PString = Parse5 (STRING)
  open PString

  let test x = parse ( 
    let v  = term "likes" || term "knows" in
    let det = term "every" || term "a" || term "the" || term "no" in
    let pn = term "Kim" || term "Sandy" in
    memorec (fun n -> term "fat" >> n  
                   || term "student" 
                   || term "professor" 
                   || term "fish") >>= fun n ->
    memorec (fun np -> pn 
                    || term "fat" >> np 
                    || np >> term "with fries" 
                    || det >> n 
                    || term "fish") >>= fun np ->
    memorec2 ( (fun (vp,s) -> v >> (np || s)),
               (fun (vp,s) -> np >> vp)) >>= fun (_,s) ->
    return s
    ) x
end

module TestStateMemo = struct
  module SMM = StateMemoM     (* memo monad using store states *)
  include MemoMonadOps (SMM)  (* monad and memo ops for memo monad *)
  include MonadicFib (SMM)
  open SMM

  let run m = fst (m Store.empty)
  let test_fib x = run (memorec fib_inc_m >>= apply_to x)
end

module SetM = struct
  module S = BatSet
  type 'a m = Ord of 'a S.t | Any of 'a list

  let list_of_m = function
    | Ord set -> S.fold cons set []
    | Any lst -> lst

  let set_of_m = function
    | Ord set -> set
    | Any lst -> S.of_list lst

  let rec collect = function
    | [] -> Any []
    | [x] -> x
    | (m::ms) -> match m with
                 | Ord set -> Ord (S.union set (set_of_m (collect ms)))
                 | Any xs  -> match collect ms with
                              | Ord ss -> Ord (S.union ss (S.of_list xs))
                              | Any ys -> Any (xs @ ys)

  let return x = Any [x]
  let bind m f = collect (List.map f (list_of_m m))
  let mzero () = Any []
  let mplus m n = match m,n with
    | Any xs, Any ys -> Any (xs @ ys)
    | Ord xs, Any ys -> Ord (S.union xs (S.of_list ys))
    | Any ys, Ord xs -> Ord (S.union xs (S.of_list ys))
    | Ord ys, Ord xs -> Ord (S.union ys xs)

  let choose xs = Ord (S.of_list xs)

  let run = list_of_m
end

module NDListM = struct
  include ListM

  let choose xs = xs
end

module TestWalk (ND : sig include MONAD val choose : 'a list -> 'a m end)= struct
  include MonadOps (ND)
  open ND

  let step i = choose [i;i+1]
  let rec stepN = function | 0 -> return 0
                           | n -> stepN (n-1) >>= step
  let rec dups = function | 0 -> return 1 
                          | n -> choose [1;1] >> dups (n-1)

  let ptriang m =
    let triang n = n*(n+1)/2 in
    choose (1--m) >>= fun k ->
    choose (1--k) >>= fun i ->
    choose (1--i) >>= fun j ->
      if triang i + triang j = triang k then return k else choose []

  let pythag m =
    choose (0--m) >>= fun i ->
    choose (0--m) >>= fun j ->
    choose (0--m) >>= fun k ->
      if i*i + j*j = k*k then return (i,j,k) else choose []


end                       

module TransClose (M : MONADPLUS) : sig
  val link : char -> char M.m
  val path : (char -> char M.m) -> char -> char M.m
end = struct
  module MO = MonadOps(M)
  open MO
  open M

  let ( || ) = mplus
  let link = function
             | 'a' -> return 'b'
             | 'b' -> return 'c' || return 'd'
             | 'c' -> return 'd'
             | 'e' -> return 'c'
             | _   -> mzero () 

  let path p x = link x || (p x >>= p) 
end

module RecTest2 = struct
  module CM = ContMemoTableM
  include MonadicFib (CM.CC)
  include TransClose (CM.CC)
  include MonadOps (CM)
  include CM

  let memorec f = memoinc f >>= return ** fix ** snd
  let memo2 (f,g) = liftM2 Pair.pair (memorec f) (memorec g)

  let test finc g  = ST.run (
    memoinc finc >>= fun (get_table,mf) -> 
    run (g (fix mf)) >>= fun res -> 
    get_table >>= fun tab -> 
    return (res,tab))
end

module RecTest3 = struct
  module CMSN = ContNondetStateMemo (TreeT)
  module PP = Path (CMSN)
  module MO = MemoOps (CMSN)

  let flatten mt = CMSN.M.fold (fun l x -> ST.return (x::l)) [] mt
  let test f x = (fun () -> (MO.memorec (trace CHAR.show "path" f)) x) |> CMSN.run |> flatten
end

let main args = 
  let _ = RecTest3.(test PP.path_r 'f') |> ST.run
  in ()

let _ = if not !Sys.interactive then main Sys.argv else ()

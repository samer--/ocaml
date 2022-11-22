(* This module contains lots of implementations of the Prob.PROB signature
 *
 * Make         : Double Direct on state and arbitrary PROBMONAD
 * MakeST       : Direct on StateT with arbitrary PROBMONAD
 * ProbTree     : Delimcc with Direct  for state 
 * ProbTreeST   : Delimcc with expanded StateT (WTreeAltM) (mem ops -> shift)
 * ProbTreeRef  : Delimcc with expanded StateT (WTreeAltM) and synchronised mutable store
 * ProbTreeRef1 : Delimcc with expanded WTreeAltM and mutable store only
 * ProbTreeRef2 : Like ProbTreeRef1 but abandoning internal monadic structure (like Hansei)
 * MakeRef      : Direct on modified expanded StateT (M) with synchronised mutable store   
 * MakeRef1     : Delimcc on M with mutable store only
 * MakeRef2     : Direct on modified M with mutable store only
 *)
open Utils
open Monads
open Store
open Dist
open Prob
open Treemonads

module NoMemo = struct
  type 'a var = unit
  exception NotSupported

  let memo _ = raise NotSupported
  let letlazy _ = raise NotSupported
  let letvar _ = raise NotSupported
  let force _ = raise NotSupported
  let constrain _ = raise NotSupported
end

(* Module to manage a reference to a store.  *)
module RefStore = struct
  let state = ref Store.empty

  let protect k x =
    let s0 = !state in
    let y = k x in
    state := s0; y

  (* Implementation of STATE signature *)
  type t = Store.t
  
  let get () = !state
  let put s  = state := s
  let upd f  = state := f !state
  let reflect f = let (x,s) = f !state in state := s; x
end

module Make (M : PROBMONAD) : PROB with type 'a m = 'a M.m = struct
  (* Implementation of stateful probabilistic effects using an an arbitrary 
   * probability monad and independent (but nested) state monad *) 
  open Monadreps

  module D = Direct(M)  (* direct representation of monad using Delimcc *)
  module S = State(Store)  (* direct representaiton of state monad *)
  include Memo (S)

  type 'a m = 'a D.m
  
  (* just plug one thing into another thing... *)
  let reflect = D.reflect
  let reify f = D.reify (fun () -> fst (S.reify f Store.empty))
  let dist xs = D.reflect (M.choice xs)
  let fail () = D.abort M.fail
end

module ImmediateProb : PROB with type 'a m = 'a thunk = struct
  type 'a m = 'a thunk

  exception Failure

  let fail () = raise Failure
  let dist d = Dist.sample d
  let reflect x = x ()
  let reify f = f

  include NoMemo
end

module ImmediateRef : PROB with type 'a m = 'a thunk = struct
  type 'a m = 'a thunk

  module S = RefStore
  include Memo (S)

  exception Failure

  let fail () = raise Failure
  let dist d = Dist.sample d
  let reflect x = x ()
  let reify f = S.protect (fun () -> S.put Store.empty; f ())
end

module MakeST (M : PROBMONAD) : PROB with type 'a m = 'a M.m = struct
  open Monadreps

  module S = StateT (Store) (M)
  module D = Direct(S)  

  type 'a m = 'a M.m
  
  let reflect m = D.reflect (S.lift m)
  let reify f = M.bind (D.reify f Store.empty) (M.return ** fst)
  let fail () = D.abort (S.lift M.fail)
  let dist xs = reflect (M.choice xs)

  include Memo (struct
      type t = Store.t

      let get () = D.reflect S.get
      let put s  = D.reflect (S.put s)
      let upd f  = D.reflect (S.upd f)
      let reflect m = D.reflect (M.return ** m)
    end)
end

module ProbTree : PROB with type 'a m = 'a WTreeAltM.m = struct
  (* Implementation of stateful probabilistic effects using an an arbitrary 
   * probability monad and an implicity key-value store. *)

  module S = State(Store)  (* direct representaiton of state monad *)
  include Memo (S)

  open Dynamic
  open Lazydata.WTreeAlt
  open Delimcc

  type 'a m = 'a tree 
  let p = new_prompt ()

  let reflect m = shift0 p (WTreeAltM.bind m)

  let reify f = 
    let (ind,outd) = newdyn () in 
    let run () = Leaf (ind (fst (S.reify f Store.empty))) in
    WTreeAltM.bind (push_prompt p run) (fun x -> Leaf (outd x)) 

  let dist xs = shift0 p (fun k -> Node (Dist.fmap (fun x () -> k x) xs))
  let fail () = abort p (Node [])

end

module ProbTreeST: PROB with type 'a m = 'a WTreeAltM.m= struct

  open Delimcc
  open Dynamic
  open Lazydata.WTreeAlt

  type 'a m = 'a tree

  let p = new_prompt ()

  let fail () = abort p (fun _ -> Node [])
  let reflect m = shift0 p (fun k s -> WTreeAltM.bind m (fun x -> k x s))
  let dist xs = shift0 p (fun k s -> Node (Dist.fmap (fun x () -> k x s) xs))
  let reify f = 
    let (ind,outd) = newdyn () in
    let st = push_prompt p (fun () -> let x = ind (f ()) in fun s -> Leaf (x,s)) in
    let res = st Store.empty in WTreeAltM.bind res (fun (x,_) -> Leaf (outd x))

  include Memo (struct
      type t = Store.t

      let get () = shift0 p (fun k s -> k s s)
      let put s  = shift0 p (fun k _ -> k () s)
      let upd f  = shift0 p (fun k s -> k () (f s))
      let reflect m = shift0 p (fun k s -> let (x,s') = m s in k x s')
    end)
end

module ProbTreeRef: PROB with type 'a m = 'a WTreeAltM.m = struct
  (* Implementation of stateful probabilistic effects using an an arbitrary 
   * probability monad and an implicity key-value store. 
   *
   * This is interesting. Step by step, I seem to be arriving at a solution
   * which is basically the same as Oleg's. The steps involve expanding the
   * Direct(StateT(WTreeAltM)) monad reprenentation and then introducing a
   * synchronisation between the monadic state and the global reference state at
   * key points, as well as protecting the existing contents of the global
   * reference when effectful computations are being made.
   *
   * The final optimisation would be to remove the monadic state all together,
   * which I suspect will give what Oleg has.
   *)

  open Delimcc
  open Dynamic
  open Lazydata.WTreeAlt

  type 'a m = 'a tree

  let p = new_prompt ()

  (* protects current contents of state from computation k x s *)
  module S = struct
    include RefStore

    let purify k s x =
      let s0 = !state in
      let y = state := s; k x s in
      state := s0; y
  end
  include Memo (S)

  let fail () = abort p (fun _ -> Node [])
  let reflect m = let s = S.get () in 
    shift0 p (fun k _ -> WTreeAltM.bind m (S.purify k s))
  let dist xs = let s = S.get () in 
    shift0 p (fun k _ -> Node (Dist.fmap (fun x () -> S.purify k s x) xs))

  let reify f = 
    let (ind,outd) = newdyn () in
    let st () = push_prompt p (fun () -> let x = ind (f ()) in fun _ -> Leaf (x,S.get ())) in
    WTreeAltM.bind (S.purify st Store.empty ()) (fun (x,_) -> Leaf (outd x)) 
end

module ProbTreeRef1: PROB with type 'a m = 'a WTreeAltM.m = struct
  (* This was obtained from ProbTreeRef after noticing that, though the basic
   * monadic type is store -> ('a,store) tree, the store argument to the
   * state transformer function is never used, and neither are the stores returned
   * in the leaves of the tree. Thus, the store argument  was systematically
   * removed, such the type of the prompt became just 'a tree. Hence, the type
   * of continuations is 'a -> 'b tree.
   *
   * This is the flattest implementation and will probably be fastest.
   *)

  open Delimcc
  open Dynamic
  open Lazydata.WTreeAlt

  type 'a m = 'a tree

  let p = new_prompt ()

  module S = struct
    include RefStore
    (* protects current contents of state from computation k x s *)
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  let fail () = abort p (Node [])
  let reflect m = let s = S.get () in 
    shift0 p (fun k -> WTreeAltM.bind m (S.purify s k))
  let dist xs = let s = S.get () in 
    shift0 p (fun k -> Node (Dist.fmap (fun x () -> S.purify s k x) xs))

  let reify f = 
    let (ind,outd) = newdyn () in
    let st () = push_prompt p (fun () -> Leaf (ind (f ()))) in
    WTreeAltM.bind (S.purify Store.empty st ()) (fun x -> Leaf (outd x))

  include Memo (S)
end


module ProbTreeRef2: PROB with type 'a m = 'a WTreeAltM.m = struct
  open Delimcc
  open Dynamic
  open Lazydata.WTreeAlt
  module M = WTreeAltM

  type 'a m = 'a tree
  
  let p = new_prompt ()

  module S = struct
    include RefStore
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  let fail () = abort p M.fail 

  let reflect m = let s = S.get () in 
    shift0 p (fun k -> M.bind m (S.purify s k))

  let dist xs = let s = S.get () in 
    shift0 p (fun k -> Node (Dist.fmap (fun x () -> S.purify s k x) xs))

  let reify f = 
    let ans = ref None in
    let st () = push_prompt p (fun () -> ans := Some (f ()); M.return ()) in
    M.bind (S.purify Store.empty st ()) (fun _ -> let Some x = !ans in M.return x)

  include Memo (S)
end

(* Next, I want to take the code in ProbTreeRef and ProbTreeRef1 and refactor it
 * to use Direct and WTreeAltM as much as possible.
 *)
module MakeRef (M : PROBMONAD) : PROB with type 'a m = 'a M.m = struct
  open Monadreps

  type 'a m = 'a M.m

  module S = struct
    include RefStore
    type 'a m = Store.t -> ('a * Store.t) M.m

    (* protects current contents of state from computation k x s *)
    let purify k (x,s) =
      let s0 = !state in
      let y = state := s; k x s in
      state := s0; y

    let return x s = M.return (x,s)
    let bind m f s = M.bind (m s) (purify f)
    let lift m s   = M.bind m (fun x -> M.return (x,s))
    let lifts m _  = let s = !state in M.bind m (fun x -> M.return (x,s))
  end
  module D = Direct(S)  
  include Memo (S)

  let reflect m = D.reflect (S.lifts m)
  let reify f = M.bind (S.purify (fun () -> D.reify f) ((), Store.empty)) (M.return ** fst)
  let fail () = D.abort (S.lift M.fail)
  let dist xs = reflect (M.choice xs)
end

(* Finally, lets get rid of the redundant state passing now *)

(* First using Delimcc directly *)
module MakeRef1 (M : PROBMONAD) : PROB with type 'a m = 'a M.m = struct
  open Delimcc
  open Dynamic

  module S = RefStore
  include Memo (S)

  type 'a m = 'a M.m

  let p = new_prompt ()

  let reify f = 
    let (ind,outd) = newdyn () in
    let st () = S.put Store.empty; push_prompt p (fun () -> M.return (ind (f ()))) in
    M.bind (S.protect st ()) (fun x -> M.return (outd x))

  let reflect m = let s = S.get () in 
    shift0 p (fun k -> M.bind m (S.protect (fun x -> S.put s; k x)))

  let fail () = abort p M.fail
  let dist xs = reflect (M.choice xs)
end

(* And now using Direct to hide Delimcc *)
module MakeRef2 (M : PROBMONAD) : PROB with type 'a m = 'a M.m = struct
  open Monadreps
  module S = struct
    include RefStore

    (* Implementation of MONAD signature *)
    type 'a m = 'a M.m
    let return = M.return 
    let bind m f = M.bind m (protect f) 
    let lifts m = let s = !state in M.bind m (fun x -> M.return (x,s))
  end
  include Memo (S)
  module D = Direct (S)

  type 'a m = 'a M.m

  let reify f = S.protect (fun () -> S.put Store.empty; D.reify f) () 
  let reflect m = let (x,s') = D.reflect (S.lifts m) in S.put s'; x
  let fail () = D.abort M.fail
  let dist xs = reflect (M.choice xs)
end

module VCM : Monads.PROBMONAD with type 'a m = 'a Ptypes.vc = struct
  open Ptypes

  type 'a m = 'a vc
  let return x = V x
  let rec extend f = function
    | V x -> f x
    | C tt -> C (fun () -> Dist.fmap (extend f)  (tt ()))

  let bind t f = extend f t
  let fail = C (const [])
  (* let choice xs = C (const (Dist.fmap return xs)) *)
  let choice xs = C (fun () -> Dist.fmap return xs)
end

module ProbVCRef1: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Dynamic
  open Ptypes
  module M = VCM

  type 'a m = 'a vc

  let p = new_prompt ()

  module S = struct
    include RefStore
    (* protects current contents of state from computation k x s *)
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  let fail () = abort p M.fail
  let reflect m = let s = S.get () in 
    shift0 p (fun k -> M.bind m (S.purify s k))
  let dist xs = let s = S.get () in 
    shift0 p (fun k -> C (fun () -> Dist.fmap (fun x -> S.purify s k x) xs))

  let reify f = 
    let (ind,outd) = newdyn () in
    let st () = push_prompt p (fun () -> V (ind (f ()))) in
    M.bind (S.purify Store.empty st ()) (fun x -> V (outd x))

  include Memo (S)
end


module ProbVCRef2: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Dynamic
  open Ptypes
  module M = VCM

  type 'a m = 'a vc

  type req= Done | More of req dist thunk
  let rfail = More (fun () -> [])
  let rec rextend (f : 'a -> req) = function
    | V x -> f x
    | C th -> More (fun () -> Dist.fmap (rextend f) (th ()))

  let p = new_prompt ()

  module S = struct
    (* include RefStore *)
    include RefStore
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  let fail () = abort p rfail
  let reflect m = let s = S.get () in 
    shift0 p (fun k -> rextend (S.purify s k) m)
  let dist xs = let s = S.get () in 
    shift0 p (fun k -> More (fun () -> Dist.fmap (S.purify s k) xs))

  let reify f = 
    let ans = ref None in
    let rec interp = function
      | Done -> let Some x = !ans in V x
      | More th -> C (fun () -> Dist.fmap interp (th ())) in
    let st () = push_prompt p (fun () -> ans := Some (f ()); Done) in
    interp (S.purify Store.empty st ()) 

  include Memo (S)
end

module ProbVCRef3: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Dynamic
  open Ptypes
  module M = VCM

  type 'a m = 'a vc

  type req= Done | More of req thunk dist
  let rfail = More []
  let rec rextend (f : 'a -> req) : 'a vc -> req = function
    | V x -> f x
    | C th -> More (Dist.fmap (fun t () -> rextend f t) (th ()))

  let p = new_prompt ()

  module S = struct
    include RefStore
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  let fail () = abort p rfail
  let reflect m = let s = S.get () in 
    shift0 p (fun k -> rextend (S.purify s k) m)
  let dist xs = let s = S.get () in 
    shift0 p (fun k -> More (Dist.fmap (fun x () -> S.purify s k x) xs))

  let reify f = 
    let ans = ref None in
    let rec interp = function
      | Done -> let Some x = !ans in V x
      | More ts -> C (fun () -> Dist.fmap (fun th -> interp (th ())) ts) in
    let st () = push_prompt p (fun () -> ans := Some (f ()); Done) in
    interp (S.purify Store.empty st ()) 

  include Memo (S)
end

module ProbVCRef4: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Ptypes
  module M = VCM

  type 'a m = 'a vc

  module S = struct
    include RefStore
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end

  type req= Done | More of req thunk dist
  let rec rextend (f : 'a -> req) : 'a vc -> req = function
    | V x -> f x
    | C th -> More (Dist.fmap (fun t () -> rextend f t) (th ()))

  let p = new_prompt ()

  let fail () = abort p (More [])
  let reflect m = let s = S.get () in 
    shift0 p (fun k -> rextend (S.purify s k) m)
  let dist xs = let s = S.get () in 
    shift0 p (fun k -> More (Dist.fmap (fun x () -> S.purify s k x) xs))

  let reify f = 
    let ans = ref None in
    let rec interp = function
      | Done -> let Some x = !ans in [1.0, V x]
      | More ts -> Dist.fmap (fun th -> C (fun () -> interp (th ()))) ts in
    let st () = push_prompt p (fun () -> ans := Some (f ()); Done) in
    match interp (S.purify Store.empty st ()) with
    | [_,V x] -> V x
    | ch -> C (const ch)

  include Memo (S)
end

module ProbVCRef6: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Ptypes
  module M = VCM

  type 'a m = 'a vc
  type req = Done |  More of req thunk dist
  let rec rextend (f : 'a -> req) : 'a vc -> req = function
    | V x -> f x
    | C th -> More (Dist.fmap (fun t () -> rextend f t) (th ()))

  module S = struct
    include RefStore
    let purify s k x =
      let s0 = !state in
      let y = state := s; k x in
      state := s0; y
  end
  include Memo (S)

  let pp = new_prompt ();;

  let fail () = abort pp (More []);;

  let reflect m= let curr_mem = !S.state in
    shift0 pp (fun k -> rextend (S.purify curr_mem k) m)

  let dist (choices : 'a dist) : 'a  =
    let curr_mem = !S.state in
    shift0 pp (fun k -> 
      More (List.map (fun (p,v) -> (p, (fun () -> S.purify curr_mem k v))) choices))

  let reify (thunk : unit -> 'a) : 'a m =
    let answer = ref None in
    let rec interp = function 
      | Done -> let Some x = !answer in [(1.0, V x)]
      | More ch -> List.map (fun (p,th) -> (p, C (fun () -> interp (th ())))) ch in
    let st () = push_prompt pp (fun () -> answer := Some (thunk ()); Done) in
    match interp (S.purify Store.empty st ()) with
    | [_,V x] -> V x
    | ch -> C (const ch)

end

module ProbVCRef5: PROB with type 'a m = 'a VCM.m = struct
  open Delimcc
  open Ptypes
  module M = VCM

  type 'a m = 'a vc

  type pReq = Done |  Choice of (unit -> pReq) cdist
   
  let pp = new_prompt ();;

  let from_option = function Some x -> x | None -> failwith "fromoption";;
  let read_answer r = let v = from_option !r in r := None; v (* for safety *)

  (* First-class storage: for the implementation of `thread-local' memory *)
  module Memory = struct
    type 'a loc = int * 'a option ref 
    type cell   = unit -> unit
    module M = Map.Make(struct type t = int let compare x y = x - y end)
    type mem = cell M.t
    let newm = M.empty
    let genid : unit -> int =	(* generating fresh locations *)
      let counter = ref 0 in
      fun () -> let v = !counter in counter := succ v; v
    let new_loc () = (genid (), ref None)
    let new_cell (_,chan) x = fun () -> chan := Some x
    let mref (id,chan) m =
      let cell = M.find id m in
      cell (); read_answer chan
    let mset ((id,chan) as loc) x m =
      M.add id (new_cell loc x) m
  end

  let thread_local = ref Memory.newm

  let reify (thunk : unit -> 'a) : 'a m =
    let answer = ref None in
    let rec interp = function 
      | Done -> [(1.0, V (read_answer answer))] (* deterministic value *)
      | Choice ch -> List.map (fun (p,th) -> (p, C (fun () -> interp (th ()))))
              ch
    in
    let mem = !thread_local in
    let v = push_prompt pp (fun () -> 
     thread_local := Memory.newm; answer := Some (thunk ()); Done) in
    thread_local := mem; 
    match interp v with
    | [_,V x] -> V x
    | ch -> C (const ch)
   

  let dist (choices : 'a dist) : 'a  =
    let curr_mem = !thread_local in
    shift0 pp (fun k -> 
      Choice 
         (List.map (fun (p,v) -> 
     (p, (fun () -> 
              let mem = !thread_local in
        let () = thread_local := curr_mem in
        let v = k v in
        thread_local := mem; v))) choices))
  

  let fail () = abort pp (Choice []);;

  let reflect = function
    | V x -> x
    | C th -> let tree = th () in
      let curr_mem = !thread_local in
      let rec make_choices k pv =
        Choice (List.map (
          function (p,V x) -> (p, fun () -> k x)
                      |  (p,C x) -> (p, fun () -> make_choices k (x ()))) pv) in
      shift0 pp (fun k -> 
        make_choices (fun x -> 
          let mem = !thread_local in
          let () = thread_local := curr_mem in
          let v = k x in
          thread_local := mem; v)
         tree)

  let letlazy e =
    let loc = Memory.new_loc () in
    let deref () = 
      try Memory.mref loc !thread_local 
      with Not_found ->
    let v = e () in
    let m' = Memory.mset loc v !thread_local in
    let () = thread_local := m' in
    v
    in deref

  let memo f =
    let loc = Memory.new_loc () in
    let m' = Memory.mset loc BatMap.empty !thread_local in
    let () = thread_local := m' in
    let deref x = 
      let table = Memory.mref loc !thread_local in
      try BatMap.find x table
      with Not_found ->
    let v = f x in			(* may change memory! *)
    let table = Memory.mref loc !thread_local in
    let m' = Memory.mset loc (BatMap.add x v table) !thread_local in
    let () = thread_local := m' in
    v
    in deref;;

  type 'a var = unit
  let letvar _ = failwith "letvar not supported"
  let force _ = failwith "var not supported"
  let constrain _ = failwith "var not supported"
end


(* The are implementations of nondeterminism and weighted nondeterminism
 * monads using lazy search trees. There are a few variants -- their are
 * two different variants of laziness:
 * 
 *  1. use separate thunks to explore each child of a node
 *  2. use a thunk to generate all children of a node at once
 *
 * In addition, the monadic type can 'plug into' the recursive tree structure at
 * different points: at the tree data type itself or at the expanded contents of
 * a node. This seems to have an effect on the depth of search trees
 * generated--see the WTree1 module below for more info.
 *)

open Monads
open Lazydata
open Utils

module WFTreeM = struct
  include WFTree

  type 'a m = 'a tree
  let return x = Leaf x
  let rec extend f = function
    | Leaf x -> f x
    | Node tst -> Node (Dist.fmap (extend f)  ** tst)
    | Stump -> Stump

  let bind t f = extend f t
  let fail = Stump
  let choice xs = Node (const (Dist.fmap return xs))
end

module TreeM = struct
  include Tree

  type 'a m = 'a tree
  let return x = Leaf x
  let rec extend f = function
    | Leaf x -> f x
    | Node tst -> Node (List.map (extend f) ** tst)

  let bind t f = extend f t
  let mzero () = Node (const [])
  let mplus x y = Node (fun () -> [x; y])
  let choice xs = Node (fun () -> List.map return xs)
end

module TreeT (M: MONAD) = struct
  type 'a tt = Leaf of 'a
             | Node of 'a tt list M.m
  type 'a m = 'a tt M.m

  module MO = MonadOps(M)
  open MO

  let return x = M.return (Leaf x)

  let bind m1 f = 
    let rec extend_subtree = function
      | Leaf x -> f x
      | Node m2 -> M.return (Node (m2 >>= mapM extend_subtree))
    in m1 >>= extend_subtree

  let mnode mchildren = M.return (Node mchildren)
  let leaf x = Leaf x

  let mzero ()    = mnode (M.return [])
  let mplus m1 m2 = mnode (sequence [m1; m2])
  let choice xs   = mnode (M.return (List.map leaf xs))
  let lift m1 = m1 >>= return

  let fold f s0 m1 = 
    let rec fold_tree s = function
      | Leaf x -> f s x
      | Node m2 -> m2 >>= foldM fold_tree s
    in m1 >>= fold_tree s0

  let to_tree m1 = 
    let rec tt_to_tree = function
      | Leaf x -> M.return (Tree.Leaf x)
      | Node m2 -> m2 >>= mapM tt_to_tree >>= (fun tree -> M.return (Tree.Node (fun () -> tree)))
    in m1 >>= tt_to_tree

end

module WTreeM = struct
  (* Weighted non-determinism monad using WTree lazy trees. 
   * The Node constructor contains a thunk to produce a distribution over
   * sub-trees. The monadic type is 'a tree, which has two constructors,
   * [Leaf] and [Node]. This means that return x can be represented simply
   * as Leaf x, but failure must be represented by a Node that produces an empty
   * list. 
   * *)
  include WTree

  type 'a m = 'a tree
  let return x = Leaf x
  let rec extend f = function
    | Leaf x -> f x
    | Node tst -> Node (Dist.fmap (extend f) ** tst)

  let bind t f = extend f t
  let fail = Node (const [])
  let choice xs = Node (fun () -> Dist.fmap return xs)
end

module WTreeAltM = struct
  open WTreeAlt

  type 'a m = 'a tree

  let return x = Leaf x
  let rec bind m f = match m with
    | Leaf x -> f x
    | Node ts -> Node (Dist.fmap (fun tt () -> bind (tt ()) f) ts)

  let lleaf x () = Leaf x
  let choice xs = Node (Dist.fmap lleaf xs)
  let fail = Node []
end

module WFTreeAltM = struct
  open WFTreeAlt

  type 'a m = 'a tree

  let return x = Leaf x
  let rec bind m f = match m with
    | Leaf x -> f x
    | Node ts -> Node (Dist.fmap (fun tt () -> bind (tt ()) f) ts)
    | Stump -> Stump

  let lleaf x () = Leaf x
  let choice xs = Node (Dist.fmap lleaf xs)
  let fail = Stump 
end

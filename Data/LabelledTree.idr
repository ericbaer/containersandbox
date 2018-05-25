||| Tree with a value at each node, labelled edges to children, and a different
||| value type at the leaves
module Data.LabelledTree

import Data.SortedMap
import Data.Some

namespace LabelledTree
  ||| Tree with a value at each node, labelled edges to children, and a
  ||| different value type at the leaves
  ||| @depth number of nodes between root and leaf. `Z` for `Leaf`s
  ||| @node  type at the nodes
  ||| @edge  type on the edge labels
  ||| @leaf  type at the leaves
  data LabelledTreeN :  (depth : Nat)
                 -> (node : Type)
                 -> (edge : Type)
                 -> (leaf : Type)
                 -> Type where
    Leaf :  leaf -> LabelledTreeN Z node edge leaf
    Node :  (Ord edge) => node -> SortedMap edge (LabelledTreeN n node edge leaf)
         -> LabelledTreeN (S n) node edge leaf

implementation (Show node, Show edge, Ord edge, Show leaf) =>
    Show (LabelledTreeN n node edge leaf) where
    showPrec d (Leaf leaf) = showCon d "Leaf" $ showArg leaf
    showPrec d (Node node children) = showCon d "Node" $ showArg node ++
        " " ++ (showCon d "fromList" $ showArg (toList children))

implementation (Eq node, Eq edge, Ord edge, Eq leaf) =>
    Eq (LabelledTreeN n node edge leaf) where
    (Leaf lleaf) == (Leaf rleaf) = lleaf == rleaf
    (Node lnode lkids) == (Node rnode rkids) =
        lnode == rnode && toList lkids == toList rkids

implementation (Ord node, Ord edge, Ord leaf) =>
    Ord (LabelledTreeN n node edge leaf) where
    compare (Leaf lleaf) (Leaf rleaf) = compare lleaf rleaf
    compare (Node lnode lkids) (Node rnode rkids) = compare lnode rnode
        `thenCompare` compare (toList lkids) (toList rkids)

||| Type synonym for `LabelledTreeN` where we don't care about the depth
LabelledTree : Type -> Type -> Type -> Type
LabelledTree node edge leaf = Some (Flipped4 LabelledTreeN leaf edge node)

||| `Forall` implementation for `Show` on `LabelledTree`s
implementation (Show node, Show edge, Ord edge, Show leaf) =>
    Forall Nat (Flipped4 LabelledTreeN leaf edge node) Show where
    mkImpl _ = %implementation
    
||| `Forall` implementation for `Eq` on `LabelledTree`s
implementation (Eq node, Eq edge, Ord edge, Eq leaf) =>
    Forall Nat (Flipped4 LabelledTreeN leaf edge node) Eq where
    mkImpl _ = %implementation

||| `Forall` implementation for `Ord` on `KVTree`s
implementation (Ord node, Ord edge, Ord leaf) =>
    Forall Nat (Flipped4 LabelledTreeN leaf edge node) Ord where
    mkImpl _ = %implementation

||| Merge the first (left) `LabelledTreeN` into the second (right)
||| `LabelledTreeN`, combining nodes or leaves at matching positions using
||| the provided functions, and recursively merging any subtrees with the
||| same labelled edge leading to them.
|||
||| @mergeNodes: a function for combining the values at two nodes
||| @mergeLeaves: a function for combining the values at two leaves
||| @left: the tree whose edges will be inserted into the right tree
||| @right: the tree into which edges will be inserted
merge :  (Ord edge, Monad m)
      => (mergeNodes : node -> node -> m node) 
      -> (mergeLeaves : leaf -> leaf -> m leaf)
      -> (left: LabelledTreeN n node edge leaf)
      -> (right : LabelledTreeN n node edge leaf)
      -> m (LabelledTreeN n node edge leaf)
merge mergeKeys mergeLeaves (Leaf lleaf) (Leaf rleaf) =
    Leaf <$> mergeLeaves lleaf rleaf
merge mergeKeys mergeLeaves (Node lkey lkids) (Node rkey rkids) = do
        mergedKey <- mergeKeys lkey rkey
        let go = flip $ tryInsert mergeKeys mergeLeaves
        mergedKids <- foldlM go lkids $ toList rkids
        pure $ Node mergedKey mergedKids
    where
        tryInsert :  (Ord edge, Monad m)
                  => (mergeNodes : node -> node -> m node)
                  -> (mergeLeaves : leaf -> leaf -> m leaf)
                  -> (edge, LabelledTreeN n node edge leaf)
                  -> SortedMap edge (LabelledTreeN n node edge leaf)
                  -> m (SortedMap edge (LabelledTreeN n node edge leaf))
        tryInsert mergeKeys mergeLeaves (edge, lkid) rkids =
            case lookup edge rkids of
                Nothing   => pure $ insert edge lkid rkids
                Just rkid => insert edge
                    <$> merge mergeKeys mergeLeaves lkid rkid
                    <*> pure rkids 

||| A function to pass to `merge` which returns `Nothing` if two values at a 
||| matching node position are not the same under the given definition of `Eq`,
||| i.e. the `merge` will fail and return `Nothing` itself.
sameNode : (Eq k) => k -> k -> Maybe k
sameNode l r = if l == r then Just l else Nothing

||| `sameKeys` with an error message on failure
sameNodeOr : (Eq k) => a -> k -> k -> Either a k
sameNodeOr a l r = maybe (Left a) Right $ sameNode l r 

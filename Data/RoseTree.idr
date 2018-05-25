module Data.RoseTree

import Data.Some
import Data.Equality.If

%access public export
%default total

namespace RoseTree
  ||| A tree which is at most n levels deep and holds values at the nodes
  data RoseTreeN : Nat -> Type -> Type where
    Node : key -> List (RoseTreeN n key) -> RoseTreeN (S n) key

implementation (Show a) => Show (RoseTreeN n a) where
    showPrec d (Node key kids) = showCon d "Node" $ showArg key ++ showArg kids

implementation (Eq a) => Eq (RoseTreeN n a) where
    (Node lkey lkids) == (Node rkey rkids) = lkey == rkey && lkids == rkids

implementation (Ord a) => Ord (RoseTreeN n a) where
    compare (Node lkey lkids) (Node rkey rkids) =
        case compare lkey rkey of
            EQ => compare lkids rkids
            tt => tt

||| Type synonym for `RoseTreeN` where we don't care about the depth
RoseTree : Type -> Type
RoseTree ty = Some (Flipped RoseTreeN ty)

||| Makes a tree taller. This takes advantage of the fact that `RoseTreeN`s do
||| not have `Leaf`s: a node with an empty list of children can be reassigned
||| to any n desired, and we will always reach such nodes in every path. 
stretchTree : LTE n m -> RoseTreeN n ty -> RoseTreeN m ty
stretchTree {n=Z}   {m=_}   LTEZero           node            impossible
stretchTree {n=S a} {m=Z}   noSuchLte         node            impossible
stretchTree {n=S Z} {m=S Z} (LTESucc LTEZero) node            = node
-- If n is 1, then kids must be empty, as no value occupies RoseTree Z ty
stretchTree {n=S Z} {m=S b} (LTESucc LTEZero) (Node key [])   = (Node key [])
stretchTree {n=S a} {m=S b} (LTESucc aLTEb)   (Node key kids) = 
    Node key $ map (stretchTree aLTEb) kids

||| Adds a new child tree to the root, given proof that the new child is no
||| taller than any of the existing children
addShorter :  LTE (S n) m
           -> (root : RoseTreeN (S m) ty)
           -> (kid : RoseTreeN n ty)
           -> RoseTreeN (S m) ty
addShorter {n=Z}   {m=Z}   snLTEm root kid impossible
addShorter {n=S a} {m=Z}   snLTEm root kid impossible
addShorter {n=S a} {m=S b} snLTEm (Node key kids) kid =
    Node key $ stretchTree (lteSuccLeft snLTEm) kid :: kids

||| Adds a new child tree to the root, given proof that the new child is taller
||| than any of the existing children.
addTaller :  LTE m n
          -> (root : RoseTreeN (S m) ty)
          -> (kid : RoseTreeN n ty)
          -> RoseTreeN (S n) ty
addTaller mLTEn (Node key kids) kid =
    Node key $ kid :: map (stretchTree mLTEn) kids

||| Adds a child, with the result type depending on whether the new child is
||| shorter or taller than the tallest existing child (this doesn't normalise
||| the height of the tallest child to the shortest possible)
addChild :  RoseTreeN (S a) ty -> RoseTreeN b ty
         -> RoseTreeN (S (if a > b then a else b)) ty
addChild {a} {b} root kid with (isLTE (S b) a)
    | Yes sbLTEa =
        rewrite lteIfGT {l=a} {r=b} sbLTEa
        in addShorter sbLTEa root kid
    | No nsbLTEa =
        rewrite notLTEIfGT {l=a} {r=b} nsbLTEa
        in addTaller (flipNotLTE nsbLTEa) root kid

-------------------------------------------------------------------------------
-- BinaryTree
-------------------------------------------------------------------------------

namespace BinaryTree
  ||| A tree with a branching factor of 2 that stores values at leaves only
  -- would be nice to make this into an n-ary tree with Vect n [NAryTree n ty]
  -- at the nodes, but as of 1.10 the totality checker has issues with that
  data BinaryTree : Type -> Type where
    Leaf : ty -> BinaryTree ty
    Node : BinaryTree ty -> BinaryTree ty -> BinaryTree ty

||| The maximum number of right turns you can take in the given tree. See
||| `rotate` for why this interesting.
maxRights : BinaryTree ty -> Nat
maxRights (Leaf _)   = 0
maxRights (Node l r) = max (maxRights l) (S $ maxRights r) 
 
-------------------------------------------------------------------------------
-- Rotation of BinaryTree into RoseTree
-------------------------------------------------------------------------------

||| See `rotate`. This adds the right-hand children from bottom to top, so e.g.
||| you end up with children in order [R, LR, LLR].
rotateReversed : (a : BinaryTree ty) -> RoseTreeN (S (maxRights a)) ty
rotateReversed (Leaf ty)  = Node ty []
rotateReversed (Node l r) = addChild (rotateReversed l) (rotateReversed r)

||| Reverse the order of the children at each level
mirror : RoseTreeN n ty -> RoseTreeN n ty
mirror (Node x kids) = Node x $ reverse $ map mirror kids

||| Convert the given `BinaryTree` into a `RoseTreeN`. The left-most node
||| becomes the new root, and all the right children along the left-most path
||| become the children of that root, recursively, with the right child of
||| the root of the `BinaryTree` at the end of the list of children of the
||| `RoseTreeN` root, and the right sibling of the left-most node in the
||| `BinaryTree` at the start of the list of children of the `RoseTreeN` root.
rotate : (a : BinaryTree ty) -> RoseTreeN (S (maxRights a)) ty
rotate btree = mirror $ rotateReversed btree

||| `Forall` implementation for `Show` on `RoseTree`s
implementation (Show ty) => Forall Nat (Flipped RoseTreeN ty) Show where
    mkImpl _ = %implementation
    
||| `Forall` implementation for `Eq` on `RoseTree`s
implementation (Eq ty) => Forall Nat (Flipped RoseTreeN ty) Eq where
    mkImpl _ = %implementation

||| `Forall` implementation for `Ord` on `RoseTree`s
implementation (Ord ty) => Forall Nat (Flipped RoseTreeN ty) Ord where
    mkImpl _ = %implementation
        

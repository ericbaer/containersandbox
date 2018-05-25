module Data.SizedVect

import Data.Vect

%access public export
%default total

namespace HSizedVect
    ||| A `Vect` that keeps track of some metric of size in addition to its
    ||| length, and where the type of the element at each index depends on the
    ||| size
    ||| @length the number of elements in the vector
    ||| @size the sum of the sizes of each element
    ||| @f function that takes a size and produces a type, which is the type of
    |||    the element at this position in the vector.
    data HSizedVect :  (length : Nat)
                    -> (size : Nat)
                    -> (f : Nat -> Type)
                    -> Type where
        Nil  : HSizedVect Z Z f
        (::) :  f s
             -> HSizedVect length size f
             -> HSizedVect (S length) (s + size) f

    ||| Sum of element sizes in entire `SizedVect`
    totalSize : {size : Nat} -> HSizedVect length size f -> Nat
    totalSize {size} _ = size

    ||| Size of the element at the head of the `SizedVect`
    headSize : HSizedVect (S length) size f -> Nat
    headSize ((::) {s} _ _) = s

namespace SizedVect
    ||| A `Vect` that keeps track of some metric of size in addition to its length
    ||| @length the number of elements in the vector
    ||| @size the sum of the sizes of each element
    ||| @sizeOf function that takes an element and produces a size
    data SizedVect :  (length : Nat)
                   -> (size : Nat)
                   -> (sizeOf : a -> Nat)
                   -> Type where
       Nil  : SizedVect Z Z sizeOf
       (::) :  (elem : a)
            -> SizedVect length size sizeOf
            -> SizedVect (S length) (sizeOf elem + size) sizeOf

    head : {sizeOf : a -> Nat} -> SizedVect (S n) o sizeOf -> a
    head (a::as) = a

    ||| A more convenient form of `sum . map sizeOf`
    sumSizes :  (Foldable f)
             => (sizeOf : a -> Nat)
             -> f a 
             -> Nat
    sumSizes sizeOf as = foldr (\a, n => sizeOf a + n) 0 as

    ||| Converts a `List` into a `SizedVect`
    ||| @sizeOf function to compute the sizes in the result
    ||| @as a `List` to convert to a `SizedVect`    
    fromList :  (sizeOf : a -> Nat)
             -> (as : List a)
             -> SizedVect (length as) (sumSizes sizeOf as) sizeOf
    fromList sizeOf []      = []
    fromList sizeOf (a::as) = a :: fromList sizeOf as
    
    ||| The `size` of the `SizedVect` returned by `take`    
    sizeOfTake :  (m : Nat)
               -> SizedVect (m + n) o sizeOf
               -> Nat
    sizeOfTake          Z      _       = Z
    sizeOfTake {sizeOf} (S m') (a::as) = sizeOf a + sizeOfTake m' as
    
    ||| Take the first `m` elements of `as`
    ||| @m how many elements to take
    ||| @as the `SizedVect` from which to take them
    take :  (m : Nat)
         -> (as : SizedVect (m + n) o sizeOf)
         -> SizedVect m (sizeOfTake m as) sizeOf
    take Z      _       = []
    take (S m') (a::as) = a :: take m' as
    
    infixr 7 ++
    
    ||| Append two `SizedVect`s
    (++) :  (as : SizedVect ma na sizeOf)
         -> (bs : SizedVect mb nb sizeOf)
         -> SizedVect (ma + mb) (na + nb) sizeOf
    (++) as bs {ma} {mb} = replace {P} (prf as bs) $ Go as bs where

        ||| A more convenient form for the size of appended `SizedVects`    
        addSizes :  (cs : SizedVect mc nc sizeOf)
                 -> (ds : SizedVect md nd sizeOf)
                 -> Nat
        addSizes {nd} []      ds = nd
        addSizes      (c::cs) ds = sizeOf c + addSizes cs ds
        
        Go :  (cs : SizedVect mc nc sizeOf)
           -> (ds : SizedVect md nd sizeOf)
           -> SizedVect (mc + md) (addSizes cs ds) sizeOf
        Go []      ds = ds
        Go (c::cs) ds = c :: Go cs ds

        ||| Proof that the more convenient form is the same as adding the sizes
        prf :  (cs : SizedVect mc nc sizeOf)
            -> (ds : SizedVect md nd sizeOf)
            -> addSizes cs ds = nc + nd
        prf      []       ds = Refl
        prf {nd} (c::cs') ds with (cong {f=(+) (sizeOf c)} $ prf cs' ds)
           | rec = trans rec $ plusAssociative (sizeOf c) _ nd
        
        P : Nat -> Type
        P n = SizedVect (ma + mb) n sizeOf

||| A wrapper for making `SizedVect` into something that can be `Foldable`
data FoldableSizedVect :  (length : Nat)
                       -> (size : Nat)
                       -> (sizeOf : a -> Nat)
                       -> Type
                       -> Type where
    MkFoldable :  {auto valid : a = b}
               -> SizedVect {a} m n sizeOf
               -> FoldableSizedVect m n sizeOf b

implementation Foldable (FoldableSizedVect m n sizeOf) where
    foldr func init (MkFoldable {valid} input) = go func init input where
        go :  {sizeOf : a -> Nat}
           -> (elem -> acc -> acc)
           -> acc
           -> SizedVect o p sizeOf
           -> acc
        go _ a []      = a
        go f a (e::es) = f (replace valid e) $ go f a es
        
    foldl func init (MkFoldable {valid} input) = go func init input where
        go :  {sizeOf : a -> Nat}
           -> (acc -> elem -> acc)
           -> acc
           -> SizedVect o p sizeOf
           -> acc
        go _ a []      = a
        go f a (e::es) = go f (f a (replace valid e)) es
    
implementation Show a => Show (SizedVect {a} m n sizeOf) where
    showPrec prec = showPrec prec . toList . MkFoldable

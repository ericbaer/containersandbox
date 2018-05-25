module Data.Some

import Data.Vect
import Data.HVect

%access public export
%default total

-------------------------------------------------------------------------------
-- Random combinators
-------------------------------------------------------------------------------

||| Reverses the order of arguments in a constructor of two type variables.
||| Equivalent to `flip` at the type level
data Flipped : (a -> b -> Type) -> b -> a -> Type where
    Flip : f a b -> Flipped f b a

implementation (Show (f a b)) => Show (Flipped f b a) where
    showPrec d (Flip fab) = showCon d "Flip" $ showArg fab

implementation (Eq (f a b)) => Eq (Flipped f b a) where
    (Flip l) == (Flip r) = l == r

implementation (Ord (f a b)) => Ord (Flipped f b a) where
    compare (Flip l) (Flip r) = compare l r

||| Reverses the order of arguments in a constructor of three type variables
data Flipped3 : (a -> b -> c -> Type) -> c -> b -> a -> Type where
    Flip3 : f a b c -> Flipped3 f c b a

implementation (Show (f a b c)) => Show (Flipped3 f c b a) where
    showPrec d (Flip3 fabc) = showCon d "Flip3" $ showArg fabc
    
implementation (Eq (f a b c)) => Eq (Flipped3 f c b a) where
    (Flip3 l) == (Flip3 r) = l == r

implementation (Ord (f a b c)) => Ord (Flipped3 f c b a) where
    compare (Flip3 l) (Flip3 r) = compare l r

||| Reverses the order of arguments in a constructor of four type variables
data Flipped4 : (a -> b -> c -> d -> Type) -> d -> c -> b -> a -> Type where
    Flip4 : f a b c d -> Flipped4 f d c b a

implementation (Show (f a b c d)) => Show (Flipped4 f d c b a) where
    showPrec d (Flip4 fabc) = showCon d "Flip3" $ showArg fabc
    
implementation (Eq (f a b c d)) => Eq (Flipped4 f d c b a) where
    (Flip4 l) == (Flip4 r) = l == r

implementation (Ord (f a b c d)) => Ord (Flipped4 f d c b a) where
    compare (Flip4 l) (Flip4 r) = compare l r

-------------------------------------------------------------------------------
-- Higher-order implementations
-------------------------------------------------------------------------------

||| Existential types in implementations. Note the distinction with the
||| similar type family in Haskell: this states that for any given value of ty,
||| there exists an implementation. It does not mean that there exists a single
||| implementation applicable to all ty. Assuming that ty is not `Type`, it is
||| perfectly legitimate to implement `mkImpl` by doing case analysis and
||| returning different implementations.
interface Forall ty (f : ty -> Type) (impl : Type -> Type) where
    mkImpl : (a : ty) -> impl (f a)

||| Analogous to `Compose` `Forall`. See the comments to `Forall`.
interface ForallF ty (g : x -> Type) (f : ty -> x) (impl : Type -> Type) where
    mkImplF : (a : ty) -> impl (g (f a))
    
-------------------------------------------------------------------------------
-- Some and its implementations
-------------------------------------------------------------------------------

||| For when you don't care about some type parameter, but you keep it around
||| anyway because it's the easiest way to convince the totality checker
data Some : (a -> Type) -> Type where
    Hide : t a -> Some t

smap : (Functor t) => ({a : _} -> a -> b) -> Some t -> Some t
smap f (Hide t) = Hide (map f t)

implementation (Forall ty f Show) => Show (Some f) where
    showPrec d (Hide {a} f) = showCon d "Hide" $ showArg @{mkImpl a} f

implementation (DecEq ty, Forall ty f Eq) => Eq (Some f) where
    (Hide {a=la} l) == (Hide {a=ra} r) with (decEq la ra)
        | Yes lara = (==) @{mkImpl la} l (rewrite lara in r)
        | No nlara = False

implementation (DecEq ty, Ord ty, Forall ty f Ord, Eq (Some f)) =>
    Ord (Some f) where
    compare (Hide {a=la} l) (Hide {a=ra} r) with (decEq la ra)
        | Yes lara = compare @{mkImpl la} l (rewrite lara in r)
        | No nlara = compare la ra

------------------------------------------------------------------------------
-- Uniqueness
------------------------------------------------------------------------------

||| Converts a vector of types into a type constructor which takes each of
||| those types as arguments, in order (from left-to-right)
FromTypeVect : Vect n Type -> Type
FromTypeVect []      = Type
FromTypeVect (a::as) = a -> FromTypeVect as

||| Applies a type constructor to a heterogeneous vector of its arguments
Apply : {ts : Vect n Type} -> FromTypeVect ts -> HVect ts -> Type
Apply f []      = f
Apply f (a::as) = Apply (f a) as

||| Given two heterogeneous vectors of the same types, yields a vector of
||| propositional equalities between each element at corresponding positions
||| in those vectors. (Basically `zip` (=), except for the higher-order type
||| of (=).)  
ReflVect : {as : Vect n Type} -> HVect as -> HVect as -> Vect n Type
ReflVect []      []      = []
ReflVect (x::xs) (y::ys) = (x=y)::(ReflVect xs ys)

-- FIXME: this needs some work
interface Unique (as : Vect n Type)
                 (f : FromTypeVect as)
                 (xs : HVect as)
                 (ys : HVect as) where
    ||| If all the type arguments xs and ys are equal, then that implies f xs
    ||| and f ys are equal 
    unique :  (fx : Apply f xs)
           -> (fy : Apply f ys)
           -> HVect (ReflVect xs ys)
           -> fx = fy

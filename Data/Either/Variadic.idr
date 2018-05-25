||| Variadic `Either`
module Data.Either.Variadic

import Data.Vect

%access public export
%default total

||| A very basic variadic `Either`. To recover the type of the element, you have
||| to pattern match on the tag:
|||
||| > data MyTag = IntTag | DoubleTag | BoolTag
||| >
||| > MyTypes : MyTag -> Type
||| > MyTypes IntTag    = Int
||| > MyTypes DoubleTag = Double
||| > MyTypes BoolTag   = Bool
||| > 
||| > foo : TaggedEither MyTypes -> String
||| > foo (Tag IntTag a)    = "Int: " ++ show (a + 0)
||| > foo (Tag DoubleTag a) = "Double: " ++ show (a * 1.0)
||| > foo (Tag BoolTag a)   = "Bool: " ++ show (a && True)
|||
||| You don't necessarily have to write the tag function in advance; see e.g.
||| `EitherN`.
data TaggedEither : (f : tag -> Type) -> Type where
    Tag : (t : tag) -> (a : f t) -> TaggedEither f

||| A variadic `Either` which uses `Elem`s as the tag. That means you have to
||| pattern-match on a bunch of `There`s in order to recover the type of the
||| element, which can be rather verbose, e.g.:
|||
||| > foo2 : EitherN [Int, Double, Bool] -> String    
||| > foo2 (Tag (_ ** Here)               a) = "Int: " ++ show (a + 0)
||| > foo2 (Tag (_ ** There Here)         a) = "Double: " ++ show (a * 1.0)
||| > foo2 (Tag (_ ** There (There Here)) a) = "Bool: " ++ show (a && True)
|||
||| However it doesn't require a fixed set of tags.
EitherN : Vect (S n) Type -> Type
EitherN as = TaggedEither FromElem where
    FromElem : DPair Type (flip Elem as) {- (a ** Elem a as) -} -> Type
    FromElem (a ** elem) = a

||| Add another type into the possible types of an `EitherN`, turning it into
||| an `Either` `S` `N` (hence the name).
EitherSN : EitherN ts -> EitherN (t::ts)
EitherSN (Tag (ty ** prf) a) = Tag (ty ** There prf) a

||| You can think of this function in two ways:
|||
||| 1. It "unrolls" an `EitherN` into an `Either` step-by-step
||| 2. It tries to "constrict" the possible types of an `EitherN`, but may fail
unroll : EitherN (t::ts) -> Either t (EitherN ts)
unroll (Tag (ty ** Here) a)        = Left a
unroll (Tag (ty ** (There prf)) a) = Right $ Tag (ty ** prf) a

||| Inverse of `unroll`
roll : Either t (EitherN ts) -> EitherN (t::ts)
roll (Left a)                    = Tag (_ ** Here) a
roll (Right (Tag (ty ** prf) b)) = Tag (ty ** There prf) b

||| The single element of `as` itself if its length is 1, `EitherN` otherwise
||| @as a vector of types
TypeOrEitherN : (as : Vect (S n) Type) -> Type
TypeOrEitherN [a] = a
TypeOrEitherN as  = EitherN as

||| Equivalent of `map ((=) x) ys`, but with readable error messages
EqOneOf : (x : ty) -> (ys : Vect n ty) -> Vect n Type
EqOneOf x []      = []
EqOneOf x (y::ys) = (x=y) :: EqOneOf x ys

||| Decide whether one thing is equal to any element of a vector
decEqMulti :  (DecEq ty)
           => (x : ty)
           -> (ys : Vect (S n) ty)
           -> Dec (EitherN (EqOneOf x ys))
decEqMulti x [y] with (decEq x y)
    | Yes x_y = Yes $ Tag (_ ** Here) x_y
    | No xnoy = No $ \(Tag (_ ** Here) x_y) => xnoy x_y
decEqMulti x (y::y'::ys) with (decEq x y)
    | Yes x_y = Yes $ roll $ Left x_y
    | No xnoy with (decEqMulti x (y'::ys))
        | Yes x_ys = Yes $ roll $ Right x_ys
        | No xnoys = No $ either xnoy xnoys . unroll

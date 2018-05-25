module Data.FiniteVect

%access public export
%default total

namespace FiniteVect
  ||| A `Vect` which can contain at most `capacity` elements
  ||| @free     How many more elements can we add
  ||| @capacity The maximum total number of elements
  data FiniteVect : (free : Nat) -> (capacity : Nat) -> Type -> Type where
    Nil  : FiniteVect n n a
    (::) : a -> FiniteVect (S m) n a -> FiniteVect m n a
  
  length : FiniteVect f c a -> Nat
  length Nil       = Z
  length (_::rest) = S $ length rest
  
  free : FiniteVect f c a -> Nat
  free {f} _ = f

  implementation Functor (FiniteVect f c) where
      map _ Nil     = Nil
      map f (a::as) = f a :: map f as

||| The `free` space in a `FiniteVect` is always less than or equal to the
||| total `capacity`
freeLTECapacity : FiniteVect f c a -> LTE f c
freeLTECapacity {f} {c} vect with (isLTE f c)
    | Yes fLTEc = fLTEc
    | No fNLTEc = absurd $ fNLTEc (go vect) where
        -- proof takes quadratic time, but never runs anyway
        go : FiniteVect g d b -> LTE g d
        go Nil       = lteRefl
        go (_::rest) with (go rest)
            | (LTESucc restProof) = lteSuccRight restProof

succDistributes : a + S b = S (a + b)
succDistributes {a=Z}        = Refl
succDistributes {a=S a'} {b} = cong {f=S} $ succDistributes {a=a'} {b}

||| The `capacity` minus the `free` space in a `FiniteVect` is always equal to
||| the `length`
||| @v the vector for which to prove this property
lengthPlusFreeIsCapacity: (v : FiniteVect f c a) -> length v + f = c
lengthPlusFreeIsCapacity {f} {c} v with (decEq (length v + f) c)
    | Yes eq = eq
    | No neq = absurd $ neq $ go v where
        -- proof takes quadratic time, but never runs anyway
        go : (u : FiniteVect g d b) -> length u + g = d
        go Nil       = Refl
        go (_::rest) = trans (sym succDistributes) (go rest)

||| The sum of two `Nat`s is always greater than or equal to either one
summandLTEResult : a + b = c -> LTE a c
summandLTEResult {a=Z}                 Refl = LTEZero
summandLTEResult {a=S a'} {b} {c=Z}    refl = absurd refl
summandLTEResult {a=S a'} {b} {c=S c'} refl = 
    LTESucc $ summandLTEResult $ succInjective (a' + b) (c') refl

lengthLTECapacity : (v : FiniteVect f c a) -> LTE (length v) c
lengthLTECapacity {c} vect with (isLTE (length vect) c)
    | Yes lenLTEc = lenLTEc
    | No lenNLTEc = absurd $ lenNLTEc $ summandLTEResult $
        lengthPlusFreeIsCapacity vect

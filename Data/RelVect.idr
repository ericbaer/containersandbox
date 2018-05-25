module Data.RelVect

%access public export
%default total

namespace RelVect
    mutual
        ||| Vector with proof that some binary relation `f` is occupied for
        ||| each pair of adjacent elements. `f` need not be commutative.
        data RelVect :  {a : Type} -> Nat -> (a -> a -> Type) -> Type where
            Nil  :  RelVect Z f
            (::) :  (b : a)
                 -> (bs : RelVect {a} n f)
                 -> {auto x : RelVectProof f b bs}
                 -> RelVect (S n) f

        ||| Takes the first element of a non-empty `RelVect`
        head : {f : a -> a -> Type} -> RelVect (S n) f -> a
        head (a::_) = a

        ||| Type of proof used for `RelVect`
        ||| @f a binary relation
        ||| @elem the new head
        ||| @rest the rest of the `RelVect`
        RelVectProof :  (f : a -> a -> Type)
                     -> (elem : a)
                     -> (rest : RelVect n f) 
                     -> Type
        RelVectProof {n=Z}   _ _ = const () -- no proof for first element
        RelVectProof {n=S m} f a = f a . head

    data Elem : a -> RelVect {a} n f -> Type where
        Here : Elem y ((::) y ys {x=_})
        There : (later : Elem y ys) -> Elem y ((::) z ys {x=_})
    
    last : {f : a -> a -> Type} -> RelVect (S n) f -> a
    last [a]         = a
    last (a::a'::as) = last (a'::as)
    
||| Special case for a `RelVect` with one element vs. many elements
||| @as a `RelVect` with element type `a`
||| @f a function to apply when `as` has a single element
||| @g a function to apply when `as` has many elements
ifSingleton :  (as : RelVect {a} (S n) rel)
            -> (f : a -> b)
            -> (g : RelVect {a} (S n) rel -> b)
            -> b
ifSingleton [a] f g = f a
ifSingleton as  f g = g as

||| Reduction sometimes gets stuck without this
ReduceRelVectProof :  {m : Nat}
                   -> RelVectProof {n=S m} f a as
                   -> f a (head as)
ReduceRelVectProof prf = prf

||| Type of a proof about the result of `rmap_`.
RmapProof :  {a : Type}
          -> {f : a -> a -> Type}
          -> (g : b -> b -> Type)
          -> (mapper : a -> b)
          -> (origin : RelVect n f)
          -> (result : RelVect n g)
          -> Type
RmapProof {n=Z}   _ _      _      _      = ()
RmapProof {n=S _} _ mapper origin result = head result = mapper (head origin)

||| Convenience synomym for the type of the second parameter to `rmap`, which
||| is rather complicated to write out in full. Needs improvement.
RmapProver :  (f : a -> a -> Type)
           -> (g : b -> b -> Type)
           -> (mapper : a -> b)
           -> Type
RmapProver {a} {b} f g mapper
           =  {m : Nat}
           -> {o : a}
           -> {os : RelVect m f}
           -> (o_prf : RelVectProof f o os)
           -> (r : b)
           -> (rs : RelVect m g)
           -> (r_is_mapper_o : r = mapper o)
           -> (r'_is_mapper_o' : RmapProof g mapper os rs)
           -> RelVectProof g (mapper o) rs

||| A helper function for `rmap`, which returns the result we want and a proof
||| of a property about that result, which is useful for induction but probably
||| not needed by the caller.
rmap_ :  {f : a -> a -> Type}
      -> {g : b -> b -> Type}
      -> (mapper : a -> b)
      -> (prover : RmapProver f g mapper)
      -> (origin : RelVect n f)
      -> DPair (RelVect n g) (RmapProof g mapper origin)
rmap_         mapper prover []                          = ([] ** ())
rmap_ {g} {b} mapper prover ((::) o os {x=o_prf})
    with (rmap_ mapper prover os)
        | ([] ** ())                                    = ([mapper o] ** Refl)
        | (((::) r' rs' {x=r'_prf}) ** r'_is_mapper_o') =
            ((::) r (r'::rs') {x=r_prf} ** r_is_mapper_o) where
            r : b
            r = mapper o
            r_is_mapper_o : r = mapper o
            r_is_mapper_o = Refl
            r_prf : g (mapper o) r'
            r_prf = prover o_prf r (r'::rs') r_is_mapper_o r'_is_mapper_o'

||| `RelVect`s can't be `Functor`s, because of the pairwise proofs; this
||| function is a rough analogue to `map`, but unfortunately has a much more
||| complicated type (see `RmapProver`)
||| @mapper a function to transform the elements
||| @prover a function to transform the pairwise proofs
||| @origin a `Relvect` over which to map
rmap :  {f : a -> a -> Type}
     -> {g : b -> b -> Type}
     -> (mapper : a -> b)
     -> (prover : RmapProver f g mapper)
     -> (origin : RelVect n f)
     -> RelVect n g
rmap mapper prover origin = fst $ rmap_ mapper prover origin

||| Obvious lemma about the behaviour of `rmap`
RmapUsesRmap_ :  {f : a -> a -> Type}
              -> {g : b -> b -> Type}
              -> {as : RelVect (S n) f}
              -> {bs : RelVect (S n) g}
              -> {mapper : a -> b}
              -> {prover : RmapProver f g mapper}
              -> rmap mapper prover as = fst (rmap_ mapper prover as)
RmapUsesRmap_ = Refl

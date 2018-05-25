||| Utilities for dealing in a unified fashion with functions (in particular,
||| type constructors) which take different numbers of arguments
module Data.Function.Variadic

import Data.Bits
import Data.Vect
import Data.HVect

import Data.RelVect

%access public export
%default total

------------------------------------------------------------------------------
-- Preliminary lemmas which should be somewhere else
------------------------------------------------------------------------------

cong2 :  {a, c : x} -> {b, d : y} -> {f : x -> y -> z} 
      -> a = c -> b = d -> f a b = f c d
cong2 Refl Refl = Refl

InputInj : (a -> b) = (c -> d) -> a = c
InputInj Refl = Refl

OutputInj : (a -> b) = (c -> d) -> b = d
OutputInj Refl = Refl

------------------------------------------------------------------------------
-- Representing variadic type constructors
------------------------------------------------------------------------------

infixr 5 ~+>

||| A tractable representation of the type of an uncurried function (not the
||| actual function itself)
data UncurriedFunction : Nat -> Type where
    ||| Fixity deliberately lower than `::` of `Vect`, so that you can write
    ||| things like this with just one set of parentheses:
    ||| > foo (a::as ~+> result) = ...
    (~+>) :  (args : Vect n Type)
          -> (result : Type)
          -> UncurriedFunction n

infixl 4 ~:>

||| Shorthand for adding another argument type onto `UncurriedFunction`          
(~:>) : Type -> UncurriedFunction n -> UncurriedFunction (S n)
(~:>) a (as ~+> r) = (a::as ~+> r)

||| Basic lemma about `UncurriedFunction`
ConsInjective :  (a :: as ~+> ra) ~=~ (b :: bs ~+> rb)
              -> (as ~+> ra) ~=~ (bs ~+> rb)
ConsInjective Refl = Refl

||| Recover equality of arities from heterogeneous equality of representations
RecoverArity :  {a : UncurriedFunction m}
             -> {b : UncurriedFunction n}
             -> a ~=~ b
             -> m = n
RecoverArity {m=Z}    {n=Z}    Refl = Refl
RecoverArity {m=Z}    {n=S n'} Refl impossible
RecoverArity {m=S m'} {n=Z}    Refl impossible
RecoverArity {m=S m'} {n=S n'} {a=_::as ~+> ra} {b=_::bs ~+> rb} refl =
    cong {f=S} $ RecoverArity $ ConsInjective refl

||| Applies the function `f` to both sides of a heterogeneous equality between
||| two `UncurriedFunction`s, i.e. in the case where their arities are not
||| known to be equal and regular `cong` will not work.
CongUncurried :  {a : UncurriedFunction m}
              -> {b : UncurriedFunction n}
              -> (f : {i : Nat} -> UncurriedFunction i -> c) 
              -> a ~=~ b
              -> f a = f b
CongUncurried f a_b with (RecoverArity a_b)
    | Refl = cong {f} a_b
              
||| Shorthand for stripping the first argument type off of `UncurriedFunction`
Tail : UncurriedFunction (S n) -> UncurriedFunction n
Tail (a::as ~+> r) = (as ~+> r)

Arity : UncurriedFunction n -> Nat
Arity {n} _ = n

||| > ModifyResultType ([Int, Bool] ~+> String) List =
||| >     [Int, Bool] ~+> (List String)
ModifyResultType :  (f : Type -> Type)
                 -> UncurriedFunction n
                 -> UncurriedFunction n
ModifyResultType f (args ~+> result) = args ~+> f result

||| > SetResultType ([Int, Bool] ~+> String) Bytes = [Int, Bool] ~+> Bytes
SetResultType : Type -> UncurriedFunction n -> UncurriedFunction n
SetResultType s = ModifyResultType $ const s

||| Textual equivalent of `~+>`, the constructor of `UncurriedFunction`
Uncurry : Vect n Type -> (r : Type) -> UncurriedFunction n
Uncurry as r = as ~+> r

ResultType : UncurriedFunction n -> Type
ResultType (_ ~+> r) = r

ArgTypeVect : UncurriedFunction n -> Vect n Type
ArgTypeVect (as ~+> _) = as

------------------------------------------------------------------------------
-- Recurry and utilities for using it
------------------------------------------------------------------------------

||| Recover function's actual type from `UncurriedFunction` representation
Recurry : UncurriedFunction n -> Type
Recurry {n=Z}   ([]    ~+> r) = r
Recurry {n=S _} (a::as ~+> r) = a -> Recurry (as ~+> r)

||| Converts a normal function into one that takes an `HVect` of its args
||| @rep the tractable representation of the function's type
||| @fun the actual function
||| @args a heterogenous vector of arguments
ApplyHVect :  {rep : UncurriedFunction n}
           -> (fun : Recurry rep)
           -> (args : HVect (ArgTypeVect rep))
           -> ResultType rep
ApplyHVect {n=Z}   {rep=[]    ~+> _} fun []      = fun
ApplyHVect {n=S _} {rep=t::ts ~+> r} fun (a::as) =
    ApplyHVect {rep=ts ~+> r} (fun a) as

||| Variadic `const` in a particular shape
constN : (rep : UncurriedFunction n) -> ResultType rep -> Recurry rep
constN {n=Z}   ([]    ~+> _)  val = val
constN {n=S _} (a::as ~+> ty) val = const $ constN (as ~+> ty) val

------------------------------------------------------------------------------
-- Proofs about the behaviour of Recurry
------------------------------------------------------------------------------

||| The most basic lemma about how `Recurry` works
RecurryStep : Recurry (a :: as ~+> ra) = (a -> Recurry (as ~+> ra))
RecurryStep = Refl

||| Another basic lemma about how `Recurry` works
RecurryZ : (a : UncurriedFunction Z) -> Recurry a = ResultType a
RecurryZ ([] ~+> r) = Refl

||| Equality is preserved when adding equal argument types onto the front of
||| each list of argument types
RecurryCons :  a = b
            -> Recurry (as ~+> ra) = Recurry (bs ~+> rb)
            -> Recurry (a :: as ~+> ra) = Recurry (b :: bs ~+> rb)
RecurryCons {b} a_b as_bs = cong2 {f=\x, y => x -> y} a_b as_bs

||| Equality of function types implies equality of their first input type
RecurryHead :  {as, bs : Vect n Type}
            -> Recurry ((a::as) ~+> ra) = Recurry ((b::bs) ~+> rb)
            -> a = b
RecurryHead raas_rbbs = InputInj raas_rbbs
         
||| Equality between is preserved when stripping arguments off of each list of
||| argument types.
RecurrySucc :  {as, bs : Vect n Type}
            -> Recurry (a :: as ~+> ra) = Recurry (b :: bs ~+> rb)
            -> Recurry (as ~+> ra) = Recurry (bs ~+> rb)
RecurrySucc {as=[]}      {bs=[]}      Refl      = Refl
RecurrySucc {as=[]}      {bs=b'::bs'} raas_rbbs impossible
RecurrySucc {as=a'::as'} {bs=[]}      raas_rbbs impossible
RecurrySucc {a} {ra} {as=a'::as'} {b} {rb} {bs=b'::bs'} raas_rbbs = qed where
    astep : Recurry (a :: a' :: as' ~+> ra) = (a -> Recurry (a' :: as' ~+> ra))
    astep = RecurryStep {a} {as=a'::as'} {ra}
    bstep : Recurry (b :: b' :: bs' ~+> rb) = (b -> Recurry (b' :: bs' ~+> rb))
    bstep = RecurryStep {a=b} {as=b'::bs'} {ra=rb}
    right : Recurry (a :: a' :: as' ~+> ra) = (b -> Recurry (b' :: bs' ~+> rb))
    right = trans raas_rbbs bstep
    both  : (a -> Recurry (a' :: as' ~+> ra)) = (b -> Recurry (b' :: bs' ~+> rb))
    both  = trans astep right
    qed   : Recurry (a' :: as' ~+> ra) = Recurry (b' :: bs' ~+> rb)
    qed   = OutputInj both

||| Recover equality of arguments of `Recurry` from equality of results
RecurryInj : {a, b : UncurriedFunction n} -> Recurry a = Recurry b -> a = b
RecurryInj {n=Z}   {a=[] ~+> ra} {b=[] ~+> rb} refl
    with ((Recurry $ [] ~+> ra), (Recurry $ [] ~+> rb))
    -- have to force it to calculate the Recurry of both arguments manually
    -- before it reduces the Recurry a and Recurry b in refl
    | (_, _) = cong {f=([] ~+>)} refl
RecurryInj {n=S m} {a=(a::as) ~+> ra} {b=(b::bs) ~+> rb} refl =
    cong2 {f=(~:>)} a_b as_bs
    where
    a_b : a = b
    a_b = RecurryHead refl
    as_bs : (as ~+> ra) = (bs ~+> rb)
    as_bs = RecurryInj $ RecurrySucc refl

||| Recover equality of arities from equality of results of `Recurry`
ArityEqual :  {a, b : UncurriedFunction n}
           -> Recurry a = Recurry b
           -> Arity a = Arity b
ArityEqual {a} {b} ra_rb = cong {f=Arity} $ RecurryInj {a} {b} ra_rb
              
------------------------------------------------------------------------------
-- RelVects of UncurriedFunctions
------------------------------------------------------------------------------

namespace UncurriedFunctionVect

    ||| Type of elements in an `UncurriedFunctionVect`
    data Elem : Type where
        MkElem :  (arity : Nat)
               -> (kind : UncurriedFunction arity)
               -> (fun : Recurry kind)
               -> Elem

    ||| Accessor for `Elem`
    Arity : Elem -> Nat
    Arity (MkElem arity _ _) = arity

    ||| Accessor for `Elem`
    Kind : (a : Elem) -> UncurriedFunction (Arity a)
    Kind (MkElem _ kind _) = kind
    
    ||| Accessor for `Elem`
    Function : (a : Elem) -> Recurry (Kind a)
    Function (MkElem _ _ fun) = fun
    
    ||| Type of `SameVectProof` in an `UncurriedFunctionVect`
    data Proof : Elem -> Elem -> Type where
        MkProof :  {a, b : Elem}
                -> Arity a = Arity b
                -> Kind a = Kind b
                -> Proof a b

||| Accessor for `Proof`
AritiesEqual : Proof a b -> Arity a = Arity b
AritiesEqual (MkProof prf _) = prf

||| Accessor for `Proof`
KindsEqual : Proof a b -> Kind a ~=~ Kind b
KindsEqual (MkProof _ prf) = prf

||| The following will not work:
||| 
||| > lemma : Proof a b -> Recurry (Kind a) = Recurry (Kind b)
||| > lemma p = cong {f=Recurry} $ KindsEqual p
|||
||| First you have to pattern-match that `AritiesEqual` is `Refl`.
CongKindsEqual :  (f : {n : Nat} -> UncurriedFunction n -> ty)
               -> Proof a b
               -> f (Kind a) = f (Kind b)
CongKindsEqual {a=MkElem n ak _} {b=MkElem n b _} f (MkProof Refl prf) =
    cong {f} prf
    
||| `RelVect` of `DPair`s of `UncurriedFunction` representations and actual
||| functions of type `Recurry` of those representations. For example, given:
|||
||| > data Foo : A -> B -> Type where ...
||| > data Bar : A -> B -> Type where ...
||| > data Qux : A -> B -> Type where ...
||| >
||| > rep : UncurriedFunction 2
||| > rep = [A, B] ~+> Type
|||
||| We can put them all into an `UncurriedFunctionVect` like this:
|||
||| > fs : UncurriedFunctionVect 3 2
||| > fs = [(rep ** Foo), (rep ** Bar), (rep ** Qux)]
|||
||| What this gains us over a simple `Vect [A -> B -> Type]`: we can express
||| the type of "vectors of type constructors" regardless of the number of
||| arguments.
UncurriedFunctionVect : (n : Nat) -> Type
UncurriedFunctionVect n = RelVect n Proof

||| Given the example types in the comments to `UncurriedFunctionVect`, then:
|||
||| > TraverseUncurried fs EitherN =
||| >     \a, b => EitherN [Foo a b, Bar a b, Qux a b]
|||
||| @fs a vector of type constructors
||| @valid a proof that they're actually type constructors
||| @vectToType a function to make a type from any number of types
TraverseUncurried :  (fs : UncurriedFunctionVect (S count))
                  -> {valid : ResultType (Kind $ head fs) = Type}
                  -> (vectToType : {x : Nat} -> Vect (S x) Type -> Type)
                  -> Recurry (Kind $ head fs)
TraverseUncurried {valid} fs vectToType = Go fs {gs_valid=valid} [] where
    ||| Makes a `Vect` of type constructors into an `EitherN`. The `kind` is
    ||| required to prove that they're all actually type constructors.
    FromVector :  (kind : UncurriedFunction a)
               -> {auto kind_valid : ResultType kind = Type}
               -> Vect (S n) (Recurry kind)
               -> Recurry kind
    FromVector {kind_valid} {n} {a=Z} kind constrs = final where
        lemma : Recurry kind = Type
        lemma = trans (RecurryZ kind) kind_valid
        types : Vect (S n) Type
        types = replace {P=Vect (S n)} lemma constrs
        final : Recurry kind
        final = rewrite lemma in vectToType types
    FromVector {a=S n} (a :: as ~+> r) constrs =
        \o => FromVector (as ~+> r) (map (\x => x o) constrs)

    ||| Converts the whole `SameVect` into a regular `Vect` (proving at each
    ||| step that the types are actually the same), then applies `FromVector`
    Go :  (gs : UncurriedFunctionVect (S n))
       -> {gs_valid : ResultType (Kind $ head gs) = Type}
       -> Vect o (Recurry (Kind $ head $ gs))
       -> Recurry (Kind $ head gs)
    Go [a] acc = FromVector (Kind a) (Function a :: acc)
    Go {o} {n=S m} ((::) a as {x}) {gs_valid} acc
        with (ReduceRelVectProof {a} {as} x)
        | _ = rewrite lemma in Go as {gs_valid=valid'} acc' where
            lemma  : Recurry (Kind a) = Recurry (Kind $ head as)
            lemma  = CongKindsEqual Recurry x
            acc'   : Vect (S o) $ Recurry $ Kind $ head as
            acc'   = replace {P=Vect (S o)} lemma $ Function a :: acc
            valid' : ResultType (Kind $ head  as) = Type
            valid' = trans (sym $ CongKindsEqual ResultType x) gs_valid

------------------------------------------------------------------------------
-- RelVects of type indices
------------------------------------------------------------------------------

||| Deliberately not using an implementation for these, since it tends to make
||| error messages unreadable.
data IsTypeIndex : Type -> Type where
    MkIsTypeIndex :  (getArity : i -> Nat)
                  -> (getKind  : (x : i) -> UncurriedFunction (getArity x))
                  -> (isTyCon  : (x : i) -> ResultType (getKind x) = Type)
                  -> IsTypeIndex i

IndexArity : IsTypeIndex i -> i -> Nat
IndexArity (MkIsTypeIndex getArity _ _) = getArity

IndexKind :  (impl : IsTypeIndex i) -> (x : i)
          -> UncurriedFunction (IndexArity impl x)
IndexKind (MkIsTypeIndex _ getKind _) = getKind

IndexIsTyCon :  (impl : IsTypeIndex i) -> (x : i)
             -> ResultType (IndexKind impl x) = Type
IndexIsTyCon (MkIsTypeIndex _ _ isTyCon) = isTyCon

namespace TypeIndex

    ArityLemma :  {o : UncurriedFunction arity}
               -> {x : i}
               -> (impl : IsTypeIndex i)
               -> IndexKind impl x = o
               -> IndexArity impl x = arity
    ArityLemma _ Refl = Refl

    ||| Proof used for a TypeIndexVect
    VectProof : IsTypeIndex i -> i -> i -> Type
    VectProof impl a b = (IndexKind impl a ~=~ IndexKind impl b)
    
    ||| Reduction seems to get stuck                            
    ReduceVectProof :  VectProof impl a b
                    -> IndexKind impl a ~=~ IndexKind impl b
    ReduceVectProof refl = refl
            
TypeIndexVect :  Nat
              -> IsTypeIndex i
              -> Type
TypeIndexVect n isTypeIndex = RelVect n (TypeIndex.VectProof isTypeIndex)

CongKind : a = MkElem b c d -> Kind a = c
CongKind Refl = Refl

||| Normally would be inside `fromIndices_`, except that having it outside
||| makes it easier to express some proofs
fromIndicesMapper :  (isTypeIndex : IsTypeIndex i)
                  -> (toType : (x : i) -> Recurry (IndexKind isTypeIndex x))
                  -> i
                  -> UncurriedFunctionVect.Elem
fromIndicesMapper isTypeIndex toType x = MkElem (IndexArity isTypeIndex x)
    (IndexKind isTypeIndex x) (toType x)

||| The `RmapProof` returned by `fromIndices_`
FromIndicesProof :  (isTypeIndex : IsTypeIndex i)
                 -> (toType : (x : i) -> Recurry (IndexKind isTypeIndex x))
                 -> TypeIndexVect (S n) isTypeIndex
                 -> UncurriedFunctionVect (S n)
                 -> Type
FromIndicesProof isTypeIndex toType = RmapProof UncurriedFunctionVect.Proof
    (fromIndicesMapper isTypeIndex toType)

||| Prove that applying `toType` to every element of `origin` yields a legal
||| `UncurriedFunctionVect` (i.e. that all indices have the same `IndexKind`)
||| @isTypeIndex proof that some type is a valid type index
||| @toType mapping from indices to actual type constructors
||| @origin a non-empty vector of type indices
fromIndices_ :  (isTypeIndex : IsTypeIndex i)
             -> (toType : (x : i) -> Recurry (IndexKind isTypeIndex x))
             -> (origin : TypeIndexVect (S n) isTypeIndex)
             -> DPair (UncurriedFunctionVect (S n))
                      (FromIndicesProof isTypeIndex toType origin)
fromIndices_ isTypeIndex toType origin =
    rmap_ (fromIndicesMapper isTypeIndex toType) prover origin where
    
    prover : RmapProver (TypeIndex.VectProof isTypeIndex)
                        UncurriedFunctionVect.Proof
                        (fromIndicesMapper isTypeIndex toType)
    prover o_prf r rs r_is_mapper_o r'_is_mapper_o' with (rs)
        | []        = ()
        | (r'::rs') with (trans o_prf $ sym $ CongKind r'_is_mapper_o')
            | o'_r' = MkProof (TypeIndex.ArityLemma isTypeIndex o'_r') o'_r'

||| Given `o` (i.e. `S n`) type indices `i_1, i_2 ... i_o`, representing type
||| constructors which all take arguments `(a_1 : t_1) ... (a_o : t_o)`, yield
||| a type constructor of the form:
|||
||| > a_1 -> a_2 -> ... a_o ->
||| > vectToType [i_1 $ a_1 ... a_o, i_2 $ a_1 ... a_o, ... i_o $ a_1 ... a_o]
|||
||| @isTypeIndex proof that some type is a valid type index
||| @indexToType mapping from indices to actual type constructors
||| @vectToType mapping from a vector of types to a type, e.g. `EitherN`
||| @origin a non-empty vector of type indices
indicesToType :  (isTypeIndex : IsTypeIndex i)
              -> (indexToType : (x : i) -> Recurry (IndexKind isTypeIndex x))
              -> (vectToType : {x : Nat} -> Vect (S x) Type -> Type)
              -> (origin : TypeIndexVect (S n) isTypeIndex)
              -> Recurry (IndexKind isTypeIndex (head origin))
indicesToType {n} isTypeIndex indexToType vectToType as = final where
    thing : DPair (UncurriedFunctionVect (S n))
                  (FromIndicesProof isTypeIndex indexToType as)
    thing = fromIndices_ isTypeIndex indexToType as
    lemma : Kind (head $ fst thing) = IndexKind isTypeIndex (head as)
    lemma = CongKind $ snd thing
    valid : ResultType (Kind $ head $ fst thing) = Type
    valid = trans (CongUncurried ResultType lemma)
                  (IndexIsTyCon isTypeIndex $ head as)
    final : Recurry (IndexKind isTypeIndex (head as))
    final = replace {P=id} (CongUncurried Recurry lemma) 
                    (TraverseUncurried {valid} (fst thing) vectToType)

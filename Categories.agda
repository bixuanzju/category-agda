{-# OPTIONS --type-in-type #-}

-- Copied from CS410-17 by Mcbride

module Categories where

open import Prelude

postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g

imp : {S : Set}{T : S -> Set}(f : (x : S) -> T x){x : S} -> T x
imp f {x} = f x

extensionality' : {S : Set}{T : S -> Set}
                  {f g : {x : S} -> T x} ->
                  ((x : S) -> f {x} == g {x}) ->
                  _==_ {forall {x : S} -> T x} f g
extensionality' {f = f}{g = g} q =
  refl imp =$= extensionality {f = \ x -> f {x}}{g = \ x -> g {x}} q

_=$'_ : {S : Set}{T : S -> Set}
        {f g : {x : S} -> T x} ->
        _==_ {forall {x : S} -> T x} f g ->
        (x : S) -> f {x} == g {x}
refl f =$' x = refl (f {x})

infixl 2 _=$'_


record Category : Set where
  field

    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj -> Obj -> Set    -- "arrows" or "morphisms"

    -- two operations
    id~>        : {T : Obj} ->      T ~> T
    _>~>_       : {R S T : Obj} ->  R ~> S  ->  S ~> T  ->  R ~> T

    -- Composition left unit law
    law-id~>>~> : {S T : Obj}     (f : S ~> T) -> (id~> >~> f) == f
    -- Composition right unit law
    law->~>id~> : {S T : Obj}     (f : S ~> T) -> (f >~> id~>) == f
    -- Composition associative law
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) -> ((f >~> g) >~> h) == (f >~> (g >~> h))


  -- The so-called whiskering
  whiskerl : {A B C : Obj} {g1 g2 : B ~> C} {f : A ~> B}  -> g1 == g2 -> (f >~> g1) == (f >~> g2)
  whiskerl {f = f} (refl x) = refl (f >~> x)

  whiskerr : {B C D : Obj} {g1 g2 : B ~> C} {h : C ~> D}  -> g1 == g2 -> (g1 >~> h) == (g2 >~> h)
  whiskerr {h = h} (refl x) = refl (x >~> h)


  infixr 3 _>~>_

-- Empty category
EMPTY : Category
EMPTY = record
          { Obj = Zero
          ; _~>_ = λ _ _ → Zero
          ; id~> = λ {T} → T
          ; _>~>_ = λ {R} {S} → λ {}
          ; law-id~>>~> = λ {S} {T} → λ ()
          ; law->~>id~> = λ {S} → λ {}
          ; law->~>>~> = λ {Q} {R} {S} → λ {}
          }


-- Another trivial category
ONE : Category
ONE = record
        { Obj = One
        ; _~>_ = λ S T -> One
        ; id~> = <>
        ; _>~>_ = λ _ _ → <>
        ; law-id~>>~> = idOne1
        ; law->~>id~> = idOne1
        ; law->~>>~> = λ f g h → refl <>
        } where
        idOne1 : (f : One) -> f == <>
        idOne1 <> = refl <>



-- The Category of sets
SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \S T -> S -> T
        ; id~> = id
        ; _>~>_ = _>>_
        ; law-id~>>~> = λ f → refl f
        ; law->~>id~> = λ f → refl f
        ; law->~>>~> = λ f g h → refl (f >> (g >> h))
        }


module FUNCTOR where
  open Category
  -- Functor from C to D
  record _=>_ (C D : Category) : Set where
    field
      -- Two mappings
      F-Obj : Obj C -> Obj D
      F-map : {S T : Obj C} -> _~>_ C S T -> _~>_ D (F-Obj S) (F-Obj T)

      -- Two laws
      F-map-id~> : {T : Obj C} -> F-map (id~> C {T}) == id~> D {F-Obj T}
      F-map->~> : {R S T : Obj C} (f : _~>_ C R S) (g : _~>_ C S T) ->
                  F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)


open FUNCTOR public

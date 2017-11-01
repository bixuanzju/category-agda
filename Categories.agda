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

  infixr 3 _>~>_

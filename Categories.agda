{-# OPTIONS --type-in-type #-}

module Categories where

open import Prelude

record Category : Set where
  infixr 3 _>~>_
  field
    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj -> Obj -> Set    -- "arrows" or "morphisms"

    -- two operations
    id~>        : {T : Obj} ->      T ~> T
    _>~>_       : {R S T : Obj} ->  R ~> S  ->  S ~> T  ->  R ~> T

    -- Composition left unit law
    law-id~>>~> : {S T : Obj}     (f : S ~> T) -> id~> >~> f == f
    -- Composition right unit law
    law->~>id~> : {S T : Obj}     (f : S ~> T) -> f >~> id~> == f
    -- Composition associative law
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) -> (f >~> g) >~> h == f >~> (g >~> h)


  -- The so-called whiskering
  whiskerl : {A B C : Obj} {g1 g2 : B ~> C} {f : A ~> B}  -> g1 == g2 -> f >~> g1 == f >~> g2
  whiskerl {f = f} refl = refl

  whiskerr : {B C D : Obj} {g1 g2 : B ~> C} {h : C ~> D}  -> g1 == g2 -> g1 >~> h == g2 >~> h
  whiskerr {h = h} refl = refl



-- Empty category
EMPTY : Category
EMPTY = record
          { Obj = Zero
          ; _~>_ = λ _ _ → Zero
          ; id~> = λ {T} → T
          ; _>~>_ = λ x _ → magic x
          ; law-id~>>~> = λ f → magic f
          ; law->~>id~> = λ f → magic f
          ; law->~>>~> = λ f g h → magic f
          }


-- Another trivial category
ONE : Category
ONE = record
        { Obj = One
        ; _~>_ = λ _ _ -> One
        ; id~> = <>
        ; _>~>_ = λ _ _ → <>
        ; law-id~>>~> = idOne
        ; law->~>id~> = idOne
        ; law->~>>~> = λ _ _ _ → refl
        } where
        idOne : (f : One) -> f == <>
        idOne <> = refl


unique->= : (m n : Nat) (p q : m >= n) -> p == q
unique->= m zero <> <> = refl
unique->= zero (suc n) p ()
unique->= (suc m) (suc n) p q = unique->= m n p q


-- Preorder is a category (should probably generalize to any preorder)
PREORDER-ℕ->= : Category
PREORDER-ℕ->= = record
                  { Obj = Nat
                  ; _~>_ = _>=_
                  ; id~> = λ {n} → refl->= n
                  ; _>~>_ = λ {m n p} f g → trans->= m n p f g
                  ; law-id~>>~> = λ {n m} f → unique->= n m _ _
                  ; law->~>id~> = λ {n m} f → unique->= n m _ _
                  ; law->~>>~> = λ {n m s t} f g h → unique->= n t _ _
                  }


record Monoid (X : Set): Set where
  infixr 5 _⋆_
  field
    ε : X
    _⋆_ : X → X → X
    absorbL : (x : X) → ε ⋆ x == x
    absorbR : (x : X) → x ⋆ ε == x
    assoc   : (x y z : X) → (x ⋆ y) ⋆ z == x ⋆ (y ⋆ z)
open Monoid {{...}} public


-- Monoid is a category
MONOID : {X : Set} {{m : Monoid X}} -> Category
MONOID  {X} = record
           { Obj = One
           ; _~>_ = λ _ _ → X
           ; id~> = ε
           ; _>~>_ = λ a b → a ⋆ b
           ; law-id~>>~> = λ f → absorbL f
           ; law->~>id~> = λ f → absorbR f
           ; law->~>>~> = λ f g h → assoc f g h
           }


-- The category of sets
SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \S T -> S -> T
        ; id~> = id
        ; _>~>_ = _>>_
        ; law-id~>>~> = λ _ → refl
        ; law->~>id~> = λ _ → refl
        ; law->~>>~> = λ _ _ _ → refl
        }

-- Monoid homomorphism
record MonoidHom {X} {{MX : Monoid X}} {Y} {{MY : Monoid Y}} (f : X  → Y) : Set where
  field
    respε : f ε == ε
    resp⋆ : ∀ x x' → f (x ⋆ x') == f x ⋆ f x'

SomeMonoid : Set
SomeMonoid = Sg Set Monoid


-- The category of monoids
CAT-MONOID : Category
CAT-MONOID  = record
               { Obj = SomeMonoid
               ; _~>_ = λ m n → Prf (fst m → fst n) λ f → MonoidHom {{snd m}} {{snd n}} f
               ; id~> = mid
               ; _>~>_ = mcom
               ; law-id~>>~> = λ _ → refl
               ; law->~>id~> = λ _ → refl
               ; law->~>>~> = λ _ _ _ → refl
               } where
                 mid : {T : SomeMonoid} → Prf (fst T → fst T) (λ f → MonoidHom {{snd T}} {{snd T}} f)
                 mid {X , m} = id , record { respε = refl ; resp⋆ = λ _ _ → refl }

                 mcom : {R S T : SomeMonoid} →
                        Prf (fst R → fst S) (λ f → MonoidHom {{snd R}} {{snd S}} f) →
                        Prf (fst S → fst T) (λ f → MonoidHom {{snd S}} {{snd T}} f) →
                        Prf (fst R → fst T) (λ f → MonoidHom {{snd R}} {{snd T}} f)
                 mcom {R , m} {S , n} {T , s} (f , fm) (g , gm)
                   = let instance
                           -- Bring instances into scope
                           _ : Monoid S
                           _ = n
                           _ : Monoid R
                           _ = m
                           _ : Monoid T
                           _ = s
                     in
                     f >> g , record { respε = g (f ε) ≡⟨ cong g (MonoidHom.respε fm) ⟩
                                               g ε  ≡⟨ MonoidHom.respε gm ⟩
                                               ε
                                               □
                                     ; resp⋆ = λ a b → g (f (a ⋆ b)) ≡⟨ cong g (MonoidHom.resp⋆ fm a b) ⟩
                                                       g (f a ⋆ f b) ≡⟨ MonoidHom.resp⋆ gm (f a) (f b) ⟩
                                                       g (f a) ⋆ g (f b)
                                                       □
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

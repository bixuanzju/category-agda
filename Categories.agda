{-# OPTIONS --type-in-type #-}

module Categories where

open import Prelude


----------------------------------------------------------------------------
-- Definition of a category
----------------------------------------------------------------------------

record Category : Set where
  infixl 3 _>~>_
  field
    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj → Obj → Set      -- "arrows" or "morphisms"

    -- two operations
    id~>        : {T : Obj} →      T ~> T
    _>~>_       : {R S T : Obj} →  R ~> S → S ~> T → R ~> T

    -- Composition left unit law
    law-id~>ˡ : {S T : Obj}     (f : S ~> T) → id~> >~> f ≡ f
    -- Composition right unit law
    law-id~>ʳ : {S T : Obj}     (f : S ~> T) → f >~> id~> ≡ f
    -- Composition associative law
    law->~>  : {Q R S T : Obj} (f : Q ~> R) (g : R ~> S)(h : S ~> T) → (f >~> g) >~> h ≡ f >~> (g >~> h)


  -- The so-called whiskering
  whiskerˡ : {A B C : Obj} {g1 g2 : B ~> C} {f : A ~> B} → g1 ≡ g2 → f >~> g1 ≡ f >~> g2
  whiskerˡ {f = f} refl = refl

  whiskerʳ : {B C D : Obj} {g1 g2 : B ~> C} {h : C ~> D} → g1 ≡ g2 → g1 >~> h ≡ g2 >~> h
  whiskerʳ {h = h} refl = refl


----------------------------------------------------------------------------
-- Structured sets as categories
----------------------------------------------------------------------------

-- Empty category
EMPTY : Category
EMPTY = record
          { Obj = Zero
          ; _~>_ = λ _ _ → Zero
          ; id~> = λ {T} → T
          ; _>~>_ = λ x _ → magic x
          ; law-id~>ˡ = λ f → magic f
          ; law-id~>ʳ = λ f → magic f
          ; law->~> = λ f g h → magic f
          }


-- Another trivial category
ONE : Category
ONE = record
        { Obj = One
        ; _~>_ = λ _ _ → One
        ; id~> = <>
        ; _>~>_ = λ _ _ → <>
        ; law-id~>ˡ = λ { <> → refl }
        ; law-id~>ʳ = λ { <> → refl }
        ; law->~> = λ _ _ _ → refl
        }


record Preorder (X : Set) : Set where
  infixl 5 _≤_
  field
    _≤_ : X → X → Set
    ≤-refl : (x : X) → x ≤ x
    ≤-trans : (x y z : X) → x ≤ y → y ≤ z → x ≤ z
    ≤-unique : (x y : X) → (p q : x ≤ y) → p ≡ q
open Preorder {{...}} public


-- Preorder is a category
PREORDER : {X : Set} {{_ : Preorder X}} → Category
PREORDER {X} = record
             { Obj = X
             ; _~>_ = _≤_
             ; id~> = λ {T} → ≤-refl T
             ; _>~>_ = λ {R} {S} {T} f g → ≤-trans R S T f g
             ; law-id~>ˡ = λ {S} {T} _ → ≤-unique S T _ _
             ; law-id~>ʳ = λ {S} {T} _ → ≤-unique S T _ _
             ; law->~> = λ {Q} {R} {S} {T} f g h → ≤-unique Q T _ _
             }


record Monoid (X : Set) : Set where
  infixl 5 _⋆_
  field
    ε : X
    _⋆_ : X → X → X
    absorbL : (x : X) → ε ⋆ x ≡ x
    absorbR : (x : X) → x ⋆ ε ≡ x
    assoc   : (x y z : X) → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)
open Monoid {{...}} public


-- Monoid is a category
MONOID : {X : Set} {{_ : Monoid X}} → Category
MONOID {X}
  =   record
       { Obj = One
       ; _~>_ = λ _ _ → X
       ; id~> = ε
       ; _>~>_ = _⋆_
       ; law-id~>ˡ = absorbL
       ; law-id~>ʳ = absorbR
       ; law->~> = assoc
       }


----------------------------------------------------------------------------
-- Categories of structured sets
----------------------------------------------------------------------------

-- The category of sets
SET : Category
SET = record
        { Obj = Set
        ; _~>_ = λ S T → S → T
        ; id~> = id
        ; _>~>_ = _>>_
        ; law-id~>ˡ = λ _ → refl
        ; law-id~>ʳ = λ _ → refl
        ; law->~> = λ _ _ _ → refl
        }

-- Monotone
record Monotone {X} {{MX : Preorder X}} {Y} {{MY : Preorder Y}} (f : X → Y) : Set where
  field
    resp≤ : ∀ {x x'} → x ≤ x' → f x ≤ f x'


SomePreorder : Set
SomePreorder = Σ Set Preorder


-- The category of preorders
Cat-Preorder : Category
Cat-Preorder = record
             { Obj = SomePreorder
             ; _~>_ = λ { (m , ≤m) (n , ≤n) → Subset (m → n) λ f → Monotone {{_}} {{_}} f }
             ; id~> = id # record { resp≤ = id }
             ; _>~>_ = λ { {R , m} {S , n} {T , s} (f # fm) (g # gm) →
                    let instance
                           -- Bring instances into scope
                           _ : Preorder S
                           _ = n
                           _ : Preorder R
                           _ = m
                           _ : Preorder T
                           _ = s
                     in f >> g # record { resp≤ = λ x≤y → Monotone.resp≤ gm (Monotone.resp≤ fm x≤y) }

               }
             ; law-id~>ˡ = λ _ → refl
             ; law-id~>ʳ = λ _ → refl
             ; law->~> = λ _ _ _ → refl
             }


-- Monoid homomorphism
record MonoidHom {X} {{MX : Monoid X}} {Y} {{MY : Monoid Y}} (f : X  → Y) : Set where
  field
    respε : f ε ≡ ε
    resp⋆ : ∀ x x' → f (x ⋆ x') ≡ f x ⋆ f x'


SomeMonoid : Set
SomeMonoid = Σ Set Monoid

-- The category of monoids
CAT-MONOID : Category
CAT-MONOID  = record
               { Obj = SomeMonoid
               ; _~>_ = λ { (m , ⋆m) (n , ⋆n) → Subset (m → n) λ f → MonoidHom {{_}} {{_}} f  }
               ; id~> = id # record { respε = refl ; resp⋆ = λ _ _ → refl }
               ; _>~>_ = λ { {R , m} {S , n} {T , s} (f # fm) (g # gm) →
                       let instance
                             _ : Monoid S
                             _ = n
                             _ : Monoid R
                             _ = m
                             _ : Monoid T
                             _ = s
                       in
                       f >> g # record { respε = begin
                                           g (f ε)
                                          ≡⟨ cong g (MonoidHom.respε fm) ⟩
                                           g ε
                                          ≡⟨ MonoidHom.respε gm ⟩
                                           ε □
                                       ; resp⋆ = λ a b → begin
                                           g (f (a ⋆ b))
                                          ≡⟨ cong g (MonoidHom.resp⋆ fm a b) ⟩
                                           g (f a ⋆ f b)
                                          ≡⟨ MonoidHom.resp⋆ gm (f a) (f b) ⟩
                                           g (f a) ⋆ g (f b) □
                                       }
                        }
               ; law-id~>ˡ = λ _ → refl
               ; law-id~>ʳ = λ _ → refl
               ; law->~> = λ _ _ _ → refl
               }


{-# OPTIONS --type-in-type #-}


open import Prelude
open import Categories
open import Functors
open import Monics
open import Terminals

module CoProducts (C : Category )where



----------------------------------------------------------------------------
-- CoProducts
----------------------------------------------------------------------------

open Category C
open Iso C

record CoProduct (A B : Obj) : Set where
  field
    A+B : Obj
    ι₀ : A ~> A+B
    ι₁ : B ~> A+B
    [_,_] : ∀ {X} → (A ~> X) → (B ~> X) → (A+B ~> X)

    commute₁ : ∀ {X} {f : A ~> X} {g : B ~> X} → ι₀ >~> [ f , g ] ≡ f
    commute₂ : ∀ {X} {f : A ~> X} {g : B ~> X} → ι₁ >~> [ f , g ] ≡ g
    universal : ∀ {X} {f : A ~> X} {g : B ~> X} {t : A+B ~> X} →
                   ι₀ >~> t ≡ f → ι₁ >~> t ≡ g → [ f , g ] ≡ t
  ι-id : [ ι₀ , ι₁ ] ≡ id~>
  ι-id = universal (law-id~>ʳ _) (law-id~>ʳ _)

  ι-η : ∀ {C} → {f : A+B ~> C} → [ ι₀ >~> f , ι₁ >~> f ] ≡ f
  ι-η = universal refl refl

  post-composing-with-tuple : ∀ {X Y} (j : X ~> Y) (f : A ~> X) (g : B ~> X) →
                             [ f , g ] >~> j ≡ [ f >~> j , g >~> j ]
  post-composing-with-tuple i f g = sym (universal {!!} {!!})
    where
      help₁ : ι₀ >~> ([ f , g ] >~> i) ≡ f >~> i
      help₁ = begin
        ι₀ >~> ([ f , g ] >~> i)
       ≡⟨ sym (law->~> _ _ _) ⟩
        ι₀ >~> [ f , g ] >~> i
       ≡⟨ whiskerʳ commute₁ ⟩
        f >~> i □

      help₂ : ι₁ >~> ([ f , g ] >~> i) ≡ g >~> i
      help₂ = begin
        ι₁ >~> ([ f , g ] >~> i)
       ≡⟨ sym (law->~> _ _ _) ⟩
        ι₁ >~> [ f , g ] >~> i
       ≡⟨ whiskerʳ commute₂ ⟩
        g >~> i □

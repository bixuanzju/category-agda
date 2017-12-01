
{-# OPTIONS --type-in-type #-}

module TerminalDef where

open import Prelude
open import Categories
open import FunctorDef
open import MonicDef



----------------------------------------------------------------------------
-- Terminal and initial objects
----------------------------------------------------------------------------

record Terminal (C : Category): Set where
  open Category C
  field
    𝟙 : Obj
    ! : ∀ {A} → A ~> 𝟙
    !-unique : ∀ {A} → (f : A ~> 𝟙) → f ≡ !

  -- identity expansion for terminals
  ⊤-id : (f : 𝟙 ~> 𝟙) → f ≡ id~>
  ⊤-id f = begin
    f
   ≡⟨ !-unique f ⟩
    !
   ≡⟨ sym (!-unique id~>) ⟩
    id~> □

module terminals-up-to-iso (C : Category)  where

  open Category C
  open Terminal
  open Iso C

  up-to-iso : (T R : Terminal C) → (𝟙 T) ≅ (𝟙 R)
  up-to-iso T R = record { f = ! R  ; iso-witness = record { fʳ = ! T ; inverse = ⊤-id T _ ; inverseʳ = ⊤-id R _ } }



module pre-composing-with-bang {C : Category} (T : Terminal C) where
  open Category C
  open Terminal

  lemma : {X Y : Obj} → (i : Y ~> X) → i >~> ! T ≡ ! T
  lemma i = !-unique T (i >~> ! T)


Terminal-Cat-Preorder : Terminal Cat-Preorder
Terminal-Cat-Preorder =
  record { 𝟙 = One , record { _≤_ = λ _ _ → One
                            ; ≤-refl = id
                            ; ≤-trans = λ _ _ _ _ _ → <>
                            ; ≤-unique = λ _ _ _ _ → refl }
         ; ! = (λ _ → <>) # record { resp≤ = λ _ → <> }
         ; !-unique = λ f → refl }

record Increasing-Preorder {X} (p : Preorder X) : Set where
  open Preorder
  field
    e : X
    ≤-e : (x : X) → _≤_ p x e


Terminal-Preorder : ∀ {X} → {{p : Preorder X}} (MP : Increasing-Preorder p) → Terminal (PREORDER {{p}})
Terminal-Preorder MP = record { 𝟙 = e MP ; ! = λ {x} → ≤-e MP x ; !-unique = λ {x} _ → ≤-unique x _ _ _ }
  where open Increasing-Preorder


record Initial (C : Category): Set where
  open Category C
  field
    𝟘 : Obj
    ! : ∀ {A} → 𝟘 ~> A
    !-unique : ∀ {A} → (f : 𝟘 ~> A) → f ≡ !

  -- identity expansion for initials
  ⊥-id : (f : 𝟘 ~> 𝟘) → f ≡ id~>
  ⊥-id f = begin
    f
   ≡⟨ !-unique f ⟩
    !
   ≡⟨ sym (!-unique id~>) ⟩
    id~> □

module initials-up-to-iso (C : Category) where

  open Category C
  open Initial
  open Iso C

  up-to-iso : (T R : Initial C) → (𝟘 T) ≅ (𝟘 R)
  up-to-iso T R = record { f = ! T ; iso-witness = record { fʳ = ! R ; inverse = ⊥-id T _ ; inverseʳ = ⊥-id R _ } }



module post-composing-with-bang {C : Category} (T : Initial C) where
  open Category C
  open Initial

  lemma : {X Y : Obj} → (i : X ~> Y) → ! T >~> i ≡ ! T
  lemma i = !-unique T (! T >~> i)


Initial-Cat-Preorder : Initial Cat-Preorder
Initial-Cat-Preorder =
  record { 𝟘 = Zero , record { _≤_ = λ _ _ → Zero ; ≤-refl = id ; ≤-trans = λ x _ _ _ _ → x ; ≤-unique = λ x _ _ _ → magic x }
         ; ! = (λ x → magic x) # record { resp≤ = λ x → magic x }
         ; !-unique = λ f → proof-irr (extensionality λ x → magic x)
         }


record Decreasing-Preorder {X} (p : Preorder X) : Set where
  open Preorder
  field
    e : X
    ≤-e : (x : X) → _≤_ p e x


Initial-Preorder : ∀ {X} → {{p : Preorder X}} (MP : Decreasing-Preorder p) → Initial (PREORDER {{p}})
Initial-Preorder MP = record { 𝟘 = e MP ; ! = λ {x} → ≤-e MP x ; !-unique = λ {x} _ → ≤-unique _ x _ _ }
  where open Decreasing-Preorder

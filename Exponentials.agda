
{-# OPTIONS --type-in-type #-}


open import Prelude
open import Categories hiding (ε)
open import Functors
open import Monics

module Exponentials (C : Category) where

open import Products C
open Category C


record Exponential (A B : Obj) : Set where
  field
    Aᴮ : Obj
    {Aᴮ×A} : Product Aᴮ A
    eval : Product.A×B Aᴮ×A ~> B
    λf : ∀ {X} {X×A : Product X A} → Product.A×B X×A ~> B → X ~> Aᴮ

    commute : ∀ {X} {X×A : Product X A} → (f : Product.A×B X×A ~> B) →
              (arrow-product X×A Aᴮ×A (λf {X×A = X×A} f) id~>) >~> eval ≡ f

    universal : ∀ {X} {X×A : Product X A} → (f : Product.A×B X×A ~> B) (g : X ~> Aᴮ) →
                (arrow-product X×A Aᴮ×A g id~>) >~> eval ≡ f → (λf {X×A = X×A} f) ≡ g

  exponential-id : λf {X×A = Aᴮ×A} eval ≡ id~>
  exponential-id = universal eval id~>
                   (
                    arrow-product Aᴮ×A Aᴮ×A id~> id~> >~> eval
                   ≡⟨ cong (λ x → x >~> eval) help ⟩
                    id~> >~> eval
                   ≡⟨ law-id~>ˡ _ ⟩
                    eval □
                   )
    where
      help : arrow-product Aᴮ×A Aᴮ×A id~> id~> ≡ id~>
      help = begin
        P.⟨ P.π₀ >~> id~> , P.π₁ >~> id~> ⟩
       ≡⟨ cong (λ x → P.⟨ x , P.π₁ >~> id~> ⟩) (law-id~>ʳ _) ⟩
        P.⟨ P.π₀ , P.π₁ >~> id~> ⟩
       ≡⟨ cong (λ x → P.⟨ P.π₀ , x ⟩) (law-id~>ʳ _) ⟩
        P.⟨ P.π₀ , P.π₁ ⟩
       ≡⟨ P.π-id ⟩
        id~> □
        where module P = Product Aᴮ×A

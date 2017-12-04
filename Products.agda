{-# OPTIONS --type-in-type #-}

open import Prelude
open import Categories
open import Functors
open import Monics
open import Terminals


module Products (C : Category) where

----------------------------------------------------------------------------
-- Products
----------------------------------------------------------------------------

open Category C
open Iso C

record Product (A B : Obj) : Set where
  field
    A×B : Obj
    π₀ : A×B ~> A
    π₁ : A×B ~> B
    ⟨_,_⟩ : ∀ {C} → (C ~> A) → (C ~> B) → (C ~> A×B)

    commute₁ : ∀ {X} {f : X ~> A} {g : X ~> B} → ⟨ f , g ⟩ >~> π₀ ≡ f
    commute₂ : ∀ {X} {f : X ~> A} {g : X ~> B} → ⟨ f , g ⟩ >~> π₁ ≡ g
    universal : ∀ {X} {f : X ~> A} {g : X ~> B} {t : X ~> A×B} →
                   t >~> π₀ ≡ f → t >~> π₁ ≡ g → ⟨ f , g ⟩ ≡ t

  π-id : ⟨ π₀ , π₁ ⟩ ≡ id~>
  π-id = universal (law-id~>ˡ _) (law-id~>ˡ _)

  π-η : ∀ {C} → {f : C ~> A×B} → ⟨ f >~> π₀ , f >~> π₁ ⟩ ≡ f
  π-η = universal refl refl

  pre-composing-with-tuple : {X Y : Obj} (i : Y ~> X) (f : X ~> A) (g : X ~> B) →
                             i >~> ⟨ f , g ⟩ ≡ ⟨ i >~> f , i >~> g ⟩
  pre-composing-with-tuple i f g = sym (universal help₁ help₂)
    where
      help₁ : i >~> ⟨ f , g ⟩ >~> π₀ ≡ i >~> f
      help₁ = begin
        i >~> ⟨ f , g ⟩ >~> π₀
       ≡⟨ law->~> _ _ _ ⟩
        i >~> (⟨ f , g ⟩ >~> π₀)
       ≡⟨ whiskerˡ commute₁ ⟩
        i >~> f □
      help₂ : i >~> ⟨ f , g ⟩ >~> π₁ ≡ i >~> g
      help₂ = begin
        i >~> ⟨ f , g ⟩ >~> π₁
       ≡⟨ law->~> _ _ _ ⟩
        i >~> (⟨ f , g ⟩ >~> π₁)
       ≡⟨ whiskerˡ commute₂ ⟩
        i >~> g □


up-to-iso : ∀ {A B} → (P Q : Product A B) → Product.A×B P ≅ Product.A×B Q
up-to-iso P Q = record { f = s
                       ; iso-witness = record { fʳ = t
                                              ; inverse = begin
                                                  s >~> t
                                                 ≡⟨ sym (Product.universal P lemmaP₁ lemmaP₂) ⟩
                                                  Product.⟨_,_⟩ P p₀ p₁
                                                 ≡⟨ Product.π-id P ⟩
                                                  id~> □
                                              ; inverseʳ = begin
                                                  t >~> s
                                                 ≡⟨ sym (Product.universal Q lemmaQ₁ lemmaQ₂) ⟩
                                                  Product.⟨_,_⟩ Q q₀ q₁
                                                 ≡⟨ Product.π-id Q ⟩
                                                  id~> □
                                              }
                       }
  where p₀ = Product.π₀ P
        p₁ = Product.π₁ P
        q₀ = Product.π₀ Q
        q₁ = Product.π₁ Q
        s = Product.⟨_,_⟩ Q p₀ p₁
        t = Product.⟨_,_⟩ P q₀ q₁
        lemmaP₁ : s >~> t >~> p₀ ≡ p₀
        lemmaP₁ = begin
          s >~> t >~> p₀
         ≡⟨ law->~> _ _ _ ⟩
          s >~> (t >~> p₀)
         ≡⟨ whiskerˡ (Product.commute₁ P) ⟩
          s >~> q₀
         ≡⟨ Product.commute₁ Q ⟩
          p₀ □
        lemmaP₂ : s >~> t >~> p₁ ≡ p₁
        lemmaP₂ = begin
          s >~> t >~> p₁
         ≡⟨ law->~> _ _ _ ⟩
          s >~> (t >~> p₁)
         ≡⟨ whiskerˡ (Product.commute₂ P) ⟩
          s >~> q₁
         ≡⟨ Product.commute₂ Q ⟩
          p₁ □
        lemmaQ₁ : t >~> s >~> q₀ ≡ q₀
        lemmaQ₁ = begin
          t >~> s >~> q₀
         ≡⟨ law->~> _ _ _ ⟩
          t >~> (s >~> q₀)
         ≡⟨ whiskerˡ (Product.commute₁ Q) ⟩
          t >~> p₀
         ≡⟨ Product.commute₁ P ⟩
          q₀ □
        lemmaQ₂ : t >~> s >~> q₁ ≡ q₁
        lemmaQ₂ = begin
          t >~> s >~> q₁
         ≡⟨ law->~> _ _ _ ⟩
          t >~> (s >~> q₁)
         ≡⟨ whiskerˡ (Product.commute₂ Q) ⟩
          t >~> p₁
         ≡⟨ Product.commute₂ P ⟩
          q₁ □


arrow-product : ∀ {X Y A B} (P : Product X Y) (Q : Product A B) → (f : X ~> A) (g : Y ~> B) → Product.A×B P ~> Product.A×B Q
arrow-product P Q f g = Q.⟨ (P.π₀ >~> f) , (P.π₁ >~> g) ⟩
  where module P = Product P
        module Q = Product Q


-×- : (p : (A B : Obj) → Product A B) → Prod C C => C
-×- p = record { 𝔽₀ = λ {(a , b) → Product.A×B (p a b)}
               ; 𝔽₁ = λ {(f , g) → arrow-product (p _ _) (p _ _) f g}
               ; F-map-id~> = λ { {A₀ , A₁} →
                   let open module A₀×A₁ = Product (p A₀ A₁)
                   in begin
                      ⟨ π₀ >~> id~> , π₁ >~> id~> ⟩
                     ≡⟨ cong (λ x → ⟨ x , π₁ >~> id~> ⟩) (law-id~>ʳ _) ⟩
                      ⟨ π₀ , π₁ >~> id~> ⟩
                     ≡⟨ cong (λ x → ⟨ π₀ , x ⟩) (law-id~>ʳ _) ⟩
                      ⟨ π₀ , π₁ ⟩
                     ≡⟨ π-id ⟩
                      id~> □
                 }
               ; F-map->~> = λ { {A₀ , A₁} {B₀ , B₁} {C₀ , C₁} (f₀ , f₁) (g₀ , g₁) →
                   let module A₀×A₁ = Product (p A₀ A₁)
                       module B₀×B₁ = Product (p B₀ B₁)
                       module C₀×C₁ = Product (p C₀ C₁)
                       f₀×f₁ = arrow-product (p _ _) (p _ _) f₀ f₁
                       g₀×g₁ = arrow-product (p _ _) (p _ _) g₀ g₁
                   in begin
                      C₀×C₁.⟨ A₀×A₁.π₀ >~> (f₀ >~> g₀) , A₀×A₁.π₁ >~> (f₁ >~> g₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ x , A₀×A₁.π₁ >~> (f₁ >~> g₁) ⟩) (sym (law->~> _ _ _)) ⟩
                      C₀×C₁.⟨ A₀×A₁.π₀ >~> f₀ >~> g₀ , A₀×A₁.π₁ >~> (f₁ >~> g₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ A₀×A₁.π₀ >~> f₀ >~> g₀ , x ⟩) (sym (law->~> _ _ _)) ⟩
                      C₀×C₁.⟨ A₀×A₁.π₀ >~> f₀ >~> g₀ , A₀×A₁.π₁ >~> f₁ >~> g₁ ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ x >~> g₀ , A₀×A₁.π₁ >~> f₁ >~> g₁ ⟩) (sym B₀×B₁.commute₁) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> B₀×B₁.π₀ >~> g₀ , A₀×A₁.π₁ >~> f₁ >~> g₁ ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ f₀×f₁ >~> B₀×B₁.π₀ >~> g₀ , x >~> g₁ ⟩) (sym B₀×B₁.commute₂) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> B₀×B₁.π₀ >~> g₀ , f₀×f₁ >~> B₀×B₁.π₁ >~> g₁ ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ x , f₀×f₁ >~> B₀×B₁.π₁ >~> g₁ ⟩) (law->~> _ _ _) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> (B₀×B₁.π₀ >~> g₀) , f₀×f₁ >~> B₀×B₁.π₁ >~> g₁ ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ f₀×f₁ >~> (B₀×B₁.π₀ >~> g₀) , x ⟩) (law->~> _ _ _) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> (B₀×B₁.π₀ >~> g₀) , f₀×f₁ >~> (B₀×B₁.π₁ >~> g₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ f₀×f₁ >~> x , f₀×f₁ >~> (B₀×B₁.π₁ >~> g₁) ⟩) (sym C₀×C₁.commute₁) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₀) , f₀×f₁ >~> (B₀×B₁.π₁ >~> g₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₀) , f₀×f₁ >~> x ⟩) (sym C₀×C₁.commute₂) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₀) , f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ x , f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₁) ⟩) (sym (law->~> _ _ _)) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> g₀×g₁ >~> C₀×C₁.π₀ , f₀×f₁ >~> (g₀×g₁ >~> C₀×C₁.π₁) ⟩
                     ≡⟨ cong (λ x → C₀×C₁.⟨ f₀×f₁ >~> g₀×g₁ >~> C₀×C₁.π₀ , x ⟩) (sym (law->~> _ _ _)) ⟩
                      C₀×C₁.⟨ f₀×f₁ >~> g₀×g₁ >~> C₀×C₁.π₀ , f₀×f₁ >~> g₀×g₁ >~> C₀×C₁.π₁ ⟩
                     ≡⟨ C₀×C₁.π-η ⟩
                      f₀×f₁ >~> g₀×g₁ □
                 }
               }

post-composing-arrow-product : ∀ {X A₀ A₁ B₀ B₁} (P : Product A₀ A₁) (Q : Product B₀ B₁) →
                               (f₀ : X ~> A₀) (f₁ : X ~> A₁) →
                               (g₀ : A₀ ~> B₀) (g₁ : A₁ ~> B₁) →
                               (Product.⟨_,_⟩ P f₀ f₁) >~> (arrow-product P Q g₀ g₁) ≡ Product.⟨_,_⟩ Q (f₀ >~> g₀) (f₁ >~> g₁)
post-composing-arrow-product P Q f₀ f₁ g₀ g₁ = begin
  P.⟨ f₀ , f₁ ⟩ >~> arrow-product P Q g₀ g₁
 ≡⟨ sym Q.π-η ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₀ , P.⟨ f₀ , f₁ ⟩ >~> Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁ ⟩
 ≡⟨ cong (λ x → Q.⟨ x , P.⟨ f₀ , f₁ ⟩ >~> Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁ ⟩) (law->~> _ _ _) ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₀) , P.⟨ f₀ , f₁ ⟩ >~> Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁ ⟩
 ≡⟨ cong (λ x → Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₀) , x ⟩) (law->~> _ _ _) ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₀) , P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁) ⟩
 ≡⟨ cong (λ x → Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> x , P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁) ⟩) Q.commute₁ ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (P.π₀ >~> g₀) , P.⟨ f₀ , f₁ ⟩ >~> (Q.⟨ P.π₀ >~> g₀ , P.π₁ >~> g₁ ⟩ >~> Q.π₁) ⟩
 ≡⟨ cong (λ x → Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (P.π₀ >~> g₀) , P.⟨ f₀ , f₁ ⟩ >~> x ⟩) Q.commute₂ ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> (P.π₀ >~> g₀) , P.⟨ f₀ , f₁ ⟩ >~> (P.π₁ >~> g₁) ⟩
 ≡⟨ cong (λ x → Q.⟨ x , P.⟨ f₀ , f₁ ⟩ >~> (P.π₁ >~> g₁) ⟩) (sym (law->~> _ _ _)) ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> P.π₀ >~> g₀ , P.⟨ f₀ , f₁ ⟩ >~> (P.π₁ >~> g₁) ⟩
 ≡⟨ cong (λ x → Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> P.π₀ >~> g₀ , x ⟩) (sym (law->~> _ _ _)) ⟩
  Q.⟨ P.⟨ f₀ , f₁ ⟩ >~> P.π₀ >~> g₀ , P.⟨ f₀ , f₁ ⟩ >~> P.π₁ >~> g₁ ⟩
 ≡⟨ cong (λ x → Q.⟨ x >~> g₀ , P.⟨ f₀ , f₁ ⟩ >~> P.π₁ >~> g₁ ⟩) P.commute₁ ⟩
  Q.⟨ f₀ >~> g₀ , P.⟨ f₀ , f₁ ⟩ >~> P.π₁ >~> g₁ ⟩
 ≡⟨ cong (λ x → Q.⟨ f₀ >~> g₀ , x >~> g₁ ⟩) P.commute₂ ⟩
  Q.⟨ f₀ >~> g₀ , f₁ >~> g₁ ⟩ □

  where module P = Product P
        module Q = Product Q


product-associator : ∀ {A B C} →
                     (P₁ : Product A B) (P₂ : Product B C)
                     (P₃ : Product A (Product.A×B P₂)) (P₄ : Product (Product.A×B P₁) C) →
                     Product.A×B P₃ ≅ Product.A×B P₄
product-associator P₁ P₂ P₃ P₄ =
  record { f = s
         ; iso-witness =
             record { fʳ = t
                    ; inverse = begin
                       s >~> t
                      ≡⟨ P₃.pre-composing-with-tuple s (P₄.π₀ >~> P₁.π₀) (P₂.⟨ P₄.π₀ >~> P₁.π₁ , P₄.π₁ ⟩) ⟩
                       P₃.⟨ s >~> (P₄.π₀ >~> P₁.π₀) , s >~> P₂.⟨ P₄.π₀ >~> P₁.π₁ , P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ s >~> (P₄.π₀ >~> P₁.π₀) , x ⟩) (P₂.pre-composing-with-tuple s (P₄.π₀ >~> P₁.π₁) P₄.π₁) ⟩
                       P₃.⟨ s >~> (P₄.π₀ >~> P₁.π₀) , P₂.⟨ s >~> (P₄.π₀ >~> P₁.π₁) , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ x , P₂.⟨ s >~> (P₄.π₀ >~> P₁.π₁) , s >~> P₄.π₁ ⟩ ⟩) (sym (law->~> _ _ _)) ⟩
                       P₃.⟨ s >~> P₄.π₀ >~> P₁.π₀ , P₂.⟨ s >~> (P₄.π₀ >~> P₁.π₁) , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ s >~> P₄.π₀ >~> P₁.π₀ , P₂.⟨ x , s >~> P₄.π₁ ⟩ ⟩) (sym (law->~> _ _ _)) ⟩
                       P₃.⟨ s >~> P₄.π₀ >~> P₁.π₀ , P₂.⟨ s >~> P₄.π₀ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ x >~> P₁.π₀ , P₂.⟨ s >~> P₄.π₀ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩) P₄.commute₁ ⟩
                       P₃.⟨ P₁.⟨ P₃.π₀ , P₃.π₁ >~> P₂.π₀ ⟩ >~> P₁.π₀ , P₂.⟨ s >~> P₄.π₀ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ x , P₂.⟨ s >~> P₄.π₀ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩) P₁.commute₁ ⟩
                       P₃.⟨ P₃.π₀ , P₂.⟨ s >~> P₄.π₀ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ P₃.π₀ , P₂.⟨ x >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩) P₄.commute₁ ⟩
                       P₃.⟨ P₃.π₀ , P₂.⟨ P₁.⟨ P₃.π₀ , P₃.π₁ >~> P₂.π₀ ⟩ >~> P₁.π₁ , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ P₃.π₀ , P₂.⟨ x , s >~> P₄.π₁ ⟩ ⟩) P₁.commute₂ ⟩
                       P₃.⟨ P₃.π₀ , P₂.⟨ P₃.π₁ >~> P₂.π₀ , s >~> P₄.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ P₃.π₀ , P₂.⟨ P₃.π₁ >~> P₂.π₀ , x ⟩ ⟩) P₄.commute₂ ⟩
                       P₃.⟨ P₃.π₀ , P₂.⟨ P₃.π₁ >~> P₂.π₀ , P₃.π₁ >~> P₂.π₁ ⟩ ⟩
                      ≡⟨ cong (λ x → P₃.⟨ P₃.π₀ , x ⟩) P₂.π-η ⟩
                       P₃.⟨ P₃.π₀ , P₃.π₁ ⟩
                      ≡⟨ P₃.π-id ⟩
                       id~> □

                    ; inverseʳ = begin
                       t >~> s
                      ≡⟨ P₄.pre-composing-with-tuple t (P₁.⟨ P₃.π₀ , P₃.π₁ >~> P₂.π₀ ⟩) (P₃.π₁ >~> P₂.π₁)  ⟩
                       P₄.⟨ t >~> P₁.⟨ P₃.π₀ , P₃.π₁ >~> P₂.π₀ ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ x , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) (P₁.pre-composing-with-tuple t P₃.π₀ (P₃.π₁ >~> P₂.π₀)) ⟩
                       P₄.⟨ P₁.⟨ t >~> P₃.π₀ , t >~> (P₃.π₁ >~> P₂.π₀) ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₁.⟨ x , t >~> (P₃.π₁ >~> P₂.π₀) ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) P₃.commute₁ ⟩
                       P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , t >~> (P₃.π₁ >~> P₂.π₀) ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , x ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) (sym (law->~> _ _ _)) ⟩
                       P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , t >~> P₃.π₁ >~> P₂.π₀ ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , x >~> P₂.π₀ ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) (P₃.commute₂) ⟩
                       P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , P₂.⟨ P₄.π₀ >~> P₁.π₁ , P₄.π₁ ⟩ >~> P₂.π₀ ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , x ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) P₂.commute₁ ⟩
                       P₄.⟨ P₁.⟨ P₄.π₀ >~> P₁.π₀ , P₄.π₀ >~> P₁.π₁ ⟩ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ x , t >~> (P₃.π₁ >~> P₂.π₁) ⟩) P₁.π-η ⟩
                       P₄.⟨ P₄.π₀ , t >~> (P₃.π₁ >~> P₂.π₁) ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₄.π₀ , x ⟩) (sym (law->~> _ _ _)) ⟩
                       P₄.⟨ P₄.π₀ , t >~> P₃.π₁ >~> P₂.π₁ ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₄.π₀ , x >~> P₂.π₁ ⟩) P₃.commute₂ ⟩
                       P₄.⟨ P₄.π₀ , P₂.⟨ P₄.π₀ >~> P₁.π₁ , P₄.π₁ ⟩ >~> P₂.π₁ ⟩
                      ≡⟨ cong (λ x → P₄.⟨ P₄.π₀ , x ⟩) P₂.commute₂ ⟩
                       P₄.⟨ P₄.π₀ , P₄.π₁ ⟩
                      ≡⟨ P₄.π-id ⟩
                       id~> □
                     }
         }
  where module P₁ = Product P₁
        module P₂ = Product P₂
        module P₃ = Product P₃
        module P₄ = Product P₄
        s = P₄.⟨ P₁.⟨ P₃.π₀ , P₃.π₁ >~> P₂.π₀ ⟩ , P₃.π₁ >~> P₂.π₁ ⟩
        t = P₃.⟨ P₄.π₀ >~> P₁.π₀ , P₂.⟨ P₄.π₀ >~> P₁.π₁ , P₄.π₁ ⟩ ⟩


product-unitor : (T : Terminal C) (A : Obj) (P : Product (Terminal.𝟙 T) A) → Product.A×B P ≅ A
product-unitor T A P =
  record { f = π₁
         ; iso-witness =
             record { fʳ = ⟨ ! , id~> ⟩
                    ; inverse = begin
                       π₁ >~> ⟨ ! , id~> ⟩
                      ≡⟨ pre-composing-with-tuple π₁ ! id~> ⟩
                       ⟨ π₁ >~> ! , π₁ >~> id~> ⟩
                      ≡⟨ cong (λ x → ⟨ π₁ >~> ! , x ⟩) (law-id~>ʳ _) ⟩
                       ⟨ π₁ >~> ! , π₁ ⟩
                      ≡⟨ cong (λ x → ⟨ x , π₁ ⟩) (lemma T π₁) ⟩
                       ⟨ ! , π₁ ⟩
                      ≡⟨ cong (λ x → ⟨ x , π₁ ⟩) (sym (!-unique π₀)) ⟩
                       ⟨ π₀ , π₁ ⟩
                      ≡⟨ π-id ⟩
                       id~> □
                    ; inverseʳ = commute₂ }
                    }
  where open Terminal T
        open Product P
        open pre-composing-with-bang

product-symmetry : ∀ {A B} (P₁ : Product A B) (P₂ : Product B A) → Product.A×B P₁ ≅ Product.A×B P₂
product-symmetry P₁ P₂ =
  record { f = P₂.⟨ P₁.π₁ , P₁.π₀ ⟩
         ; iso-witness = record { fʳ = P₁.⟨ P₂.π₁ , P₂.π₀ ⟩
                                ; inverse = begin
                                     P₂.⟨ P₁.π₁ , P₁.π₀ ⟩ >~> P₁.⟨ P₂.π₁ , P₂.π₀ ⟩
                                    ≡⟨ P₁.pre-composing-with-tuple (P₂.⟨ P₁.π₁ , P₁.π₀ ⟩) P₂.π₁ P₂.π₀ ⟩
                                     P₁.⟨ P₂.⟨ P₁.π₁ , P₁.π₀ ⟩ >~> P₂.π₁ , P₂.⟨ P₁.π₁ , P₁.π₀ ⟩ >~> P₂.π₀ ⟩
                                    ≡⟨ cong (λ x → P₁.⟨ x , P₂.⟨ P₁.π₁ , P₁.π₀ ⟩ >~> P₂.π₀ ⟩) P₂.commute₂ ⟩
                                     P₁.⟨ P₁.π₀ , P₂.⟨ P₁.π₁ , P₁.π₀ ⟩ >~> P₂.π₀ ⟩
                                    ≡⟨ cong (λ x → P₁.⟨ P₁.π₀ , x ⟩) P₂.commute₁ ⟩
                                     P₁.⟨ P₁.π₀ , P₁.π₁ ⟩
                                    ≡⟨ P₁.π-id ⟩
                                     id~> □
                                ; inverseʳ = begin
                                    P₁.⟨ P₂.π₁ , P₂.π₀ ⟩ >~> P₂.⟨ P₁.π₁ , P₁.π₀ ⟩
                                   ≡⟨ P₂.pre-composing-with-tuple (P₁.⟨ P₂.π₁ , P₂.π₀ ⟩) P₁.π₁ P₁.π₀ ⟩
                                    P₂.⟨ P₁.⟨ P₂.π₁ , P₂.π₀ ⟩ >~> P₁.π₁ , P₁.⟨ P₂.π₁ , P₂.π₀ ⟩ >~> P₁.π₀ ⟩
                                   ≡⟨ cong (λ x → P₂.⟨ P₁.⟨ P₂.π₁ , P₂.π₀ ⟩ >~> P₁.π₁ , x ⟩) P₁.commute₁ ⟩
                                    P₂.⟨ P₁.⟨ P₂.π₁ , P₂.π₀ ⟩ >~> P₁.π₁ , P₂.π₁ ⟩
                                   ≡⟨ cong (λ x → P₂.⟨ x , P₂.π₁ ⟩) P₁.commute₂ ⟩
                                    P₂.⟨ P₂.π₀ , P₂.π₁ ⟩
                                   ≡⟨ P₂.π-id ⟩
                                    id~> □
                                }
         }
  where module P₁ = Product P₁
        module P₂ = Product P₂

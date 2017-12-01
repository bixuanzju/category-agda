
{-# OPTIONS --type-in-type #-}

module MonicDef where

open import Prelude
open import Categories
open import FunctorDef


----------------------------------------------------------------------------
-- Monic and epic morphisms
----------------------------------------------------------------------------

module Monic-Epic (C : Category) where
  open Category C

  Monic : {A B : Obj} (↣ : A ~> B) → Set
  Monic {A} {B} ↣ = ∀ {C} {f g : C ~> A} → f >~> ↣ ≡ g >~> ↣ → f ≡ g


  Epic : {A B : Obj} (↠ : A ~> B) → Set
  Epic {A} {B} ↠ = ∀ {C} {f g : B ~> C} → ↠ >~> f ≡ ↠ >~> g → f ≡ g

  id-monic : ∀ {T} → Monic (id~> {T})
  id-monic {f = f} {g = g} post = begin
    f
   ≡⟨ sym (law-id~>ʳ _) ⟩
    f >~> id~>
   ≡⟨ post ⟩
    g >~> id~>
   ≡⟨ law-id~>ʳ _ ⟩
    g □

  id-epic : ∀ {T} → Epic (id~> {T})
  id-epic {f = f} {g = g} pre = begin
    f
   ≡⟨ sym (law-id~>ˡ _) ⟩
    id~> >~> f
   ≡⟨ pre ⟩
    id~> >~> g
   ≡⟨ law-id~>ˡ _ ⟩
    g □

  >~>-monic : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Monic m → Monic n → Monic (m >~> n)
  >~>-monic {m = m} {n = n}  ↣m ↣n {f = f} {g = g} post = ↣m (↣n help)
    where help : f >~> m >~> n ≡ g >~> m >~> n
          help = begin
            f >~> m >~> n
           ≡⟨ law->~> _ _ _ ⟩
            f >~> (m >~> n)
           ≡⟨ post ⟩
            g >~> (m >~> n)
           ≡⟨ sym (law->~> _ _ _) ⟩
            g >~> m >~> n □

  >~>-epic : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Epic m → Epic n → Epic (m >~> n)
  >~>-epic {m = m} {n = n}  ↠m ↠n {f = f} {g = g} pre = ↠n (↠m help)
    where help : m >~> (n >~> f) ≡ m >~> (n >~> g)
          help = begin
            m >~> (n >~> f)
           ≡⟨ sym (law->~> _ _ _) ⟩
            m >~> n >~> f
           ≡⟨ pre ⟩
            m >~> n >~> g
           ≡⟨ law->~> _ _ _ ⟩
            m >~> (n >~> g) □

  >~>-monicʳ : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Monic (m >~> n) → Monic m
  >~>-monicʳ {m = m} {n = n} ↣mn {f = f} {g = g} post = ↣mn help
    where help : f >~> (m >~> n) ≡ g >~> (m >~> n)
          help = begin
            f >~> (m >~> n)
           ≡⟨ sym (law->~> _ _ _) ⟩
            f >~> m >~> n
           ≡⟨ whiskerʳ post ⟩
            g >~> m >~> n
           ≡⟨ law->~> _ _ _ ⟩
            g >~> (m >~> n) □

  >~>-epicʳ : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Epic (m >~> n) → Epic n
  >~>-epicʳ {m = m} {n = n} ↠mn {f = f} {g = g} pre = ↠mn help
    where help : m >~> n >~> f ≡ m >~> n >~> g
          help = begin
            m >~> n >~> f
           ≡⟨ law->~> _ _ _ ⟩
            m >~> (n >~> f)
           ≡⟨ whiskerˡ pre ⟩
            m >~> (n >~> g)
           ≡⟨ sym (law->~> _ _ _) ⟩
            m >~> n >~> g □



----------------------------------------------------------------------------
-- Split monic and epic morphisms
----------------------------------------------------------------------------


module Split-Monic-Epic (C : Category) where
  open Category C
  open Monic-Epic C

  record Split-Monic {A B : Obj} (s : A ~> B) : Set where
    field
      r : B ~> A
      post-invert : s >~> r ≡ id~>

  record Split-Epic {A B : Obj} (r : A ~> B) : Set where
    field
      s : B ~> A
      pre-invert : s >~> r ≡ id~>

  split-monic : {A B : Obj} {s : A ~> B} → Split-Monic s → Monic s
  split-monic {A} {B} {s} m {f = f} {g = g} post = begin
      f
     ≡⟨ sym (law-id~>ʳ _) ⟩
      f >~> id~>
     ≡⟨ cong (λ x → f >~> x) (sym post-invert) ⟩
      f >~> (s >~> r)
     ≡⟨ sym (law->~> _ _ _) ⟩
      f >~> s >~> r
     ≡⟨ whiskerʳ post ⟩
      g >~> s >~> r
     ≡⟨ law->~> _ _ _ ⟩
      g >~> (s >~> r)
     ≡⟨ cong (λ x → g >~> x) post-invert ⟩
      g >~> id~>
     ≡⟨ law-id~>ʳ _ ⟩
      g □
    where open Split-Monic m


  split-epic : {A B : Obj} {r : A ~> B} → Split-Epic r → Epic r
  split-epic {A} {B} {r} m {f = f} {g = g} pre = begin
      f
     ≡⟨ sym (law-id~>ˡ _) ⟩
      id~> >~> f
     ≡⟨ cong (λ x → x >~> f) (sym pre-invert) ⟩
      s >~> r >~> f
     ≡⟨ law->~> _ _ _ ⟩
      s >~> (r >~> f)
     ≡⟨ whiskerˡ pre ⟩
      s >~> (r >~> g)
     ≡⟨ sym (law->~> _ _ _) ⟩
      s >~> r >~> g
     ≡⟨ cong (λ x → x >~> g) pre-invert ⟩
      id~> >~> g
     ≡⟨ law-id~>ˡ _ ⟩
      g □
    where open Split-Epic m


module Functor-Split-Monic-Epic {C D : Category} (F : C => D)where
  open Category
  open Split-Monic-Epic
  open _=>_ F

  F-split-monic : {A B : Obj C} {s : _~>_ C A B} →
                  Split-Monic C s →
                  Split-Monic D (𝔽₁ s)
  F-split-monic {A} {B} {s} m =
    record { r = 𝔽₁ r
           ; post-invert = begin
               _>~>_ D (𝔽₁ s) (𝔽₁ r)
              ≡⟨ sym (F-map->~> s r) ⟩
               𝔽₁ (_>~>_ C s r)
              ≡⟨ cong (λ x → 𝔽₁ x) post-invert ⟩
               𝔽₁ (id~> C)
              ≡⟨ F-map-id~> ⟩
               id~> D □
           }
    where open Split-Monic m

  F-split-epic : {A B : Obj C} {r : _~>_ C A B} →
                  Split-Epic C r →
                  Split-Epic D (𝔽₁ r)
  F-split-epic {A} {B} {r} m =
    record { s = 𝔽₁ s
           ; pre-invert = begin
               _>~>_ D (𝔽₁ s) (𝔽₁ r)
              ≡⟨ sym (F-map->~> s r) ⟩
               𝔽₁ (_>~>_ C s r)
              ≡⟨ cong (λ x → 𝔽₁ x) pre-invert ⟩
               𝔽₁ (id~> C)
              ≡⟨ F-map-id~> ⟩
               id~> D □
           }
    where open Split-Epic m


----------------------------------------------------------------------------
-- Isomorphisms
----------------------------------------------------------------------------


module Iso (C : Category) where
  open Category C

  record have-section {A B : Obj} (r : B ~> A) : Set where
    field
      s : A ~> B
      section : s >~> r ≡ id~>

  record have-retraction {A B : Obj} (s : A ~> B) : Set where
    field
      r : B ~> A
      retraction : s >~> r ≡ id~>

  sec≡retrac : {A B : Obj} {f : A ~> B}
               {s : have-section f} {r : have-retraction f} →
               have-section.s s ≡ have-retraction.r r
  sec≡retrac {f = f} {record { s = s ; section = section }}
                     {record { r = r ; retraction = retraction }} = begin
             s
            ≡⟨ sym (law-id~>ʳ _) ⟩
             s >~> id~>
            ≡⟨ sym (whiskerˡ retraction) ⟩
             s >~> (f >~> r)
            ≡⟨ sym (law->~> _ _ _) ⟩
             s >~> f >~> r
            ≡⟨ whiskerʳ section ⟩
             id~> >~> r
            ≡⟨ law-id~>ˡ _ ⟩
             r □

  record isomorphism {A B : Obj} (f : A ~> B) : Set where
    field
      fʳ : B ~> A
      inverse  : f >~> fʳ ≡ id~>
      inverseʳ : fʳ >~> f ≡ id~>


  record _≅_ (A B : Obj) : Set where
    field
      f : A ~> B
      iso-witness : isomorphism f

  iso-refl : {A : Obj} → A ≅ A
  iso-refl = record { f = id~> ; iso-witness = record { fʳ = id~> ; inverse = law-id~>ʳ _ ; inverseʳ = law-id~>ʳ _ } }

  iso-sym : {A B : Obj} → A ≅ B → B ≅ A
  iso-sym record { f = f ; iso-witness = record { fʳ = fʳ ; inverse = inverse ; inverseʳ = inverseʳ } } =
    record { f = fʳ ; iso-witness = record { fʳ = f ; inverse = inverseʳ ; inverseʳ = inverse } }

  iso-trans : {A B C : Obj} → A ≅ B → B ≅ C → A ≅ C
  iso-trans record { f = f₁ ; iso-witness = record { fʳ = fʳ₁ ; inverse = inverse₁ ; inverseʳ = inverseʳ₁ } }
            record { f = f₂ ; iso-witness = record { fʳ = fʳ₂ ; inverse = inverse₂ ; inverseʳ = inverseʳ₂ } } =
     record { f = f₁ >~> f₂
            ; iso-witness =
                record { fʳ = fʳ₂ >~> fʳ₁
                       ; inverse = begin
                           f₁ >~> f₂ >~> (fʳ₂ >~> fʳ₁)
                          ≡⟨ law->~> _ _ _ ⟩
                           f₁ >~> (f₂ >~> (fʳ₂ >~> fʳ₁))
                          ≡⟨ whiskerˡ (sym (law->~> _ _ _)) ⟩
                           f₁ >~> (f₂ >~> fʳ₂ >~> fʳ₁)
                          ≡⟨ cong (λ x → f₁ >~> (x >~> fʳ₁)) inverse₂ ⟩
                           f₁ >~> (id~> >~> fʳ₁)
                          ≡⟨ whiskerˡ (law-id~>ˡ _) ⟩
                           f₁ >~> fʳ₁
                          ≡⟨ inverse₁ ⟩
                           id~> □
                       ; inverseʳ = begin
                           fʳ₂ >~> fʳ₁ >~> (f₁ >~> f₂)
                          ≡⟨ law->~> _ _ _ ⟩
                           fʳ₂ >~> (fʳ₁ >~> (f₁ >~> f₂))
                          ≡⟨ whiskerˡ (sym (law->~> _ _ _)) ⟩
                           fʳ₂ >~> (fʳ₁ >~> f₁ >~> f₂)
                          ≡⟨ cong (λ x → fʳ₂ >~> (x >~> f₂)) inverseʳ₁ ⟩
                           fʳ₂ >~> (id~> >~> f₂)
                          ≡⟨ whiskerˡ (law-id~>ˡ _) ⟩
                           fʳ₂ >~> f₂
                          ≡⟨ inverseʳ₂ ⟩
                           id~> □
                       }
            }

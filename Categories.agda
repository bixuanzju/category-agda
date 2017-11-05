{-# OPTIONS --type-in-type #-}

module Categories where

open import Prelude

record Category : Set where
  infixr 3 _>~>_
  field
    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj → Obj → Set    -- "arrows" or "morphisms"

    -- two operations
    id~>        : {T : Obj} →      T ~> T
    _>~>_       : {R S T : Obj} →  R ~> S → S ~> T → R ~> T

    -- Composition left unit law
    law-id~>>~> : {S T : Obj}     (f : S ~> T) → id~> >~> f ≡ f
    -- Composition right unit law
    law->~>id~> : {S T : Obj}     (f : S ~> T) → f >~> id~> ≡ f
    -- Composition associative law
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) → (f >~> g) >~> h ≡ f >~> (g >~> h)


  -- The so-called whiskering
  whiskerl : {A B C : Obj} {g1 g2 : B ~> C} {f : A ~> B}  → g1 ≡ g2 → f >~> g1 ≡ f >~> g2
  whiskerl {f = f} refl = refl

  whiskerr : {B C D : Obj} {g1 g2 : B ~> C} {h : C ~> D}  → g1 ≡ g2 → g1 >~> h ≡ g2 >~> h
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
        ; _~>_ = λ _ _ → One
        ; id~> = <>
        ; _>~>_ = λ _ _ → <>
        ; law-id~>>~> = idOne
        ; law->~>id~> = idOne
        ; law->~>>~> = λ _ _ _ → refl
        } where
        idOne : (f : One) → f ≡ <>
        idOne <> = refl


record Preorder (X : Set) : Set where
  infixl 5 _≤_
  field
    _≤_ : X → X → Set
    ≤-refl : (x : X) → x ≤ x
    ≤-trans : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
    ≤-unique : {x y : X} → (p q : x ≤ y) → p ≡ q
open Preorder {{...}} public

-- Preorder is a category
PREORDER : {X : Set} {{m : Preorder X}} → Category
PREORDER {X} {{m}} = record
             { Obj = X
             ; _~>_ = _≤_
             ; id~> = λ {x} → ≤-refl x
             ; _>~>_ = λ f g → ≤-trans {{m}} f g
             ; law-id~>>~> = λ f → ≤-unique {{m}} _ _
             ; law->~>id~> = λ f → ≤-unique  {{m}} _ _
             ; law->~>>~> = λ f g h → ≤-unique {{m}} _ _
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

SomeMonoid : Set
SomeMonoid = Sg Set Monoid


-- Monoid is a category
MONOID : SomeMonoid → Category
MONOID (X , m)
  = let instance
          _ : Monoid X
          _ = m
    in record
       { Obj = One
       ; _~>_ = λ _ _ → X
       ; id~> = ε
       ; _>~>_ = _⋆_
       ; law-id~>>~> = absorbL
       ; law->~>id~> = absorbR
       ; law->~>>~> = assoc
       }


-- The category of sets
SET : Category
SET = record
        { Obj = Set
        ; _~>_ = λ S T → S → T
        ; id~> = id
        ; _>~>_ = _>>_
        ; law-id~>>~> = λ _ → refl
        ; law->~>id~> = λ _ → refl
        ; law->~>>~> = λ _ _ _ → refl
        }

-- Monotone
record Monotone {X} {{MX : Preorder X}} {Y} {{MY : Preorder Y}} (f : X  → Y) : Set where
  field
    resp≤ : ∀ {x x'} → x ≤ x' → f x ≤ f x'


SomePreorder : Set
SomePreorder = Sg Set Preorder

-- The category of preorders
Cat-Preorder : Category
Cat-Preorder = record
             { Obj = SomePreorder
             ; _~>_ = λ m n → Prf (fst m → fst n) λ f → Monotone {{snd m}} {{snd n}} f
             ; id~> = id , record { resp≤ = id }
             ; _>~>_ = mcom
             ; law-id~>>~> = λ _ → refl
             ; law->~>id~> = λ _ → refl
             ; law->~>>~> = λ _ _ _ → refl
             } where
             mcom : {R S T : Sg Set Preorder} →
                    Prf (fst R → fst S) (λ f → Monotone {{snd R}} {{snd S}} f) →
                    Prf (fst S → fst T) (λ f → Monotone {{snd S}} {{snd T}} f) →
                    Prf (fst R → fst T) (λ f → Monotone {{snd R}} {{snd T}} f)
             mcom {R , m} {S , n} {T , s} (f , fm) (g , gm)
                   = let instance
                           -- Bring instances into scope
                           _ : Preorder S
                           _ = n
                           _ : Preorder R
                           _ = m
                           _ : Preorder T
                           _ = s
                     in f >> g , record { resp≤ = λ {x y} x≤y → Monotone.resp≤ gm (Monotone.resp≤ fm x≤y) }


-- Monoid homomorphism
record MonoidHom {X} {{MX : Monoid X}} {Y} {{MY : Monoid Y}} (f : X  → Y) : Set where
  field
    respε : f ε ≡ ε
    resp⋆ : ∀ x x' → f (x ⋆ x') ≡ f x ⋆ f x'

-- The category of monoids
CAT-MONOID : Category
CAT-MONOID  = record
               { Obj = SomeMonoid
               ; _~>_ = λ m n → Prf (fst m → fst n) λ f → MonoidHom {{snd m}} {{snd n}} f
               ; id~> = id , record { respε = refl ; resp⋆ = λ _ _ → refl }
               ; _>~>_ = mcom
               ; law-id~>>~> = λ _ → refl
               ; law->~>id~> = λ _ → refl
               ; law->~>>~> = λ _ _ _ → refl
               } where
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
                     f >> g , record { respε = g (f ε)    ≡⟨ cong g (MonoidHom.respε fm) ⟩
                                               g ε        ≡⟨ MonoidHom.respε gm ⟩
                                               ε
                                               □
                                     ; resp⋆ = λ a b → g (f (a ⋆ b))     ≡⟨ cong g (MonoidHom.resp⋆ fm a b) ⟩
                                                       g (f a ⋆ f b)     ≡⟨ MonoidHom.resp⋆ gm (f a) (f b) ⟩
                                                       g (f a) ⋆ g (f b)
                                                       □
                                     }



module FUNCTOR where
  open Category
  -- Functor from C to D
  record _=>_ (C D : Category) : Set where
    field
      -- Two mappings
      𝔽₀ : Obj C → Obj D
      𝔽₁ : {S T : Obj C} → _~>_ C S T → _~>_ D (𝔽₀ S) (𝔽₀ T)

      -- Two laws
      F-map-id~> : {T : Obj C} → 𝔽₁ (id~> C {T}) ≡ id~> D {𝔽₀ T}
      F-map->~> : {R S T : Obj C} (f : _~>_ C R S) (g : _~>_ C S T) →
                  𝔽₁ (_>~>_ C f g) ≡ _>~>_ D (𝔽₁ f) (𝔽₁ g)

open FUNCTOR public


-- Identity functor
Functor-id : ∀ {C} → C => C
Functor-id = record { 𝔽₀ = id ; 𝔽₁ = id ; F-map-id~> = refl ; F-map->~> = λ _ _ → refl }


-- Functor composition
module FUNCTOR-CP {C D E : Category} where
  open _=>_
  open Category

  _>=>_ : C => D → D => E → C => E
  𝔽₀ (F >=> G) = 𝔽₀ F >> 𝔽₀ G
  𝔽₁ (F >=> G) = 𝔽₁ F >> 𝔽₁ G
  F-map-id~> (F >=> G) = 𝔽₁ G (𝔽₁ F (id~> C))         ≡⟨ cong (𝔽₁ G) (F-map-id~> F) ⟩
                         𝔽₁ G (id~> D)                ≡⟨ F-map-id~> G ⟩
                         id~> E
                         □
  F-map->~> (F >=> G) f g =  𝔽₁ G (𝔽₁ F (_>~>_ C f g))                      ≡⟨ cong (𝔽₁ G) (F-map->~> F f g) ⟩
                             𝔽₁ G (_>~>_ D (𝔽₁ F f) (𝔽₁ F g))               ≡⟨ F-map->~> G (𝔽₁ F f) (𝔽₁ F g) ⟩
                             _>~>_ E (𝔽₁ G (𝔽₁ F f)) (𝔽₁ G (𝔽₁ F g))
                             □


open FUNCTOR-CP public


-- Functor (extensional) equivalence:
-- 𝔽₀ ≡ 𝔾₀
-- 𝔽₁ ≡ 𝔾₁
-- F-map-id~> ≡ G-map-id~>
-- F-map->~> ≡ G-map->~>
Functor≡ : {C D : Category} (F G : C => D) → Set
Functor≡ {C} {D}
  record { 𝔽₀ = 𝔽₀ ; 𝔽₁ = 𝔽₁ ; F-map-id~> = F-map-id~> ; F-map->~> = F-map->~> }
  record { 𝔽₀ = 𝔾₀ ; 𝔽₁ = 𝔾₁ ; F-map-id~> = G-map-id~> ; F-map->~> = G-map->~> }
  = Sg (𝔽₀ ≡ 𝔾₀)
       λ { refl  → -- Patterns lambdas
         Sg (_≡_ {∀ {S T : Category.Obj C} → (C Category.~> S) T → (D Category.~> 𝔽₀ S) (𝔾₀ T)} 𝔽₁ 𝔾₁)
            λ { refl →
                _≡_ {forall {T : Category.Obj C} → 𝔽₁ (Category.id~> C {T}) ≡ Category.id~> D} F-map-id~> G-map-id~>
                *
                _≡_ {forall {R S T : Category.Obj C} (f : (C Category.~> R) S) (g : (C Category.~> S) T) →
                     𝔽₁ ((C Category.>~> f) g) ≡ (D Category.>~> 𝔽₁ f) (𝔽₁ g)}
                     F-map->~>  G-map->~>
              }
         }

-- Functor equivalence implies propositional equivalence
Functor≡→≡ : {C D : Category}{F G : C => D} → Functor≡ F G → F ≡ G
Functor≡→≡ (refl , (refl , (refl , refl)))  = refl


-- The category of categories
CATEGORY : Category
CATEGORY = record
             { Obj = Category
             ; _~>_ =  _=>_
             ; id~> = Functor-id
             ; _>~>_ = _>=>_
             ; law-id~>>~> =
               λ F → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                 extensionality' λ x →
                   extensionality' λ y →
                     extensionality' λ z →
                       extensionality λ g → extensionality λ h → eqUnique _ _)
             ; law->~>id~> =
               λ F → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                   extensionality' λ x →
                     extensionality' λ y →
                       extensionality' λ z → extensionality λ g → extensionality λ h → eqUnique _ _)
             ; law->~>>~> =
               λ F G H → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                   extensionality' λ x →
                     extensionality' λ y →
                       extensionality' λ z →
                         extensionality λ g → extensionality λ h → eqUnique _ _)
             } where open _=>_


-- A forgetful functor
U : {m : SomeMonoid} → MONOID m => SET
U {X , mon} =
  let instance
        _ : Monoid X
        _ = mon
  in record { 𝔽₀ = λ _ → X ; 𝔽₁ = λ x y → y ⋆ x -- note the order
            ; F-map-id~> = extensionality absorbR
            ; F-map->~> = λ x y → extensionality λ z → sym (assoc z x y)
            }

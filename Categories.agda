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
                       f >> g # record { respε = g (f ε)    ≡⟨ cong g (MonoidHom.respε fm) ⟩
                                                 g ε        ≡⟨ MonoidHom.respε gm ⟩
                                                 ε
                                                 □
                                       ; resp⋆ = λ a b → g (f (a ⋆ b))     ≡⟨ cong g (MonoidHom.resp⋆ fm a b) ⟩
                                                         g (f a ⋆ f b)     ≡⟨ MonoidHom.resp⋆ gm (f a) (f b) ⟩
                                                         g (f a) ⋆ g (f b)
                                                         □
                                       }
                        }
               ; law-id~>ˡ = λ _ → refl
               ; law-id~>ʳ = λ _ → refl
               ; law->~> = λ _ _ _ → refl
               }


----------------------------------------------------------------------------
-- Categories of categories
----------------------------------------------------------------------------

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
  = Σ (𝔽₀ ≡ 𝔾₀)
       λ { refl  → -- Patterns lambdas
         Σ (_≡_ {∀ {S T : Category.Obj C} → (C Category.~> S) T → (D Category.~> 𝔽₀ S) (𝔾₀ T)} 𝔽₁ 𝔾₁)
            λ { refl →
                _≡_ {forall {T : Category.Obj C} → 𝔽₁ (Category.id~> C {T}) ≡ Category.id~> D} F-map-id~> G-map-id~>
                ×
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
             ; law-id~>ˡ =
               λ F → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                 extensionality' λ x →
                   extensionality' λ y →
                     extensionality' λ z →
                       extensionality λ g → extensionality λ h → eqUnique _ _)
             ; law-id~>ʳ =
               λ F → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                   extensionality' λ x →
                     extensionality' λ y →
                       extensionality' λ z → extensionality λ g → extensionality λ h → eqUnique _ _)
             ; law->~> =
               λ F G H → Functor≡→≡ (refl , refl ,
                 extensionality' (λ x → eqUnique _ _) ,
                   extensionality' λ x →
                     extensionality' λ y →
                       extensionality' λ z →
                         extensionality λ g → extensionality λ h → eqUnique _ _)
             } where open _=>_


-- A forgetful functor
U : ∀ {X} {{m : Monoid X}} → MONOID {{m}} => SET
U {X} = record { 𝔽₀ = λ _ → X
               ; 𝔽₁ = λ x y →  y ⋆ x
               ; F-map-id~> = extensionality absorbR
               ; F-map->~> = λ x y → extensionality λ z → sym (assoc z x y)
               }


-- A representable functor
module Rep (C : Category) where
  open Category C

  ℂₓ : (X : Obj) → C => SET
  ℂₓ X = record { 𝔽₀ = λ A → X ~> A  ; 𝔽₁ = λ f g → g >~> f
                ; F-map-id~> = extensionality λ x → law-id~>ʳ _
                ; F-map->~> = λ f g → extensionality λ x → sym (law->~> x f g)
                }


----------------------------------------------------------------------------
-- New categories from old
----------------------------------------------------------------------------

-- Opposite categories
_op : Category → Category
C op = record
         { Obj = Obj
         ; _~>_ = λ x y → y ~> x
         ; id~> = id~>
         ; _>~>_ = λ f g → g >~> f
         ; law-id~>ˡ = λ f → law-id~>ʳ f
         ; law-id~>ʳ = λ f → law-id~>ˡ f
         ; law->~> = λ f g h → sym (law->~> h g f)
         } where open Category C


-- Arrow categories
module ArrowCat (C : Category) where
  open Category C

  record ArrowObj : Set where
    constructor arrobj
    field
      {A} : Obj
      {B} : Obj
      arr : A ~> B

  record Arrow~> (X Y : ArrowObj) : Set where
    constructor arrarr
    module X = ArrowObj X
    module Y = ArrowObj Y
    f : X.A ~> X.B
    f = X.arr
    g : Y.A ~> Y.B
    g = Y.arr
    field
      i : X.A ~> Y.A
      j : X.B ~> Y.B
      .commuteSquare : i >~> g ≡ f >~> j


  Arrow~>-≡ : ∀ {X Y} → {f g : Arrow~> X Y} → Arrow~>.i f ≡ Arrow~>.i g → Arrow~>.j f ≡ Arrow~>.j g → f ≡ g
  Arrow~>-≡ {f = arrarr _ _ _} {arrarr _ _ _} eq1 eq2 rewrite eq1 | eq2 = refl

  arrow : Category
  arrow = record
            { Obj = ArrowObj
            ; _~>_ = Arrow~>
            ; id~> = λ { {arrobj {A} {B} f} →
                   arrarr (id~> {A}) (id~> {B})
                          ( id~> >~> f            ≡⟨ law-id~>ˡ _ ⟩
                            f                      ⟨ law-id~>ʳ _ ⟩≡
                            f >~> id~>
                            □
                          )
                   }
            ; _>~>_ = λ { {arrobj {A} {B} f} {arrobj {C} {D} g} {arrobj {E} {F} h} ij kl →
                    let i : A ~> C
                        i = Arrow~>.i ij
                        j : B ~> D
                        j = Arrow~>.j ij
                        k : C ~> E
                        k = Arrow~>.i kl
                        l : D ~> F
                        l = Arrow~>.j kl
                    in arrarr (i >~> k) (j >~> l)
                              ( i >~> k >~> h                ≡⟨ law->~> i k h ⟩
                                i >~> (k >~> h)              ≡⟨ whiskerˡ (Arrow~>.commuteSquare kl) ⟩
                                i >~> (g >~> l)               ⟨ law->~> i g l ⟩≡
                                i >~> g >~> l                ≡⟨ whiskerʳ (Arrow~>.commuteSquare ij) ⟩
                                f >~> j >~> l                ≡⟨ law->~> f j l ⟩
                                f >~> (j >~> l)
                                □
                              )

                    }
            ; law-id~>ˡ = λ f → Arrow~>-≡ (law-id~>ˡ _) (law-id~>ˡ _)
            ; law-id~>ʳ = λ f → Arrow~>-≡ (law-id~>ʳ _) (law-id~>ʳ _)
            ; law->~> = λ f g h → Arrow~>-≡ (law->~> _ _ _) (law->~> _ _ _)
            }


  -- Domain functor
  dom-functor : arrow => C
  dom-functor = record { 𝔽₀ = ArrowObj.A ; 𝔽₁ = Arrow~>.i ; F-map-id~> = refl ; F-map->~> = λ _ _ → refl }

  -- reflexivity functor
  refl-functor : C => arrow
  refl-functor =
    record { 𝔽₀ = λ x → arrobj (id~> {x})
           ; 𝔽₁ = λ x → arrarr x x (x >~> id~> ≡⟨ law-id~>ʳ x ⟩ x ⟨ law-id~>ˡ x ⟩≡ id~> >~> x □)
           ; F-map-id~> = refl
           ; F-map->~> = λ f g → refl
           }

  -- codomain functor
  cod-functor : arrow => C
  cod-functor = record { 𝔽₀ = ArrowObj.B ; 𝔽₁ = Arrow~>.j ; F-map-id~> = refl ; F-map->~> = λ _ _ → refl }



-- Slice categories
module SliceCat (C : Category) (A : Category.Obj C) where
  open Category C

  record SliceObj : Set where
    constructor sliceobj
    field
      {B} : Obj
      arr : B ~> A


  record Slice~> (X Y : SliceObj) : Set where
    constructor slicearr
    module X = SliceObj X
    module Y = SliceObj Y
    field
      p : X.B ~> Y.B
      .commuteTri : p >~> Y.arr ≡ X.arr

  Arrow~>-≡ : ∀ {X Y} → {f g : Slice~> X Y} → Slice~>.p f ≡ Slice~>.p g → f ≡ g
  Arrow~>-≡ {f = slicearr _ _} {g = slicearr _ _} eq rewrite eq  = refl

  slice : Category
  slice = record
            { Obj = SliceObj
            ; _~>_ = Slice~>
            ; id~> = slicearr id~> (law-id~>ˡ _)
            ; _>~>_ =
              λ { {sliceobj r} {sliceobj s} {sliceobj t} (slicearr f f-prf) (slicearr g g-prf) →
                  slicearr (f >~> g)
                         ( f >~> g >~> t           ≡⟨ law->~> _ _ _ ⟩
                           f >~> (g >~> t)         ≡⟨ whiskerˡ g-prf ⟩
                           f >~> s                 ≡⟨ f-prf ⟩
                           r
                           □
                         )
                }
            ; law-id~>ˡ = λ _ → Arrow~>-≡ (law-id~>ˡ _)
            ; law-id~>ʳ = λ _ → Arrow~>-≡ (law-id~>ʳ _)
            ; law->~> = λ _ _ _ → Arrow~>-≡ (law->~> _ _ _)
            }


module Post-Composition-Functor {C : Category} {A B : Category.Obj C} (f : Category._~>_ C A B) where
  open Category C
  module C/A = SliceCat C A
  module C/B = SliceCat C B

  f! : C/A.slice => C/B.slice
  f! = record { 𝔽₀ = λ { (C/A.SliceObj.sliceobj x) → C/B.SliceObj.sliceobj (x >~> f) }
              ; 𝔽₁ = λ { {C/A.SliceObj.sliceobj x} {C/A.SliceObj.sliceobj y}  (C/A.Slice~>.slicearr p p-prf) →
                          C/B.slicearr p ( p >~> (y >~> f)       ⟨ law->~> _ _ _ ⟩≡
                                           p >~> y >~> f        ≡⟨ whiskerʳ p-prf ⟩
                                           x >~> f
                                           □
                                         )
                       }
              ; F-map-id~> = refl
              ; F-map->~> = λ _ _ → refl }


----------------------------------------------------------------------------
-- Monic and epic morphisms
----------------------------------------------------------------------------

module Monic-Epic {C : Category} where
  open Category C

  Monic : {A B : Obj} (↣ : A ~> B) → Set
  Monic {A} {B} ↣ = ∀ {C} {f g : C ~> A} → f >~> ↣ ≡ g >~> ↣ → f ≡ g


  Epic : {A B : Obj} (↠ : A ~> B) → Set
  Epic {A} {B} ↠ = ∀ {C} {f g : B ~> C} → ↠ >~> f ≡ ↠ >~> g → f ≡ g

  id-monic : ∀ {T} → Monic (id~> {T})
  id-monic {f = f} {g = g} post = f              ⟨ law-id~>ʳ _ ⟩≡
                                  f >~> id~>    ≡⟨ post ⟩
                                  g >~> id~>    ≡⟨ law-id~>ʳ _ ⟩
                                  g
                                  □

  id-epic : ∀ {T} → Epic (id~> {T})
  id-epic {f = f} {g = g} pre = f              ⟨ law-id~>ˡ _ ⟩≡
                                id~> >~> f    ≡⟨ pre ⟩
                                id~> >~> g    ≡⟨ law-id~>ˡ _ ⟩
                                g
                                □

  >~>-monic : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Monic m → Monic n → Monic (m >~> n)
  >~>-monic {m = m} {n = n}  ↣m ↣n {f = f} {g = g} post = ↣m (↣n help)
    where help : f >~> m >~> n ≡ g >~> m >~> n
          help = f >~> m >~> n        ≡⟨ law->~> _ _ _ ⟩
                 f >~> (m >~> n)      ≡⟨ post ⟩
                 g >~> (m >~> n)       ⟨ law->~> _ _ _ ⟩≡
                 g >~> m >~> n
                 □

  >~>-epic : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Epic m → Epic n → Epic (m >~> n)
  >~>-epic {m = m} {n = n}  ↠m ↠n {f = f} {g = g} pre = ↠n (↠m help)
    where help : m >~> (n >~> f) ≡ m >~> (n >~> g)
          help = m >~> (n >~> f) ⟨ law->~> _ _ _ ⟩≡
                 m >~> n >~> f ≡⟨ pre ⟩
                 m >~> n >~> g ≡⟨ law->~> _ _ _ ⟩
                 m >~> (n >~> g)
                 □

  >~>-monicʳ : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Monic (m >~> n) → Monic m
  >~>-monicʳ {m = m} {n = n} ↣mn {f = f} {g = g} post = ↣mn help
    where help : f >~> (m >~> n) ≡ g >~> (m >~> n)
          help = f >~> (m >~> n) ⟨ law->~> _ _ _ ⟩≡
                 f >~> m >~> n ≡⟨ whiskerʳ post ⟩
                 g >~> m >~> n ≡⟨ law->~> _ _ _ ⟩
                 g >~> (m >~> n)
                 □

  >~>-epicʳ : ∀ {A B C} {m : A ~> B} {n : B ~> C} → Epic (m >~> n) → Epic n
  >~>-epicʳ {m = m} {n = n} ↠mn {f = f} {g = g} pre = ↠mn help
    where help : m >~> n >~> f ≡ m >~> n >~> g
          help = m >~> n >~> f ≡⟨ law->~> _ _ _ ⟩
                 m >~> (n >~> f) ≡⟨ whiskerˡ pre ⟩
                 m >~> (n >~> g) ⟨ law->~> _ _ _ ⟩≡
                 m >~> n >~> g
                 □



----------------------------------------------------------------------------
-- Split monic and epic morphisms
----------------------------------------------------------------------------


module Split-Monic-Epic {C : Category} where
  open Category C
  open Monic-Epic {C}

  record Split-Monic {A B : Obj} (s : A ~> B) : Set where
    field
      r : B ~> A
      post-invert : s >~> r ≡ id~>

  record Split-Epic {A B : Obj} (r : A ~> B) : Set where
    field
      s : B ~> A
      pre-invert : s >~> r ≡ id~>

  split-monic : {A B : Obj} {s : A ~> B} → Split-Monic s → Monic s
  split-monic {A} {B} {s} m {f = f} {g = g} post =
      f                         ⟨ law-id~>ʳ _ ⟩≡
      f >~> id~>               ≡⟨ cong (λ x → f >~> x) (sym post-invert) ⟩
      f >~> (s >~> r)           ⟨ law->~> _ _ _ ⟩≡
      f >~> s >~> r            ≡⟨ whiskerʳ post ⟩
      g >~> s >~> r            ≡⟨ law->~> _ _ _ ⟩
      g >~> (s >~> r)          ≡⟨ cong (λ x → g >~> x) post-invert ⟩
      g >~> id~>               ≡⟨ law-id~>ʳ _ ⟩
      g
      □
    where open Split-Monic m


  split-epic : {A B : Obj} {r : A ~> B} → Split-Epic r → Epic r
  split-epic {A} {B} {r} m {f = f} {g = g} pre =
      f                         ⟨ law-id~>ˡ _ ⟩≡
      id~> >~> f               ≡⟨ cong (λ x → x >~> f) (sym pre-invert) ⟩
      s >~> r >~> f            ≡⟨ law->~> _ _ _ ⟩
      s >~> (r >~> f)          ≡⟨ whiskerˡ pre ⟩
      s >~> (r >~> g)           ⟨ law->~> _ _ _ ⟩≡
      s >~> r >~> g            ≡⟨ cong (λ x → x >~> g) pre-invert ⟩
      id~> >~> g               ≡⟨ law-id~>ˡ _ ⟩
      g
      □
    where open Split-Epic m


module Functor-Split-Monic-Epic {C D : Category} (F : C => D)where
  open Category
  open Split-Monic-Epic
  open _=>_ F

  F-split-monic : {A B : Obj C} {s : _~>_ C A B} →
                  Split-Monic {C} s →
                  Split-Monic {D} (𝔽₁ s)
  F-split-monic {A} {B} {s} m =
    record { r = 𝔽₁ r
           ; post-invert =  _>~>_ D (𝔽₁ s) (𝔽₁ r)     ⟨ F-map->~> s r ⟩≡
                            𝔽₁ (_>~>_ C s r)         ≡⟨ cong (λ x → 𝔽₁ x) post-invert ⟩
                            𝔽₁ (id~> C)              ≡⟨ F-map-id~> ⟩
                            id~> D
                            □
           }
    where open Split-Monic m

  F-split-epic : {A B : Obj C} {r : _~>_ C A B} →
                  Split-Epic {C} r →
                  Split-Epic {D} (𝔽₁ r)
  F-split-epic {A} {B} {r} m =
    record { s = 𝔽₁ s
           ; pre-invert =  _>~>_ D (𝔽₁ s) (𝔽₁ r)     ⟨ F-map->~> s r ⟩≡
                            𝔽₁ (_>~>_ C s r)         ≡⟨ cong (λ x → 𝔽₁ x) pre-invert ⟩
                            𝔽₁ (id~> C)              ≡⟨ F-map-id~> ⟩
                            id~> D
                            □
           }
    where open Split-Epic m


----------------------------------------------------------------------------
-- Isomorphisms
----------------------------------------------------------------------------


module Iso {C : Category} where
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
                     {record { r = r ; retraction = retraction }} =
             s                ⟨ law-id~>ʳ _ ⟩≡
             s >~> id~>       ⟨ whiskerˡ retraction ⟩≡
             s >~> (f >~> r)  ⟨ law->~> _ _ _ ⟩≡
             s >~> f >~> r   ≡⟨ whiskerʳ section ⟩
             id~> >~> r      ≡⟨ law-id~>ˡ _ ⟩
             r
             □

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
            ; iso-witness = record { fʳ = fʳ₂ >~> fʳ₁
                                   ; inverse = f₁ >~> f₂ >~> (fʳ₂ >~> fʳ₁)   ≡⟨ law->~> _ _ _ ⟩
                                               f₁ >~> (f₂ >~> (fʳ₂ >~> fʳ₁)) ≡⟨ whiskerˡ (sym (law->~> _ _ _)) ⟩
                                               f₁ >~> (f₂ >~> fʳ₂ >~> fʳ₁)   ≡⟨ cong (λ x → f₁ >~> (x >~> fʳ₁)) inverse₂ ⟩
                                               f₁ >~> (id~> >~> fʳ₁)         ≡⟨ whiskerˡ (law-id~>ˡ _) ⟩
                                               f₁ >~> fʳ₁                    ≡⟨ inverse₁ ⟩
                                               id~>
                                               □
                                   ; inverseʳ = fʳ₂ >~> fʳ₁ >~> (f₁ >~> f₂)    ≡⟨ law->~> _ _ _ ⟩
                                                fʳ₂ >~> (fʳ₁ >~> (f₁ >~> f₂))  ≡⟨ whiskerˡ (sym (law->~> _ _ _)) ⟩
                                                fʳ₂ >~> (fʳ₁ >~> f₁ >~> f₂)    ≡⟨ cong (λ x → fʳ₂ >~> (x >~> f₂)) inverseʳ₁ ⟩
                                                fʳ₂ >~> (id~> >~> f₂)          ≡⟨ whiskerˡ (law-id~>ˡ _) ⟩
                                                fʳ₂ >~> f₂                     ≡⟨ inverseʳ₂ ⟩
                                                id~>
                                                □
                                   }
            }



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
  ⊤-id f = f    ≡⟨ !-unique f ⟩
           !     ⟨ !-unique id~> ⟩≡
           id~>
           □

module terminals-up-to-iso {C : Category} {T R : Terminal C} where

  open Category C
  open Terminal
  open Iso {C}

  up-to-iso : (𝟙 T) ≅ (𝟙 R)
  up-to-iso = record { f = ! R  ; iso-witness = record { fʳ = ! T ; inverse = ⊤-id T _ ; inverseʳ = ⊤-id R _ } }



module pre-composing-with-bang {C : Category} {T : Terminal C} where
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
  ⊥-id f = f    ≡⟨ !-unique f ⟩
           !     ⟨ !-unique id~> ⟩≡
           id~>
           □

module initials-up-to-iso {C : Category} {T R : Initial C} where

  open Category C
  open Initial
  open Iso {C}

  up-to-iso : (𝟘 T) ≅ (𝟘 R)
  up-to-iso = record { f = ! T ; iso-witness = record { fʳ = ! R ; inverse = ⊥-id T _ ; inverseʳ = ⊥-id R _ } }



module post-composing-with-bang {C : Category} {T : Initial C} where
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

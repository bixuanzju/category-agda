{-# OPTIONS --type-in-type #-}

module Functors where

open import Prelude
open import Categories


-- Functor from C to D
record _=>_ (C D : Category) : Set where
  module C = Category C
  module D = Category D
  field
    -- Two mappings
    𝔽₀ : C.Obj → D.Obj
    𝔽₁ : {S T : C.Obj} → S C.~> T → (𝔽₀ S) D.~> (𝔽₀ T)

    -- Two laws
    F-map-id~> : {T : C.Obj} → 𝔽₁ C.id~> ≡ D.id~> {𝔽₀ T}
    F-map->~> : {R S T : C.Obj} (f : R C.~> S) (g : S C.~> T) →
                𝔽₁ (f C.>~> g) ≡ (𝔽₁ f) D.>~> (𝔽₁ g)


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
  F-map-id~> (F >=> G) = begin
    𝔽₁ G (𝔽₁ F (id~> C))
   ≡⟨ cong (𝔽₁ G) (F-map-id~> F) ⟩
    𝔽₁ G (id~> D)
   ≡⟨ F-map-id~> G ⟩
    id~> E □
  F-map->~> (F >=> G) f g = begin
    𝔽₁ G (𝔽₁ F (_>~>_ C f g))
   ≡⟨ cong (𝔽₁ G) (F-map->~> F f g) ⟩
    𝔽₁ G (_>~>_ D (𝔽₁ F f) (𝔽₁ F g))
   ≡⟨ F-map->~> G (𝔽₁ F f) (𝔽₁ F g) ⟩
    _>~>_ E (𝔽₁ G (𝔽₁ F f)) (𝔽₁ G (𝔽₁ F g)) □


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
                _≡_ {∀ {T : Category.Obj C} → 𝔽₁ (Category.id~> C {T}) ≡ Category.id~> D} F-map-id~> G-map-id~>
                ×
                _≡_ {∀ {R S T : Category.Obj C} (f : (C Category.~> R) S) (g : (C Category.~> S) T) →
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

open Rep public

----------------------------------------------------------------------------
-- New categories from old
----------------------------------------------------------------------------


-- Ordered pair categories

Prod : Category → Category → Category
Prod C D = record
             { Obj = C.Obj × D.Obj
             ; _~>_ = λ x y → (fst x C.~> fst y) × (snd x D.~> snd y)
             ; id~> = C.id~> , D.id~>
             ; _>~>_ = λ { (f , p) (g , q) → C._>~>_ f g , D._>~>_ p q }
             ; law-id~>ˡ = λ f → begin
                 (C.id~> C.>~> fst f) , (D.id~> D.>~> snd f)
                ≡⟨ cong (λ x → x , (D.id~> D.>~> snd f)) (C.law-id~>ˡ _) ⟩
                 fst f , (D.id~> D.>~> snd f)
                ≡⟨ cong (λ x → fst f , x) (D.law-id~>ˡ _) ⟩
                 f □
             ; law-id~>ʳ = λ f → begin
                  (fst f C.>~> C.id~>) , (snd f D.>~> D.id~>)
                 ≡⟨ cong (λ x → x , (snd f D.>~> D.id~>)) (C.law-id~>ʳ _) ⟩
                  fst f , (snd f D.>~> D.id~>)
                 ≡⟨ cong (λ x → fst f , x) (D.law-id~>ʳ _) ⟩
                  f □
             ; law->~> = λ f g h → begin
                  (fst f C.>~> fst g C.>~> fst h) , (snd f D.>~> snd g D.>~> snd h)
                 ≡⟨ cong (λ x → x , (snd f D.>~> snd g D.>~> snd h)) (C.law->~> _ _ _) ⟩
                  (fst f C.>~> (fst g C.>~> fst h)) , (snd f D.>~> snd g D.>~> snd h)
                 ≡⟨ cong (λ x → (fst f C.>~> (fst g C.>~> fst h)) , x) (D.law->~> _ _ _) ⟩
                  (fst f C.>~> (fst g C.>~> fst h)) , (snd f D.>~> (snd g D.>~> snd h)) □
             }
  where module C = Category C
        module D = Category D




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
                          ( begin
                            id~> >~> f
                           ≡⟨ law-id~>ˡ _ ⟩
                            f
                           ≡⟨ sym (law-id~>ʳ _) ⟩
                            f >~> id~> □
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
                              ( begin
                                i >~> k >~> h
                               ≡⟨ law->~> i k h ⟩
                                i >~> (k >~> h)
                               ≡⟨ whiskerˡ (Arrow~>.commuteSquare kl) ⟩
                                i >~> (g >~> l)
                               ≡⟨ sym (law->~> i g l) ⟩
                                i >~> g >~> l
                               ≡⟨ whiskerʳ (Arrow~>.commuteSquare ij) ⟩
                                f >~> j >~> l
                               ≡⟨ law->~> f j l ⟩
                                f >~> (j >~> l) □
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
           ; 𝔽₁ = λ x → arrarr x x ( begin
                                     x >~> id~>
                                    ≡⟨ law-id~>ʳ x ⟩
                                     x
                                    ≡⟨ sym (law-id~>ˡ x) ⟩
                                     id~> >~> x □
                                   )
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
                         ( begin
                           f >~> g >~> t
                          ≡⟨ law->~> _ _ _ ⟩
                           f >~> (g >~> t)
                          ≡⟨ whiskerˡ g-prf ⟩
                           f >~> s
                          ≡⟨ f-prf ⟩
                           r □
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
                          C/B.slicearr p ( begin
                                           p >~> (y >~> f)
                                          ≡⟨ sym (law->~> _ _ _) ⟩
                                           p >~> y >~> f
                                          ≡⟨ whiskerʳ p-prf ⟩
                                           x >~> f □
                                         )
                       }
              ; F-map-id~> = refl
              ; F-map->~> = λ _ _ → refl }

module Prelude where

-- Copied from CS410-17 by Mcbride

------------------------------------------------------------------------------
-- functional equipment (types may be generalized later)
------------------------------------------------------------------------------

-- the polymorphic identity function
id : {X : Set} -> X -> X
id x = x

-- standard composition: f << g is "f after g"
_<<_ : {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> (X -> Z)
(f << g) x = f (g x)

-- diagrammatic composition: f >> g is "f then g"
_>>_ : {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
                     --       ^^^^^^^^          dominoes!
(f >> g) x = g (f x)
infixr 5 _>>_

-- infix application
_$_ : {S : Set}{T : S -> Set}(f : (x : S) -> T x)(s : S) -> T s
f $ s = f s
infixl 2 _$_


------------------------------------------------------------------------------
-- some basic "logical" types
------------------------------------------------------------------------------

data Zero : Set where
  -- to give a value in a data, choose one constructor
  -- there are no constructors
  -- so that's impossible

record One : Set where
  -- to give a value in a record type, fill all its fields
  -- there are no fields
  -- so that's trivial
  --   (can we have a constructor, for convenience?)
  constructor <>

data _+_ (S : Set)(T : Set) : Set where -- "where" wants an indented block
  -- to offer a choice of constructors, list them with their types
  inl : S -> S + T     -- constructors can pack up stuff
  inr : T -> S + T
  -- in Haskell, this was called "Either S T"

record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
  constructor _,_
  field -- introduces a bunch of fields, listed with their types
    fst : S
    snd : T fst
open Sg public


-- A variant of Sigma type with the second field annotated as irrelevant
record Prf (S : Set)(T : (S -> Set)) : Set where
  constructor _,_
  field
    elem : S
    .prf : (T elem)
open Prf public


_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

infixr 4 _,_ _*_

magic : Zero → {A : Set} → A
magic ()


------------------------------------------------------------------------------
-- natural numbers and addition
------------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat     -- recursive data type

{-# BUILTIN NATURAL Nat #-}
--  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc x +N y = suc (x +N y)      -- there are other choices


------------------------------------------------------------------------------
-- equality
------------------------------------------------------------------------------

data _==_ {X : Set} (x : X) : X -> Set where
  refl : x == x           -- the relation that's "only reflexive"
infix 2 _==_


{-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl =$= refl = refl

_=$_ : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} -> (f == g) -> (x : S) -> f x == g x
refl =$ x = refl

infixl 2 _=$=_ _=$_

sym : {X : Set}{x y : X} -> x == y -> y == x
sym refl = refl

subst : ∀ {X : Set} {s t : X} → s == t → (P : X → Set) → P s → P t
subst refl P x = x

cong : ∀ {X : Set}{Y : Set}(f : X → Y){x y} → x == y → f x == f y
cong f refl = refl

_□ : {X : Set} (x : X) → x == x
x □ = refl

_≡⟨_⟩_  : ∀ {X : Set} (x : X) {y z} → x == y → y == z → x == z
_ ≡⟨ refl ⟩ q = q

_⟨_⟩≡_ : ∀ {X : Set} (x : X) {y z} → y == x → y == z → x == z
_ ⟨ refl ⟩≡ q = q


infixr 1 _≡⟨_⟩_ _⟨_⟩≡_
infixr 2 _□


------------------------------------------------------------------------------
-- greater-than-or-equals
------------------------------------------------------------------------------

_>=_ : Nat -> Nat -> Set
x     >= zero   = One
zero  >= suc y  = Zero
suc x >= suc y  = x >= y

refl->= : (n : Nat) -> n >= n
refl->= zero    = record {}
refl->= (suc n) = refl->= n

trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >= z
trans->=      x       y  zero    x>=y y>=z = record {}
trans->=      x  zero    (suc z) x>=y ()
trans->= zero    (suc y) (suc z) ()   y>=z
trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z

suc->= : (x : Nat) -> suc x >= x
suc->= zero    = <>
suc->= (suc x) = suc->= x


----------------------------------------------------------------------------
-- Two -- the type of Boolean values
----------------------------------------------------------------------------

data Two : Set where tt ff : Two
{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

-- nondependent conditional with traditional syntax
if_then_else_ : forall {l}{X : Set l} -> Two -> X -> X -> X
if tt then t else e = t
if ff then t else e = e

-- dependent conditional cooked for partial application
caseTwo : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
caseTwo t f tt = t
caseTwo t f ff = f

_⊹_ : Set → Set → Set
S ⊹ T = Sg Two (caseTwo S T)

Dec : Set → Set
Dec X = X ⊹ (X → Zero)


----------------------------------------------------------------------------
-- lists
----------------------------------------------------------------------------

data List (X : Set) : Set where
  []   : List X
  _,-_ : (x : X)(xs : List X) -> List X
infixr 4 _,-_
{-# COMPILE GHC List = data [] ([] | (:)) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _,-_ #-}


----------------------------------------------------------------------------
-- chars and strings
----------------------------------------------------------------------------

postulate       -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String

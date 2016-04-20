--open import Agda.Builtin.Equality


infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

data Bool : Set where
  false true : Bool

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

infixl 6 _+_ 
_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

infixl 7 _*_
_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

module _ where

  {- Functions -}

  postulate funext : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

  id : {A : Set} → A → A
  id x = x

  infixr 9 _∘_
  _∘_ : {A B C : Set} (f : B → C) (g : A → B) → A → C
  (f ∘ g) x = f (g (x))

  {- Equality -}

  ≡-subst : {A : Set} {x y : A} → x ≡ y → (P : A → Set) → P x → P y 
  ≡-subst refl p px = px

  ≡-sym : {A : Set} {x y : A} → x ≡ y → y ≡ x 
  ≡-sym refl = refl

  ≡-trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≡-trans refl refl = refl

  ≡-cong : {A B : Set} {x x' : A} (f : A → B) → x ≡ x' → f x ≡ f x'
  ≡-cong f refl = refl

  ≡-cong₂ : {A B C : Set} {x x' : A} {y y' : B} (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
  ≡-cong₂ f refl refl = refl

  infixr 1 _≡⟨_⟩_ 
  _≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
  _≡⟨_⟩_ x x≡y y≡z = ≡-trans x≡y y≡z

  infix 2 _≡∎
  _≡∎ : {A : Set} (x : A) → x ≡ x
  _≡∎  _ = refl

  {- Unit -}

  data ⊤ : Set where
    top : ⊤

  {- Sum -}

  infixr 1 _∨_
  data _∨_ (A : Set) (B : Set) : Set where
    inl : A → A ∨ B
    inr : B → A ∨ B

  _?! : Set → Set
  A ?! = A ∨ ⊤

  {- Product -}

  infixr 2 _∧_
  infixr 4 _,_
  data _∧_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A ∧ B

  data ∃ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → ∃ A B


  


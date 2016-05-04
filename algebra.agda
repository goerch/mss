open import Agda.Builtin.Equality

open import prelude

module _ where

  record IsSemigroup {A : Set} (_+S_ : A → A → A) : Set where
    constructor mk
    field
      assoc : (x y z : A) → x +S (y +S z) ≡ (x +S y) +S z

  record Semigroup (A : Set) : Set where
    constructor mk
    field
      _+S_ : A → A → A
      isSemigroup : IsSemigroup _+S_
    open IsSemigroup isSemigroup public

  record IsSemigroupHomomorphism {A B : Set} (ma : Semigroup A) (mb : Semigroup B) (h : A → B) : Set where
    constructor mk
    open Semigroup ma renaming (_+S_ to _+Sa_)
    open Semigroup mb renaming (_+S_ to _+Sb_)
    field
      respects : (x y : A) → h (x +Sa y) ≡ (h x) +Sb (h y)

  record SemigroupHomomorphism {A B : Set} (ma : Semigroup A) (mb : Semigroup B) : Set where
    constructor mk
    field
      h : A → B
      isSemigroupHomomorphism : IsSemigroupHomomorphism ma mb h
    open IsSemigroupHomomorphism isSemigroupHomomorphism public

  record IsMonoid {A : Set} (_+M_ : A → A → A) (e : A) : Set where
    constructor mk
    field
      left-unit : (x : A) → e +M x ≡ x
      right-unit : (x : A) → x +M e ≡ x
      assoc : (x y z : A) → x +M (y +M z) ≡ (x +M y) +M z

  record Monoid (A : Set) : Set where
    constructor mk
    field
      e : A
      _+M_ : A → A → A
      isMonoid : IsMonoid _+M_ e
    open IsMonoid isMonoid public
    semigroup : Semigroup A
    semigroup = mk _+M_ (mk assoc)

  record IsMonoidHomomorphism {A B : Set} (ma : Monoid A) (mb : Monoid B) (h : A → B) : Set where
    constructor mk
    open Monoid ma renaming (e to ea; _+M_ to _+Ma_)
    open Monoid mb renaming (e to eb; _+M_ to _+Mb_)
    field
      unit : h (ea) ≡ eb
      respects : (x y : A) → h (x +Ma y) ≡ (h x) +Mb (h y)

  record MonoidHomomorphism {A B : Set} (ma : Monoid A) (mb : Monoid B) : Set where
    constructor mk
    field
      h : A → B
      isMonoidHomomorphism : IsMonoidHomomorphism ma mb h
    open IsMonoidHomomorphism isMonoidHomomorphism public


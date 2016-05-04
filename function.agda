open import Agda.Builtin.Equality

open import prelude

module _ where

  record IsWeakInvertible {A B : Set} (h : A → B) (g : B → A) : Set where
    constructor mk
    field
      apply : (x : A) → (h ∘ g ∘ h) x ≡ h x

  record WeakInvertible (A B : Set) : Set where
    constructor mk
    field
      h : A → B
      h- : B → A
      isWeakInvertible : IsWeakInvertible h h-
    open IsWeakInvertible isWeakInvertible public


  record IsLeftInvertible {A B : Set} (hl- : B → A) (h : A → B) : Set where
    constructor mk
    field
      apply : (x : A) → (hl- ∘ h) x ≡ x
    isWeakInvertible₁ : IsWeakInvertible h hl-
    isWeakInvertible₁ = mk (λ x → ≡-cong h (apply x))
    isWeakInvertible₂ : IsWeakInvertible hl- h
    isWeakInvertible₂ = mk (λ x → apply (hl- x))

  record LeftInvertible (A B : Set) : Set where
    constructor mk
    field
      hl- : B → A
      h : A → B
      isLeftInvertible : IsLeftInvertible hl- h
    open IsLeftInvertible isLeftInvertible public
    weakInvertible₁ : WeakInvertible A B
    weakInvertible₁ = mk h hl- isWeakInvertible₁
    weakInvertible₂ : WeakInvertible B A
    weakInvertible₂ = mk hl- h isWeakInvertible₂

  record IsRightInvertible {A B : Set} (h : A → B) (hr- : B → A) : Set where
    constructor mk
    field
      apply : (y : B) → (h ∘ hr-) y ≡ y
    isWeakInvertible₁ : IsWeakInvertible h hr-
    isWeakInvertible₁ = mk (λ x → apply (h x))
    isWeakInvertible₂ : IsWeakInvertible hr- h
    isWeakInvertible₂ = mk (λ x → ≡-cong hr- (apply x))

  record RightInvertible (A B : Set) : Set where
    constructor mk
    field
      h : A → B
      hr- : B → A
      isRightInvertible : IsRightInvertible h hr-
    open IsRightInvertible isRightInvertible public
    weakInvertible₁ : WeakInvertible A B
    weakInvertible₁ = mk h hr- isWeakInvertible₁
    weakInvertible₂ : WeakInvertible B A
    weakInvertible₂ = mk hr- h isWeakInvertible₂

  record IsInvertible {A B : Set} (h : A → B) (h- : B → A) : Set where
    constructor mk
    field
      left-apply : (x : A) → (h- ∘ h) x ≡ x
      right-apply : (y : B) → (h ∘ h-) y ≡ y

  record Invertible (A B : Set) : Set where
    constructor mk
    field
      h : A → B
      h- : B → A
      isInvertible : IsInvertible h h-
    open IsInvertible isInvertible public


--open import Agda.Builtin.Equality
--open import Agda.Builtin.Nat

open import prelude

module _ where

  {- Natural numbers -}

  suc-injective : {n o : Nat} → suc n ≡ suc o → n ≡ o
  suc-injective refl = refl

  {- Order -}

  infix 4 _≤N_
  data _≤N_ : Nat → Nat → Set where
    zn : {n : Nat} → zero ≤N n
    ss : {n o : Nat} → n ≤N o → suc n ≤N suc o

  ≤N-refl : {n : Nat} → n ≤N n
  ≤N-refl {zero} = zn 
  ≤N-refl {suc n} = ss ≤N-refl

  ≤N-anti : {n o : Nat} → n ≤N o → o ≤N n → n ≡ o
  ≤N-anti zn zn = refl
  ≤N-anti (ss h1) (ss h2) = ≡-cong suc (≤N-anti h1 h2)

  ≤N-trans : {n o p : Nat} → n ≤N o → o ≤N p → n ≤N p
  ≤N-trans zn h2 = zn
  ≤N-trans (ss h1) (ss h2) = ss (≤N-trans h1 h2)

  ≤N-total : (n o : Nat) → (n ≤N o) ∨ (o ≤N n)
  ≤N-total zero zero = inl zn
  ≤N-total zero (suc o) = inl zn
  ≤N-total (suc n) zero = inr zn
  ≤N-total (suc n) (suc o) with ≤N-total n o
  ≤N-total (suc n) (suc o) | inl h1 = inl (ss h1)
  ≤N-total (suc n) (suc o) | inr h1 = inr (ss h1)

  infixr 1 _≤N⟨_⟩_ 
  _≤N⟨_⟩_ : (x : Nat) {y z : Nat} → (x ≤N y) → (y ≤N z) → (x ≤N z)
  _≤N⟨_⟩_ x x≤y y≤z = ≤N-trans x≤y y≤z

  infix 2 _≤N∎
  _≤N∎ : (x : Nat) → x ≤N x
  _≤N∎  _ = ≤N-refl

  {- Addition -}

  +N-suc : (x y : Nat) → suc x + y ≡ x + suc y
  +N-suc zero y = refl
  +N-suc (suc x) y = ≡-cong suc (+N-suc x y) 

  +N-unit : (x : Nat) → x + 0 ≡ x
  +N-unit zero = refl
  +N-unit (suc x) = ≡-cong suc (+N-unit x) 

  +N-comm : (x y : Nat) → x + y ≡ y + x
  +N-comm zero y = ≡-sym (+N-unit y) 
  +N-comm (suc x) y = 
    suc (x + y)
      ≡⟨ ≡-cong suc (+N-comm x y) ⟩
    suc (y + x)
      ≡⟨ +N-suc y x ⟩
    y + suc x
      ≡∎

  +N-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
  +N-assoc zero y z = refl
  +N-assoc (suc x) y z = ≡-cong suc (+N-assoc x y z) 

  +N-mono : {n o p : Nat} → o ≤N p → (n + o) ≤N (n + p)
  +N-mono {zero} h1 = h1
  +N-mono {suc n} h1 = ss (+N-mono {n} h1)

  {- Multiplication -}

  *N-unit : (x : Nat) → x * 1 ≡ x
  *N-unit zero = refl
  *N-unit (suc x) = ≡-cong suc (*N-unit x) 

  N-distrib : (x y z : Nat) → x * (y + z) ≡ x * y + x * z 
  N-distrib zero y z = refl
  N-distrib (suc x) y z = 
    y + z + x * (y + z)
      ≡⟨ ≡-cong (λ c → y + z + c) (N-distrib x y z) ⟩
    y + z + (x * y + x * z)
      ≡⟨ +N-assoc y z (x * y + x * z) ⟩
    y + (z + (x * y + x * z))
      ≡⟨ ≡-cong (λ c → y + c) (
      z + (x * y + x * z)
        ≡⟨ ≡-sym (+N-assoc z (x * y) (x * z)) ⟩
      z + x * y + x * z
        ≡⟨ ≡-cong (λ c → c + x * z) (+N-comm z (x * y)) ⟩
      x * y + z + x * z
        ≡⟨ +N-assoc (x * y) z (x * z) ⟩
      x * y + (z + x * z)
        ≡∎) ⟩
    y + (x * y + (z + x * z))
      ≡⟨ ≡-sym (+N-assoc y (x * y) (z + x * z)) ⟩
    y + x * y + (z + x * z)
      ≡∎

  {- Maximum -}

  ↑N : Nat → Nat → Nat
  ↑N zero y = y
  ↑N (suc x) zero = suc x
  ↑N (suc x) (suc y) = suc (↑N x y)

  example-↑N = ↑N 1 2

  ↑N-comm : (n o : Nat) → ↑N n o ≡ ↑N o n
  ↑N-comm zero zero = refl
  ↑N-comm zero (suc o) = refl
  ↑N-comm (suc n) zero = refl
  ↑N-comm (suc n) (suc o) = ≡-cong suc (↑N-comm n o)
 
  ↑N-assoc : (x y z : Nat) → ↑N x (↑N y z) ≡ ↑N (↑N x y) z
  ↑N-assoc zero y z = refl
  ↑N-assoc (suc x) zero z = refl
  ↑N-assoc (suc x) (suc y) zero = refl
  ↑N-assoc (suc x) (suc y) (suc z) = ≡-cong suc (↑N-assoc x y z) 

  ≤N⇒↑N : {n o : Nat} → n ≤N o → ↑N n o ≡ o
  ≤N⇒↑N zn = refl
  ≤N⇒↑N (ss p) = ≡-cong suc (≤N⇒↑N p)

  ↑N⇒≤N : {n o : Nat} → ↑N n o ≡ o → n ≤N o
  ↑N⇒≤N {zero} refl = zn
  ↑N⇒≤N {suc n} {zero} ()
  ↑N⇒≤N {suc n} {suc o} h1 = ss (↑N⇒≤N (suc-injective h1))

  {- Minimum -}

  ↓N : Nat → Nat → Nat
  ↓N zero y = zero
  ↓N (suc x) zero = zero
  ↓N (suc x) (suc y) = suc (↓N x y)

  example-↓N = ↓N 1 2

  ↓N-comm : ∀ (n o : Nat) → ↓N n o ≡ ↓N o n
  ↓N-comm zero zero = refl
  ↓N-comm zero (suc o) = refl
  ↓N-comm (suc n) zero = refl
  ↓N-comm (suc n) (suc o) = ≡-cong suc (↓N-comm n o)

  ↓N-assoc : (x y z : Nat) → ↓N x (↓N y z) ≡ ↓N (↓N x y) z
  ↓N-assoc zero y z = refl
  ↓N-assoc (suc x) zero z = refl
  ↓N-assoc (suc x) (suc y) zero = refl
  ↓N-assoc (suc x) (suc y) (suc z) = ≡-cong suc (↓N-assoc x y z) 

  ≤N⇒↓N : {n o : Nat} → n ≤N o → ↓N o n ≡ n
  ≤N⇒↓N {o = o} zn = ↓N-comm o zero
  ≤N⇒↓N (ss p) = ≡-cong suc (≤N⇒↓N p)

  ↓N⇒≤N : {n o : Nat} → ↓N o n ≡ n → n ≤N o
  ↓N⇒≤N {zero} h1 = zn
  ↓N⇒≤N {suc n} {zero} ()
  ↓N⇒≤N {suc n} {suc o} h1 = ss (↓N⇒≤N (suc-injective h1))





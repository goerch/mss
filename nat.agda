open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

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

  ≤N-respects-≡ : {n o : Nat} → n ≡ o → n ≤N o
  ≤N-respects-≡ refl = ≤N-refl

  ≤N-total : (n o : Nat) → n ≤N o ∨ o ≤N n
  ≤N-total zero zero = inl zn
  ≤N-total zero (suc o) = inl zn
  ≤N-total (suc n) zero = inr zn
  ≤N-total (suc n) (suc o) with ≤N-total n o
  ≤N-total (suc n) (suc o) | inl h1 = inl (ss h1)
  ≤N-total (suc n) (suc o) | inr h1 = inr (ss h1)

  ≤N-decidable : (n o : Nat) → n ≤N o ∨ ¬ n ≤N o
  ≤N-decidable zero zero = inl zn
  ≤N-decidable zero (suc o) = inl zn
  ≤N-decidable (suc n) zero = inr (λ ())
  ≤N-decidable (suc n) (suc o) with ≤N-decidable n o
  ≤N-decidable (suc n) (suc o) | inl h1 = inl (ss h1)
  ≤N-decidable (suc n) (suc o) | inr h1 = inr (λ h2 → h1 (≤N-pred h2)) where
    ≤N-pred : ∀ {n o} → suc n ≤N suc o → n ≤N o
    ≤N-pred (ss h1) = h1

  infixr 1 _≤N⟨_⟩_ 
  _≤N⟨_⟩_ : (n : Nat) {o p : Nat} → (n ≤N o) → (o ≤N p) → (n ≤N p)
  _≤N⟨_⟩_ n n≤o o≤p = ≤N-trans n≤o o≤p

  infix 2 _≤N∎
  _≤N∎ : (n : Nat) → n ≤N n
  _≤N∎  _ = ≤N-refl

  infix 4 _<N_
  data _<N_ : Nat → Nat → Set where
    zn : {n : Nat} → zero <N suc n
    ss : {n o : Nat} → n <N o → suc n <N suc o

  <N-total : (n o : Nat) → (n <N o) ∨ (n ≡ o) ∨ (o <N n)
  <N-total zero zero = inr (inl refl)
  <N-total zero (suc o) = inl zn
  <N-total (suc n) zero = inr (inr zn)
  <N-total (suc n) (suc o) with <N-total n o
  <N-total (suc .0) (suc _) | inl zn = inl (ss zn)
  <N-total (suc _) (suc _) | inl (ss h1) = inl (ss (ss h1))
  <N-total (suc n) (suc .n) | inr (inl refl) = inr (inl refl)
  <N-total (suc _) (suc .0) | inr (inr zn) = inr (inr (ss zn))
  <N-total (suc _) (suc _) | inr (inr (ss h1)) = inr (inr (ss (ss h1)))

  <N⇒¬≡ : {n o : Nat} → n <N o → ¬ n ≡ o
  <N⇒¬≡ zn ()
  <N⇒¬≡ (ss h1) refl = ⊥-elim (<N⇒¬≡ h1 refl)

  >N⇒¬≡ : {n o : Nat} → o <N n → ¬ n ≡ o
  >N⇒¬≡ zn ()
  >N⇒¬≡ (ss h1) refl = ⊥-elim (>N⇒¬≡ h1 refl)

  ≡N-decidable : (n o : Nat) → n ≡ o ∨ ¬ n ≡ o
  ≡N-decidable n o with <N-total n o 
  ≡N-decidable n o | inl h1 = inr (<N⇒¬≡ h1)
  ≡N-decidable n o | inr (inl h1) = inl h1
  ≡N-decidable n o | inr (inr h1) = inr (>N⇒¬≡ h1)

  {- Addition -}

  +N-suc : (n o : Nat) → suc n + o ≡ n + suc o
  +N-suc zero o = refl
  +N-suc (suc n) o = ≡-cong suc (+N-suc n o) 

  +N-unit : (n : Nat) → n + 0 ≡ n
  +N-unit zero = refl
  +N-unit (suc n) = ≡-cong suc (+N-unit n) 

  +N-comm : (n o : Nat) → n + o ≡ o + n
  +N-comm zero o = ≡-sym (+N-unit o) 
  +N-comm (suc n) o = 
    suc (n + o)
      ≡⟨ ≡-cong suc (+N-comm n o) ⟩
    suc (o + n)
      ≡⟨ +N-suc o n ⟩
    o + suc n
      ≡∎

  +N-assoc : (n o p : Nat) → (n + o) + p ≡ n + (o + p)
  +N-assoc zero o p = refl
  +N-assoc (suc n) o p = ≡-cong suc (+N-assoc n o p) 

  +N-mono : {n o p : Nat} → o ≤N p → (n + o) ≤N (n + p)
  +N-mono {zero} h1 = h1
  +N-mono {suc n} h1 = ss (+N-mono {n} h1)

  {- Multiplication -}

  *N-unit : (n : Nat) → n * 1 ≡ n
  *N-unit zero = refl
  *N-unit (suc n) = ≡-cong suc (*N-unit n) 

  *N-distrib : (n o p : Nat) → n * (o + p) ≡ n * o + n * p 
  *N-distrib zero o p = refl
  *N-distrib (suc n) o p = 
    o + p + n * (o + p)
      ≡⟨ ≡-cong (λ c → o + p + c) (*N-distrib n o p) ⟩
    o + p + (n * o + n * p)
      ≡⟨ +N-assoc o p (n * o + n * p) ⟩
    o + (p + (n * o + n * p))
      ≡⟨ ≡-cong (λ c → o + c) (
      p + (n * o + n * p)
        ≡⟨ ≡-sym (+N-assoc p (n * o) (n * p)) ⟩
      p + n * o + n * p
        ≡⟨ ≡-cong (λ c → c + n * p) (+N-comm p (n * o)) ⟩
      n * o + p + n * p
        ≡⟨ +N-assoc (n * o) p (n * p) ⟩
      n * o + (p + n * p)
        ≡∎) ⟩
    o + (n * o + (p + n * p))
      ≡⟨ ≡-sym (+N-assoc o (n * o) (p + n * p)) ⟩
    o + n * o + (p + n * p)
      ≡∎

  {- Maximum -}

  ↑N : Nat → Nat → Nat
  ↑N zero o = o
  ↑N (suc n) zero = suc n
  ↑N (suc n) (suc o) = suc (↑N n o)

  example-↑N = ↑N 1 2

  ↑N-comm : (n o : Nat) → ↑N n o ≡ ↑N o n
  ↑N-comm zero zero = refl
  ↑N-comm zero (suc o) = refl
  ↑N-comm (suc n) zero = refl
  ↑N-comm (suc n) (suc o) = ≡-cong suc (↑N-comm n o)
 
  ↑N-assoc : (n o p : Nat) → ↑N n (↑N o p) ≡ ↑N (↑N n o) p
  ↑N-assoc zero o p = refl
  ↑N-assoc (suc n) zero p = refl
  ↑N-assoc (suc n) (suc o) zero = refl
  ↑N-assoc (suc n) (suc o) (suc p) = ≡-cong suc (↑N-assoc n o p) 

  ≤N⇒↑N : {n o : Nat} → n ≤N o → ↑N n o ≡ o
  ≤N⇒↑N zn = refl
  ≤N⇒↑N (ss p) = ≡-cong suc (≤N⇒↑N p)

  ↑N⇒≤N : {n o : Nat} → ↑N n o ≡ o → n ≤N o
  ↑N⇒≤N {zero} refl = zn
  ↑N⇒≤N {suc n} {zero} ()
  ↑N⇒≤N {suc n} {suc o} h1 = ss (↑N⇒≤N (suc-injective h1))

  {- Minimum -}

  ↓N : Nat → Nat → Nat
  ↓N zero o = zero
  ↓N (suc n) zero = zero
  ↓N (suc n) (suc o) = suc (↓N n o)

  example-↓N = ↓N 1 2

  ↓N-comm : ∀ (n o : Nat) → ↓N n o ≡ ↓N o n
  ↓N-comm zero zero = refl
  ↓N-comm zero (suc o) = refl
  ↓N-comm (suc n) zero = refl
  ↓N-comm (suc n) (suc o) = ≡-cong suc (↓N-comm n o)

  ↓N-assoc : (n o p : Nat) → ↓N n (↓N o p) ≡ ↓N (↓N n o) p
  ↓N-assoc zero o p = refl
  ↓N-assoc (suc n) zero p = refl
  ↓N-assoc (suc n) (suc o) zero = refl
  ↓N-assoc (suc n) (suc o) (suc p) = ≡-cong suc (↓N-assoc n o p) 

  ≤N⇒↓N : {n o : Nat} → n ≤N o → ↓N o n ≡ n
  ≤N⇒↓N {o = o} zn = ↓N-comm o zero
  ≤N⇒↓N (ss p) = ≡-cong suc (≤N⇒↓N p)

  ↓N⇒≤N : {n o : Nat} → ↓N o n ≡ n → n ≤N o
  ↓N⇒≤N {zero} h1 = zn
  ↓N⇒≤N {suc n} {zero} ()
  ↓N⇒≤N {suc n} {suc o} h1 = ss (↓N⇒≤N (suc-injective h1))

  ↓↑N : (n o : Nat) → (↓N (↑N n o) n) ≡ n
  ↓↑N zero o = ↓N-comm o zero
  ↓↑N (suc n) zero = ≡-cong suc (≤N⇒↓N ≤N-refl)
  ↓↑N (suc n) (suc o) = ≡-cong suc (↓↑N n o)

  ↑N-distrib : (n o p : Nat) → ↑N n  (↓N o p) ≡ ↓N (↑N n o) (↑N n p)
  ↑N-distrib zero o p = refl
  ↑N-distrib (suc n) zero p = 
    suc n
      ≡⟨ ≡-sym (↓↑N (suc n) p) ⟩
    ↓N (↑N (suc n) p) (suc n)
      ≡⟨ ↓N-comm (↑N (suc n) p) (suc n) ⟩
    ↓N (suc n) (↑N (suc n) p)
      ≡∎
  ↑N-distrib (suc n) (suc o) zero = ≡-cong suc (≡-sym (↓↑N n o))
  ↑N-distrib (suc n) (suc o) (suc p) = ≡-cong suc (↑N-distrib n o p)

  ↓N-distrib : (n o p : Nat) → ↓N n (↑N o p) ≡ ↑N (↓N n o) (↓N n p)
  ↓N-distrib zero o p = refl
  ↓N-distrib (suc n) zero p = refl
  ↓N-distrib (suc n) (suc o) zero = refl 
  ↓N-distrib (suc n) (suc o) (suc p) = ≡-cong suc (↓N-distrib n o p)


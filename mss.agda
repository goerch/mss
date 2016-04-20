--open import Agda.Builtin.Equality
--open import Agda.Builtin.Nat
--open import Agda.Builtin.Int
--open import Agda.Builtin.Bool
--open import Agda.Builtin.List

open import prelude
open import nat
open import int
open import list
open import nelist
open import horner

module _ where

  sum : (xs : List Int) → Int
  sum xs = foldr (λ x1 x2 →  x1 +I x2) (pos 0) xs

  sum+ : (xs : List+ Int) → Int
  sum+ xs = foldr+ (λ x1 x2 →  x1 +I x2) id xs

  example-sum+ = sum+ (pos 1 ∷+ pos 2 ∷+ [ pos 3 ]+)

  -- max : (xs : List Int) → Int
  -- max xs = foldr (λ x1 x2 → ↑I x1 x2) {!!} xs

  max+ : (xs : List+ Int) → Int
  max+ xs = foldr+ (λ x1 x2 → ↑I x1 x2) id xs

  example-max+ = max+ (pos 1 ∷+ pos 2 ∷+ [ pos 3 ]+)

  example-first+ = first+ (1 ∷+ 2 ∷+ [ 3 ]+)
  example-last+ = last+ (1 ∷+ 2 ∷+ [ 3 ]+)

  example-inits+ = inits+ (1 ∷+ 2 ∷+ [ 3 ]+)
  example-tails+ = tails+ (1 ∷+ 2 ∷+ [ 3 ]+)

  example-segs+ = segs+ (1 ∷+ 2 ∷+ [ 3 ]+)

  mss-spec : List+ Int → Int
  mss-spec = max+ ∘ map+ sum+ ∘ segs+

  example-mss-spec = mss-spec (pos 1 ∷+ negsuc 2 ∷+ [ pos 3 ]+)

  max+-flatten+ : (xs : List+ (List+ Int)) → (max+ ∘ flatten+) xs ≡ (max+ ∘ map+ max+) xs
  max+-flatten+ [ x ]+ = refl
  max+-flatten+ (x ∷+ xs) = 
    foldr+ ↑I id (x +++ foldr+ _+++_ id xs)
      ≡⟨ max+-+++ x (foldr+ _+++_ id xs) ⟩
    ↑I (foldr+ ↑I id x) (foldr+ ↑I id (foldr+ _+++_ id xs))
      ≡⟨ ≡-cong (λ c → ↑I (foldr+ ↑I id x) c) (max+-flatten+ xs) ⟩
    ↑I (foldr+ ↑I id x) ((max+ ∘ map+ max+) xs)
      ≡∎ where
    max+-+++ : (xs ys : List+ Int) → max+ (xs +++ ys) ≡ ↑I (max+ xs) (max+ ys)
    max+-+++ [ x ]+ ys = refl
    max+-+++ (x ∷+ xs) ys =
      ↑I x (foldr+ ↑I id (xs +++ ys))
        ≡⟨ ≡-cong (λ c → ↑I x c) (max+-+++ xs ys) ⟩
      ↑I x (↑I (foldr+ ↑I id xs) (foldr+ ↑I id ys))
        ≡⟨ ↑I-assoc x (foldr+ ↑I id xs) (foldr+ ↑I id ys) ⟩
      ↑I (↑I x (foldr+ ↑I id xs)) (foldr+ ↑I id ys)
        ≡∎ 

  mss-derivation : (xs : List+ Int) → mss-spec  xs  ≡ (max+ ∘ scanr+ (λ x1 x2 → x1 +I ↑I (pos zero) x2) id) xs
  mss-derivation xs = 
    (max+ ∘ map+ sum+ ∘ flatten+ ∘ map+ inits+ ∘ tails+) xs
      ≡⟨ ≡-cong (λ c → max+ c) (map+-flatten+ sum+ ((map+ inits+ ∘ tails+) xs)) ⟩
    (max+ ∘ flatten+ ∘ map+ (map+ sum+) ∘ map+ inits+ ∘ tails+) xs
      ≡⟨ max+-flatten+ ((map+ (map+ sum+) ∘ map+ inits+ ∘ tails+) xs) ⟩
    (max+ ∘ map+ max+ ∘ map+ (map+ sum+) ∘ map+ inits+ ∘ tails+) xs
      ≡⟨ ≡-cong (λ c → (max+ ∘ (map+ max+)) c) (≡-sym (map+-compose (map+ sum+) inits+ (tails+ xs))) ⟩
    (max+ ∘ map+ max+) (map+ (map+ sum+ ∘ inits+) (tails+ xs))
      ≡⟨ ≡-cong (λ c → max+ c) (≡-sym (map+-compose max+ ((map+ sum+) ∘ inits+) (tails+ xs))) ⟩
    (max+ ∘ map+ (max+ ∘ (map+ sum+) ∘ inits+) ∘ tails+) xs
      ≡⟨ ≡-cong (λ c → max+ c) (map+-cong (max+ ∘ (map+ sum+) ∘ inits+) (foldr+ (λ x1 x2 → x1 +I (↑I (pos zero) x2)) id)
                        (λ xs → horner-derivation (pos zero) ↑I _+I_ +I-unit distrib xs) (tails+ xs)) ⟩ 
    max+ (map+ (foldr+ (λ x1 x2 → x1 +I (↑I (pos zero) x2)) id) (tails+ xs))
      ≡⟨ ≡-cong (λ c → max+ c) (scanr-derivation (λ x1 x2 → x1 +I ↑I (pos zero) x2) id xs) ⟩
    max+ (scanr+ (λ x1 x2 → x1 +I ↑I (pos zero) x2) id xs)
      ≡∎ where

      distrib : ∀ x y z → x +I ↑I y z ≡ ↑I (x +I y) (x +I z) 
      distrib x y z with ≤I-total y z
      distrib x y z | inl h1 = 
        x +I ↑I y z
          ≡⟨ ≡-cong (λ c → x +I c) (≤I⇒↑I h1) ⟩
        x +I z
          ≡⟨ ≡-sym (≤I⇒↑I (+I-mono {x} {y} {z}  h1)) ⟩
        ↑I (x +I y) (x +I z)
          ≡∎
      distrib x y z | inr h1 =
        x +I ↑I y z
          ≡⟨ ≡-cong (λ c → x +I c) (↑I-comm y z) ⟩
        x +I ↑I z y
          ≡⟨ ≡-cong (λ c → x +I c) (≤I⇒↑I h1) ⟩
        x +I y
          ≡⟨ ≡-sym (≤I⇒↑I (+I-mono {x} {z} {y} h1)) ⟩
        ↑I (x +I z) (x +I y)
          ≡⟨ ↑I-comm (x +I z) (x +I y) ⟩
        ↑I (x +I y) (x +I z)
          ≡∎

  down-from : (n : Nat) → List Int
  down-from n = unfoldr (λ n e → inl (pos n , e)) n n

  up-to : (n : Nat) → List Int
  up-to n = unfoldr (λ n e → inl (negsuc n , e)) n n

  down-from+ : (n : Nat) → List+ Int
  down-from+  zero = [ pos zero ]+
  down-from+ (suc n) = (pos (suc n)) ∷+ (down-from+ n)

  up-to+ : (n : Nat) → List+ Int
  up-to+  zero = [ negsuc zero ]+
  up-to+ (suc n) = (negsuc (suc n)) ∷+ (up-to+ n)

  sawtooth : (n : Nat) → List+ Int
  sawtooth n = up-to+ n +++ reverse+ (down-from+ n) +++ down-from+ n +++ reverse+ (up-to+ n)

  sawtooth-mss-spec : (n : Nat) → Int
  sawtooth-mss-spec n = (max+ ∘ (map+ sum+) ∘ segs+) (sawtooth n)

  sawtooth-mss : (n : Nat) → Int
  sawtooth-mss n = (max+ ∘ scanr+ (λ x1 x2 → x1 +I ↑I (pos zero) x2) id) (sawtooth n)


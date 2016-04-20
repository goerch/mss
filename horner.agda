--open import Agda.Builtin.Equality
--open import Agda.Builtin.Nat
--open import Agda.Builtin.Int

open import prelude
open import nat
open import int
open import nelist

module _ where

  example-horner = (foldr+ ↑I id ∘ map+ (foldr+ _+I_ id) ∘ inits+) (pos 1 ∷+ negsuc 2 ∷+ [ pos 3 ]+)

  horner-spec-concrete : List+ Nat → Nat
  horner-spec-concrete = ((foldr+ _+_ id) ∘ map+ (foldr+ _*_ id) ∘ inits+)

  horner-derivation-concrete : (xs : List+ Nat) → ((foldr+ _+_ id) ∘ map+ (foldr+ _*_ id) ∘ inits+) xs ≡ foldr+ (λ x1 x2 → x1 * suc x2) id xs
  horner-derivation-concrete [ x ]+ = refl
  horner-derivation-concrete (x ∷+ xs) = 
    (foldr+ _+_ id ∘ map+ (foldr+ _*_ id) ∘ inits+) (x ∷+ xs)
      ≡⟨ ≡-cong (λ c → x + c) (go x (inits+ xs)) ⟩
    x + x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id) ∘ inits+) xs
      ≡⟨ ≡-cong (λ c → x + x * c) (horner-derivation-concrete xs) ⟩
    x + x * foldr+ (λ x1 x2 → x1 * suc x2) id xs
      ≡⟨ ≡-cong (λ c → c + x * (foldr+ (λ x1 x2 → x1 * suc x2) id xs)) (≡-sym (*N-unit x)) ⟩
    x * 1 + x * foldr+ (λ x1 x2 → x1 * suc x2) id xs
      ≡⟨ ≡-sym (N-distrib x 1 (foldr+ (λ x1 x2 → x1 * suc x2) id xs)) ⟩ 
    x * suc (foldr+ (λ x1 x2 → x1 * suc x2) id xs)
      ≡∎ where
    go : (x : Nat) (ys : List+ (List+ Nat)) → foldr+ _+_ id (map+ (foldr+ _*_ id) (map+ (_∷+_ x) ys)) ≡ x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id)) ys
    go x [ y ]+ = refl
    go x (y ∷+ ys) = 
      foldr+ _+_ id (map+ (foldr+ _*_ id) (map+ (_∷+_ x) (y ∷+ ys)))
        ≡⟨ ≡-cong (λ c → x * foldr+ _*_ id y + c) (go x ys) ⟩
      x * foldr+ _*_ id y + x * foldr+ _+_ id (map+ (foldr+ _*_ id) ys)
        ≡⟨ ≡-sym (N-distrib x (foldr+ _*_ id y) (foldr+ _+_ id (map+ (foldr+ _*_ id) ys))) ⟩
      x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id)) (y ∷+ ys)
        ≡∎

  horner-derivation : (e : Int) (_+_ _*_ : Int → Int → Int) 
    (unit : (x : Int) → x * e ≡ x)
    (distributive : (x y z : Int) → x * (y + z) ≡ (x * y) + (x * z))
    (xs : List+ Int) → ((foldr+ _+_ id) ∘ map+ (foldr+ _*_ id) ∘ inits+) xs ≡ foldr+ (λ x1 x2 → x1 * (e + x2)) id xs
  horner-derivation e _+_ _*_ unit distributive [ x ]+ = refl
  horner-derivation e _+_ _*_ unit distributive (x ∷+ xs) = 
    (foldr+ _+_ id ∘ map+ (foldr+ _*_ id) ∘ inits+) (x ∷+ xs)
      ≡⟨ ≡-cong (λ c → x + c) (go x (inits+ xs)) ⟩
    x + (x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id) ∘ inits+) xs)
      ≡⟨ ≡-cong (λ c → x + (x * c)) (horner-derivation e _+_ _*_ unit distributive xs) ⟩
    x + (x * foldr+ (λ x1 x2 → x1 * (e + x2)) id xs)
      ≡⟨ ≡-cong (λ c → c + (x * (foldr+ (λ x1 x2 → x1 * (e + x2)) id xs))) (≡-sym (unit x)) ⟩
    (x * e) + (x * foldr+ (λ x1 x2 → x1 * (e + x2)) id xs)
      ≡⟨ ≡-sym (distributive x e (foldr+ (λ x1 x2 → x1 * (e + x2)) id xs)) ⟩ 
    x * (e + foldr+ (λ x1 x2 → x1 * (e + x2)) id xs)
      ≡∎ where 
    go : (x : Int) (ys : List+ (List+ Int)) → foldr+ _+_ id (map+ (foldr+ _*_ id) (map+ (_∷+_ x) ys)) ≡ (x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id)) ys)
    go x [ y ]+ = refl
    go x (y ∷+ ys) =
      foldr+ _+_ id (map+ (foldr+ _*_ id) (map+ (_∷+_ x) (y ∷+ ys)))
        ≡⟨ ≡-cong (λ c → (x * foldr+ _*_ id y) + c) (go x ys) ⟩
      (x * foldr+ _*_ id y) + (x * foldr+ _+_ id (map+ (foldr+ _*_ id) ys))
        ≡⟨ ≡-sym (distributive x (foldr+ _*_ id y) (foldr+ _+_ id (map+ (foldr+ _*_ id) ys))) ⟩
      x * (foldr+ _+_ id ∘ map+ (foldr+ _*_ id)) (y ∷+ ys)
        ≡∎


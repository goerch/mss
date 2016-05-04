open import Agda.Builtin.Equality
open import Agda.Builtin.List

open import prelude
open import function
open import algebra
open import nelist

module _ where

  list+Semigroup : (A : Set) → Semigroup (List+ A)
  list+Semigroup A = mk _+++_ (mk (λ x y z → +++-assoc x y z))

  foldl+SemigroupHomomorphism : {A : Set} (sa : Semigroup A) → SemigroupHomomorphism (list+Semigroup A) sa
  foldl+SemigroupHomomorphism sa = mk (foldl+ _+S_ id) (mk (foldl+-+++₂ _+S_ assoc)) where
    open Semigroup sa

  foldrSemigroupHomomorphism : {A : Set} (sa : Semigroup A) → SemigroupHomomorphism (list+Semigroup A) sa
  foldrSemigroupHomomorphism sa = mk (foldr+ _+S_ id) (mk (foldr+-+++₂ _+S_ assoc)) where
    open Semigroup sa

  mapSemigroupHomomorphism : {A B : Set} (f : A → B) → SemigroupHomomorphism (list+Semigroup A) (list+Semigroup B)
  mapSemigroupHomomorphism f = mk (map+ f) (mk (map+-+++ f))

  homomorphism₁⇒ : {A B : Set} (sb : Semigroup B) (mh : SemigroupHomomorphism (list+Semigroup A) sb) →
    ∃ (Semigroup B) (λ sb' → (xs : List+ A) → 
    let open Semigroup sb' in 
    let open SemigroupHomomorphism mh in
    h xs ≡ (foldr+ (_+S_) id ∘ map+ (h ∘ [_]+ )) xs)
  homomorphism₁⇒ {A} {B} sb mh = 
    mk _+S_ (mk assoc), (λ xs → go xs) where 
    open Semigroup sb
    open SemigroupHomomorphism mh
    go : (xs : List+ A) → h xs ≡ (foldr+ (_+S_) id ∘ map+ (h ∘ [_]+ )) xs
    go [ x ]+ = refl
    go (x ∷+ xs) =
      h (x ∷+ xs)
        ≡⟨ respects [ x ]+ xs ⟩
      h [ x ]+ +S h xs 
        ≡⟨ ≡-cong (λ c → h [ x ]+ +S c) (go xs) ⟩
      h [ x ]+ +S (foldr+ _+S_ id ∘ map+ (h ∘ [_]+)) xs 
        ≡⟨ ≡-cong (λ c → h [ x ]+ +S c) (map+-fusion _+S_ id (h ∘ [_]+) xs) ⟩
      h [ x ]+ +S foldr+ (_+S_ ∘ (h ∘ [_]+)) (id ∘ (h ∘ [_]+)) xs
        ≡⟨ ≡-sym (map+-fusion _+S_ id (h ∘ [_]+) (x ∷+ xs)) ⟩ 
      (foldr+ _+S_ id ∘ map+ (h ∘ [_]+)) (x ∷+ xs)
        ≡∎ 

  homomorphism₁⇐ : {A B : Set} (sb : Semigroup B) (h : List+ A → B) → SemigroupHomomorphism (list+Semigroup A) sb
  homomorphism₁⇐ {A} sb h = mk (foldr+ _+S_ id ∘ map+ (h ∘ [_]+ )) (mk (λ xs ys → 
    (foldr+ _+S_ id ∘ map+ (h ∘ [_]+)) (xs +++ ys)
      ≡⟨ map+-fusion _+S_ id (h ∘ [_]+) (xs +++ ys) ⟩
    foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) (xs +++ ys)
      ≡⟨ go xs ys ⟩
    ( foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) xs) +S (foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) ys)
      ≡⟨ ≡-cong₂ (λ c1 c2 → _+S_ c1 c2) 
                   (≡-sym (map+-fusion _+S_ id (h ∘ [_]+) xs)) 
                   (≡-sym (map+-fusion _+S_ id (h ∘ [_]+) ys)) ⟩
    (foldr+ _+S_ id (map+ (h ∘ [_]+ ) xs)) +S (foldr+ _+S_ id (map+ (h ∘ [_]+ ) ys))
      ≡∎)) where
    open Semigroup sb
    go : (xs ys : List+ A) → foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) (xs +++ ys) ≡ 
      (foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) xs) +S (foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) ys)
    go [ x ]+ ys = refl
    go (x ∷+ xs) ys = 
      foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) ((x ∷+ xs) +++ ys)
        ≡⟨ ≡-cong (λ c → _+S_ (h [ x ]+) c) (go xs ys) ⟩
      h [ x ]+ +S
        (foldr+ (_+S_ ∘ h ∘ [_]+) (h ∘ [_]+) xs +S
         foldr+ (_+S_ ∘ h ∘ [_]+) (h ∘ [_]+) ys)
        ≡⟨ assoc (h [ x ]+) (foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) xs) (foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) ys) ⟩
      foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) (x ∷+ xs) +S
        foldr+ (_+S_ ∘ (h ∘ [_]+)) (h ∘ [_]+) ys 
        ≡∎

  homomorphism₂₁ : {A B : Set} (sb : Semigroup  B) (mh : SemigroupHomomorphism (list+Semigroup A) sb) →
    ∃ (A → B → B) (λ f → (xs : List+ A) → 
     let open Semigroup sb in 
     let open SemigroupHomomorphism mh in
     h xs ≡ foldr+ f (h ∘ [_]+) xs)
  homomorphism₂₁ {A} {B} sb mh = mkf , (λ xs → 
    h xs
      ≡⟨ go xs ⟩
    foldr+ mkf (h ∘ [_]+) xs
      ≡∎) where
    open Semigroup sb
    open SemigroupHomomorphism mh
    mkf : A → B → B
    mkf x y = (h [ x ]+) +S y
    go : (xs : List+ A) → h xs ≡ foldr+ mkf (h ∘ [_]+) xs
    go [ x ]+ = refl
    go (x ∷+ xs) =
      h (x ∷+ xs)
        ≡⟨ respects [ x ]+ xs ⟩
      (h [ x ]+) +S (h xs)
        ≡⟨ ≡-cong (λ c → h [ x ]+ +S c) (go xs) ⟩
      foldr+ mkf (h ∘ [_]+) (x ∷+ xs)
        ≡∎ 

  homomorphism₂₂ : {A B : Set} (sb : Semigroup B) (mh : SemigroupHomomorphism (list+Semigroup A) sb) →
    ∃ (B → A → B) (λ f → (xs : List+ A) →
    let open Semigroup sb in 
    let open SemigroupHomomorphism mh in
    h xs ≡ foldl+ f (h ∘ [_]+) xs)
  homomorphism₂₂ {A} {B} sb mh = mkf , (λ xs → 
    h xs
      ≡⟨ go xs ⟩
    foldl+ mkf (h ∘ [_]+) xs
      ≡∎) where
    open Semigroup sb
    open SemigroupHomomorphism mh
    mkf : B → A → B
    mkf x y = x +S (h [ y ]+) 
    go : (xs : List+ A) → h xs ≡ foldl+ mkf (h ∘ [_]+) xs 
    go [ x ]+ = refl
    go (x ∷+ xs) = 
      h (x ∷+ xs)
        ≡⟨ respects [ x ]+ xs ⟩
      h [ x ]+ +S h xs
        ≡⟨ ≡-cong (λ c → (h [ x ]+) +S c) (go xs) ⟩
      h [ x ]+ +S foldl+ mkf (h ∘ [_]+) xs
        ≡⟨ foldl+-fusion mkf mkf (h ∘ [_]+) (_+S_ (h [ x ]+)) (λ y z → assoc (h [ x ]+) y (h [ z ]+)) xs ⟩
      foldl+ mkf (mkf ((h ∘ [_]+) x)) xs
        ≡∎


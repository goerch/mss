open import Agda.Builtin.Equality
open import Agda.Builtin.List

open import prelude
open import function
open import algebra
open import list

module _ where

  listMonoid : (A : Set) → Monoid (List A)
  listMonoid A = mk [] _++_ (mk (λ x → refl) (λ x → ++-unit x) (λ x y z → ++-assoc x y z))

  foldlMonoidHomomorphism : {A : Set} (ma : Monoid A) → MonoidHomomorphism (listMonoid A) ma
  foldlMonoidHomomorphism ma = mk (foldl _+M_ e) (mk refl  (foldl-++₂ _+M_ e left-unit right-unit assoc)) where
    open Monoid ma

  foldrMonoidHomomorphism : {A : Set} (ma : Monoid A) → MonoidHomomorphism (listMonoid A) ma
  foldrMonoidHomomorphism ma = mk (foldr _+M_ e) (mk refl (foldr-++₂ _+M_ e left-unit right-unit assoc)) where
    open Monoid ma

  mapMonoidHomomorphism : {A B : Set} (f : A → B) → MonoidHomomorphism (listMonoid A) (listMonoid B)
  mapMonoidHomomorphism f = mk (map f) (mk refl (map-++ f))

  homomorphism₁⇒ : {A B : Set} (mb : Monoid B) (mh : MonoidHomomorphism (listMonoid A) mb) →
    ∃ (Monoid B) (λ mb' → (xs : List A) → 
    let open Monoid mb' in 
    let open MonoidHomomorphism mh in
    h xs ≡ (foldr (_+M_) e ∘ map (h ∘ [_])) xs)
  homomorphism₁⇒ {A} {B} mb mh = 
    mk e _+M_ (mk left-unit right-unit assoc), (λ xs → go xs) where 
    open Monoid mb
    open MonoidHomomorphism mh
    go : (xs : List A) → h xs ≡ (foldr (_+M_) e ∘ map (h ∘ [_])) xs
    go [] = unit
    go (x ∷ xs) =
      h (x ∷ xs) 
        ≡⟨ respects [ x ] xs ⟩
      h [ x ] +M h xs 
        ≡⟨ ≡-cong (λ c → h [ x ] +M c) (go xs) ⟩
      h [ x ] +M (foldr _+M_ e ∘ map (h ∘ [_])) xs 
        ≡⟨ ≡-cong (λ c → (h [ x ]) +M c) (map-fusion _+M_ e (h ∘ [_]) xs) ⟩
      h [ x ] +M foldr (_+M_ ∘ (h ∘ [_])) e xs 
        ≡⟨ ≡-sym (map-fusion _+M_ e (h ∘ [_]) (x ∷ xs)) ⟩ 
      (foldr _+M_ e ∘ map (h ∘ [_])) (x ∷ xs) 
        ≡∎ 
    
  homomorphism₁⇐ : {A B : Set} (mb : Monoid B) (h : List A → B) → MonoidHomomorphism (listMonoid A) mb
  homomorphism₁⇐ {A} mb h = mk (foldr _+M_ e ∘ map (h ∘ [_])) (mk refl (λ xs ys → 
    (foldr _+M_ e ∘ map (h ∘ [_])) (xs ++ ys)
      ≡⟨ map-fusion _+M_ e (h ∘ [_]) (xs ++ ys) ⟩
    foldr (_+M_ ∘ (h ∘ [_])) e (xs ++ ys)
      ≡⟨ go xs ys ⟩
    ( foldr (_+M_ ∘ (h ∘ [_])) e xs) +M (foldr (_+M_ ∘ (h ∘ [_])) e ys)
      ≡⟨ ≡-cong₂ (λ c1 c2 → _+M_ c1 c2) 
                   (≡-sym (map-fusion _+M_ e (h ∘ [_]) xs)) 
                   (≡-sym (map-fusion _+M_ e (h ∘ [_]) ys)) ⟩
    (foldr _+M_ e (map (h ∘ [_]) xs)) +M (foldr _+M_ e (map (h ∘ [_]) ys))
      ≡∎)) where
    open Monoid mb
    go : (xs ys : List A) → foldr (_+M_ ∘ (λ x1 → h  [ x1 ]) ) e (xs ++ ys) ≡ 
      (foldr (_+M_ ∘ (h ∘ [_])) e xs) +M (foldr (_+M_ ∘ (h ∘ [_])) e ys)
    go [] ys = 
      foldr (_+M_ ∘ (h ∘ [_])) e ([] ++ ys)
        ≡⟨ ≡-sym (left-unit (foldr (_+M_ ∘ (h ∘ [_])) e ([] ++ ys))) ⟩
      (foldr (_+M_ ∘ (h ∘ [_])) e []) +M (foldr (_+M_ ∘ (h ∘ [_])) e ys)
        ≡∎
    go (x ∷ xs) ys = 
      foldr (_+M_ ∘ (h ∘ [_])) e ((x ∷ xs) ++ ys)
        ≡⟨ ≡-cong (λ c → foldr (_+M_ ∘ (h ∘ [_])) c [ x ]) (go xs ys) ⟩
      foldr (_+M_ ∘ (h ∘ [_])) ((foldr (_+M_ ∘ (h ∘ [_])) e xs) +M (foldr (_+M_ ∘ (h ∘ [_])) e ys)) [ x ]
        ≡⟨ assoc (h [ x ]) (foldr (_+M_ ∘ (h ∘ [_])) e xs) (foldr (_+M_ ∘ (h ∘ [_])) e ys) ⟩
      (foldr (_+M_ ∘ (h ∘ [_])) e (x ∷ xs)) +M
        (foldr (_+M_ ∘ (h ∘ [_])) e ys)
        ≡∎

  homomorphism₂₁ : {A B : Set} (mb : Monoid B) (mh : MonoidHomomorphism (listMonoid A) mb) →
    ∃ (A → B → B) (λ f → (xs : List A) → 
     let open Monoid mb in 
     let open MonoidHomomorphism mh in
     h xs ≡ foldr f e xs)
  homomorphism₂₁ {A} {B} mb mh = mkf , (λ xs → 
    h xs
      ≡⟨ go xs ⟩
    foldr mkf e xs
      ≡∎) where
    open Monoid mb
    open MonoidHomomorphism mh
    mkf : A → B → B
    mkf x y = (h [ x ]) +M y
    go : (xs : List A) → h xs ≡ foldr mkf e xs
    go [] = unit
    go (x ∷ xs) =
      h (x ∷ xs)
        ≡⟨ respects [ x ] xs ⟩
      (h [ x ]) +M (h xs)
        ≡⟨ ≡-cong (λ c → h [ x ] +M c) (go xs) ⟩
      foldr mkf e (x ∷ xs)
        ≡∎ 

  homomorphism₂₂ : {A B : Set} (mb : Monoid B) (mh : MonoidHomomorphism (listMonoid A) mb) →
    ∃ (B → A → B) (λ f → (xs : List A) →
    let open Monoid mb in 
    let open MonoidHomomorphism mh in
    h xs ≡ foldl f e xs)
  homomorphism₂₂ {A} {B} mb mh = mkf , (λ xs → 
    h xs
      ≡⟨ go xs ⟩
    foldl mkf (h []) xs
      ≡⟨ ≡-cong (λ c → foldl mkf c xs) unit ⟩
    foldl mkf e xs
      ≡∎) where
    open Monoid mb
    open MonoidHomomorphism mh
    mkf : B → A → B
    mkf x y = x +M (h [ y ]) 
    go : (xs : List A) → (h xs) ≡ foldl mkf (h []) xs
    go [] = refl
    go (x ∷ xs) = 
      h (x ∷ xs)
        ≡⟨ respects [ x ] xs ⟩
      h [ x ] +M h xs
        ≡⟨ ≡-cong (λ c → h [ x ] +M c) (go xs) ⟩
      h [ x ] +M foldl mkf (h []) xs
        ≡⟨ foldl-fusion mkf mkf (h []) (_+M_ (h [ x ])) (λ y z → assoc (h [ x ]) y (h [ z ])) xs ⟩
      foldl mkf (h [ x ] +M h []) xs
        ≡⟨ ≡-cong (λ c → foldl mkf c xs) (≡-sym (respects (x ∷ []) [])) ⟩
      foldl mkf (h [ x ]) xs
        ≡⟨ ≡-cong (λ c → foldl mkf c xs) (respects [] (x ∷ [])) ⟩
      foldl mkf (mkf (h []) x) xs
        ≡∎

  rightInvertibleSemigroup : {A B : Set} (hri : WeakInvertible (List A) B) →
    let open WeakInvertible hri in
    ((vs ws xs ys : List A) → h vs ≡ h xs → h ws ≡ h ys → h (vs ++ ws) ≡ h (xs ++ ys)) → Semigroup B
  rightInvertibleSemigroup {A} {B} hri h1 = mk (λ x y → h (h- x ++ h- y)) (mk (λ x y z → 
    h (h- x ++ h- (h (h- y ++ h- z)))
      ≡⟨ h1 (h- x) (h- (h (h- y ++ h- z))) (h- x) (h- y ++ h- z) refl (apply (h- y ++ h- z)) ⟩
    h (h- x ++ h- y ++ h- z)
      ≡⟨ ≡-cong (λ c → h c) (++-assoc (h- x) (h- y) (h- z)) ⟩
    h ((h- x ++ h- y) ++ h- z)
      ≡⟨ ≡-sym (h1 (h- (h (h- x ++ h- y))) (h- z) (h- x ++ h- y) (h- z) (apply (h- x ++ h- y)) refl) ⟩
    h (h- (h (h- x ++ h- y)) ++ h- z)
      ≡∎)) where 
    open WeakInvertible hri 

  homomorphism₃-lemma : {A B : Set} (hri : WeakInvertible (List A) B) → 
    let open WeakInvertible hri in 
    (f : A → B → B) (hf : (xs : List A) → h xs ≡ foldr f (h []) xs)
    (f' : B → A → B) (hg : (xs : List A) → h xs ≡ foldl f' (h []) xs) → 
    (vs ws xs ys : List A) → h vs ≡ h xs → h ws ≡ h ys → h (vs ++ ws) ≡ h (xs ++ ys)
  homomorphism₃-lemma hri f hf f' hf' vs ws xs ys h1 h2 = 
    h (vs ++ ws)
      ≡⟨ hf (vs ++ ws) ⟩
    foldr f (h []) (vs ++ ws)
      ≡⟨ foldr-++₁ f (h []) vs ws ⟩
    foldr f (foldr f (h []) ws) vs
      ≡⟨ ≡-cong (λ c → foldr f c vs) (
      foldr f (h []) ws
        ≡⟨ ≡-sym (hf ws) ⟩
      h ws
        ≡⟨ h2 ⟩
      h ys
        ≡⟨ hf ys ⟩
      foldr f (h []) ys
        ≡∎) ⟩    
    foldr f (foldr f (h []) ys) vs
      ≡⟨ ≡-sym (foldr-++₁ f (h []) vs ys) ⟩
    foldr f (h []) (vs ++ ys)
      ≡⟨ ≡-sym (hf (vs ++ ys)) ⟩
    h (vs ++ ys)
      ≡⟨ hf' (vs ++ ys) ⟩
    foldl f' (h []) (vs ++ ys)
      ≡⟨ foldl-++₁ f' (h []) vs ys ⟩
    foldl f' (foldl f' (h []) vs) ys
      ≡⟨ ≡-cong (λ c → foldl f' c ys) (
      foldl f' (h []) vs
        ≡⟨ ≡-sym (hf' vs) ⟩
      h vs
        ≡⟨ h1 ⟩
      h xs
        ≡⟨ hf' xs ⟩
      foldl f' (h []) xs
        ≡∎) ⟩
    foldl f' (foldl f' (h []) xs) ys
      ≡⟨ ≡-sym (foldl-++₁ f' (h []) xs ys) ⟩
    foldl f' (h []) (xs ++ ys)
      ≡⟨ ≡-sym (hf' (xs ++ ys)) ⟩
    h (xs ++ ys)
      ≡∎ where
    open WeakInvertible hri

  homomorphism₃ : {A B : Set} (hri : WeakInvertible (List A) B) → 
    let open WeakInvertible hri in 
    (f : A → B → B) (hf : (xs : List A) → h xs ≡ foldr f (h []) xs)
    (g : B → A → B) (hg : (xs : List A) → h xs ≡ foldl g (h []) xs) → 
    IsSemigroupHomomorphism (Monoid.semigroup (listMonoid A)) (rightInvertibleSemigroup hri (homomorphism₃-lemma hri f hf g hg)) h
  homomorphism₃ {A} {B} hri f hf g hg = mk (λ xs ys → (homomorphism₃-lemma hri f hf g hg) xs ys (h- (h xs)) (h- (h ys)) (≡-sym (apply xs)) (≡-sym (apply ys))) where
    open Semigroup (rightInvertibleSemigroup hri (homomorphism₃-lemma hri f hf g hg))
    open WeakInvertible hri


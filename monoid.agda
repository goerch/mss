--open import Agda.Builtin.Equality
--open import Agda.Builtin.List

open import prelude
open import list

module _ where

  record IsLeftInverse (A B : Set) (hl- : B → A) (h : A → B) : Set where
    constructor mk
    field
      apply : (x : A) → (hl- ∘ h) x ≡ x

  record LeftInverse (A B : Set) : Set where
    constructor mk
    field
      hl- : B → A
      h : A → B
      isLeftInverse : IsLeftInverse A B hl- h
    open IsLeftInverse isLeftInverse public

  record IsRightInverse (A B : Set) (h : A → B) (hr- : B → A) : Set where
    constructor mk
    field
      apply : (y : B) → (h ∘ hr-) y ≡ y

  record RightInverse (A B : Set) : Set where
    constructor mk
    field
      h : A → B
      hr- : B → A
      isRightInverse : IsRightInverse A B h hr-
    open IsRightInverse isRightInverse public

  record IsMonoid (A : Set) (_+M_ : A → A → A) (e : A) : Set where
    constructor mk
    field
      left-unit : (x : A) → e +M x ≡ x
      right-unit : (x : A) → x +M e ≡ x
      assoc : (x y z : A) → (x +M y) +M z ≡ x +M (y +M z)

  record Monoid (A : Set) : Set where
    constructor mk
    field
      _+M_ : A → A → A
      e : A
      isMonoid : IsMonoid A _+M_ e
    open IsMonoid isMonoid public

  listMonoid : (A : Set) → Monoid (List A)
  listMonoid A = mk _++_ [] (mk (λ x → refl) (λ x → ++-unit x) (λ x y z → ++-assoc x y z))

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

  homomorphism₁⇒ : {A B : Set} (mb : Monoid B) (mh : MonoidHomomorphism (listMonoid A) mb) →
    ∃ (Monoid B) (λ mb' → (xs : List A) → 
    let open Monoid mb' in 
    let open MonoidHomomorphism mh in
    h xs ≡ (foldr (_+M_) e ∘ map (λ x → h [ x ])) xs)
  homomorphism₁⇒ {A} {B} mb mh = 
    mk (_+M_) e (mk left-unit right-unit assoc), (λ xs → go xs) where 
    open Monoid mb
    open MonoidHomomorphism mh
    go : (xs : List A) → h xs ≡ (foldr (_+M_) e ∘ map (λ x → h [ x ])) xs
    go [] = unit
    go (x ∷ xs) =
      h (x ∷ xs) 
        ≡⟨ respects [ x ] xs ⟩
      h [ x ] +M h xs 
        ≡⟨ ≡-cong (λ c → (h [ x ]) +M c) (go xs) ⟩
      h [ x ] +M (foldr _+M_ e ∘ map (λ x₁ → h [ x₁ ])) xs 
        ≡⟨ ≡-cong (λ c → (h [ x ]) +M c) (map-fusion (_+M_) e (λ x1 → h [ x1 ]) xs) ⟩
      h [ x ] +M foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs 
        ≡⟨ ≡-sym (map-fusion (_+M_) e (λ x1 → h [ x1 ]) (x ∷ xs)) ⟩ 
      (foldr _+M_ e ∘ map (λ x₁ → h [ x₁ ])) (x ∷ xs) 
        ≡∎ 
    
  homomorphism₁⇐ : {A B : Set} (mb : Monoid B) (h : List A → B) → MonoidHomomorphism (listMonoid A) mb
  homomorphism₁⇐ {A} mb h = mk (foldr (_+M_) e ∘ map (λ x → h [ x ])) (mk refl (λ xs ys → 
    (foldr _+M_ e ∘ map (λ x1 → h [ x1 ])) (xs ++ ys)
      ≡⟨ map-fusion _+M_ e (λ x1 → h [ x1 ]) (xs ++ ys) ⟩
    foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e (xs ++ ys)
      ≡⟨ go xs ys ⟩
    ( foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs) +M (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)
      ≡⟨ ≡-cong₂ (λ c1 c2 → _+M_ c1 c2) 
                   (≡-sym (map-fusion _+M_ e (λ x1 → h [ x1 ]) xs)) 
                   (≡-sym (map-fusion _+M_ e (λ x1 → h [ x1 ]) ys)) ⟩
    (foldr _+M_ e (map (λ x → h [ x ]) xs)) +M (foldr _+M_ e (map (λ x → h [ x ]) ys))
      ≡∎)) where
    open Monoid mb
    go : (xs ys : List A) → foldr (_+M_ ∘ (λ x1 → h  [ x1 ]) ) e (xs ++ ys) ≡ 
      (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs) +M (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)
    go [] ys = 
      foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ([] ++ ys)
        ≡⟨ ≡-sym (left-unit (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ([] ++ ys))) ⟩
      (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e []) +M (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)
        ≡∎
    go (x ∷ xs) ys = 
      foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ((x ∷ xs) ++ ys)
        ≡⟨ foldr-decomp (_+M_ ∘ (λ x1 → h [ x1 ])) e [ x ] (xs ++ ys) ⟩
      foldr (_+M_ ∘ (λ x1 → h [ x1 ])) (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e (xs ++ ys)) [ x ]
        ≡⟨ ≡-cong (λ c → foldr (_+M_ ∘ (λ x1 → h [ x1 ])) c [ x ]) (go xs ys) ⟩
      foldr (_+M_ ∘ (λ x1 → h [ x1 ])) ((foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs) +M (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)) [ x ]
        ≡⟨ ≡-sym (assoc (h [ x ]) (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs) (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)) ⟩
      (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e xs) [ x ]) +M (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)
        ≡⟨ ≡-cong ((λ c → _+M_ c (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys))) (≡-sym (foldr-decomp (_+M_ ∘ (λ x1 → h [ x1 ])) e [ x ] xs)) ⟩
      (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e (x ∷ xs)) +M
        (foldr (_+M_ ∘ (λ x1 → h [ x1 ])) e ys)
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
        ≡⟨ ≡-cong (λ c → (h [ x ]) +M c) (go xs) ⟩
      foldr mkf (foldr mkf e xs) [ x ]
        ≡⟨ ≡-sym (foldr-decomp mkf e [ x ] xs) ⟩
      foldr mkf e (x ∷ xs)
        ≡∎ 

  homomorphism₂₂ : {A B : Set} (mb : Monoid B) (mh : MonoidHomomorphism (listMonoid A) mb) →
    ∃ (B → A → B) (λ f → (xs : List A) →
    let open Monoid mb in 
    let open MonoidHomomorphism mh in
    h xs ≡ foldl f e xs)
  homomorphism₂₂ {A} {B} mb mh = mkf , (λ xs → 
    h xs
      ≡⟨ ≡-sym (left-unit (h xs)) ⟩
    e +M (h xs)
      ≡⟨ ≡-cong (λ c → c +M (h xs)) (≡-sym unit) ⟩
    (h []) +M (h xs)
      ≡⟨ go [] xs ⟩
    foldl mkf (h []) xs
      ≡⟨ ≡-cong (λ c → foldl mkf c xs) unit ⟩
    foldl mkf e xs
      ≡∎) where
    open Monoid mb
    open MonoidHomomorphism mh
    mkf : B → A → B
    mkf x y = x +M (h [ y ]) 
    go : (xs ys : List A) → (h xs) +M (h ys) ≡ foldl mkf (h xs) ys
    go xs [] = 
      (h xs) +M (h [])
        ≡⟨ ≡-cong (λ c → (h xs) +M c) unit ⟩
      (h xs) +M e
        ≡⟨ right-unit (h xs) ⟩
      h xs
        ≡∎
    go xs (y ∷ ys) =
      (h xs) +M (h (y ∷ ys))
        ≡⟨ ≡-sym (respects xs (y ∷ ys)) ⟩
      h (xs ++ (y ∷ ys))
        ≡⟨ ≡-cong (λ c → h c) (≡-sym (++-assoc xs [ y ] ys)) ⟩
      h ((xs ++ y ∷ []) ++ ys)
        ≡⟨ respects (xs ++ y ∷ []) ys ⟩
      (h (xs ++ y ∷ [])) +M (h ys)
        ≡⟨ go (xs ++ y ∷ []) ys ⟩
      foldl mkf (h (xs ++ [ y ])) ys
        ≡⟨ ≡-cong (λ c → foldl mkf c ys) (respects xs [ y ]) ⟩
      foldl mkf (h xs) (y ∷ ys)
        ≡∎
    
  rightInverseMonoid : {A B : Set} (hri : RightInverse (List A) B) →
    let open RightInverse hri in
    ((vs ws xs ys : List A) → h vs ≡ h xs → h ws ≡ h ys → h (vs ++ ws) ≡ h (xs ++ ys)) → Monoid B
  rightInverseMonoid {A} {B} hri h1 = mk (λ x y → h ((hr- x) ++ (hr- y))) (h []) (mk (λ x → 
    h (hr- (h []) ++ hr- x)
      ≡⟨ h1 (hr- (h [])) (hr- x) ([]) (hr- x) (apply (h [])) refl ⟩
    h (hr- x)
      ≡⟨ apply x ⟩
    x
      ≡∎) (λ x → 
    h (hr- x ++ hr- (h []))
      ≡⟨ h1 (hr- x) (hr- (h [])) (hr- x) ([]) refl (apply (h [])) ⟩
    h (hr- x ++ [])
      ≡⟨ ≡-cong (λ c → h c) (++-unit (hr- x)) ⟩
    h (hr- x)
      ≡⟨ apply x ⟩
    x
      ≡∎) (λ x y z → 
    h (hr- (h (hr- x ++ hr- y)) ++ hr- z)
      ≡⟨ h1 (hr- (h (hr- x ++ hr- y))) (hr- z) (hr- x ++ hr- y) (hr- z) (apply (h (hr- x ++ hr- y))) refl ⟩
    h ((hr- x ++ hr- y) ++ hr- z)
      ≡⟨ ≡-cong (λ c → h c) (++-assoc (hr- x) (hr- y) (hr- z)) ⟩
    h (hr- x ++ hr- y ++ hr- z)
      ≡⟨ ≡-sym (h1 (hr- x) (hr- (h (hr- y ++ hr- z))) (hr- x) (hr- y ++ hr- z) refl (apply (h (hr- y ++ hr- z)))) ⟩
    h (hr- x ++ hr- (h (hr- y ++ hr- z)))
      ≡∎)) where
    open RightInverse hri 

  homomorphism₃-lemma : {A B : Set} (hri : RightInverse (List A) B) → 
    let open RightInverse hri in 
    (f : A → B → B) (hf : (xs : List A) → h xs ≡ foldr f (h []) xs)
    (g : B → A → B) (hg : (xs : List A) → h xs ≡ foldl g (h []) xs) → 
    (vs ws xs ys : List A) → h vs ≡ h xs → h ws ≡ h ys → h (vs ++ ws) ≡ h (xs ++ ys)
  homomorphism₃-lemma hri f hf g hg vs ws xs ys h1 h2 = 
    h (vs ++ ws)
      ≡⟨ hf (vs ++ ws) ⟩
    foldr f (h []) (vs ++ ws)
      ≡⟨ foldr-decomp f (h []) vs ws ⟩
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
      ≡⟨ ≡-sym (foldr-decomp f (h []) vs ys) ⟩
    foldr f (h []) (vs ++ ys)
      ≡⟨ ≡-sym (hf (vs ++ ys)) ⟩
    h (vs ++ ys)
      ≡⟨ hg (vs ++ ys) ⟩
    foldl g (h []) (vs ++ ys)
      ≡⟨ foldl-decomp g (h []) vs ys ⟩
    foldl g (foldl g (h []) vs) ys
      ≡⟨ ≡-cong (λ c → foldl g c ys) (
      foldl g (h []) vs
        ≡⟨ ≡-sym (hg vs) ⟩
      h vs
        ≡⟨ h1 ⟩
      h xs
        ≡⟨ hg xs ⟩
      foldl g (h []) xs
        ≡∎) ⟩
    foldl g (foldl g (h []) xs) ys
      ≡⟨ ≡-sym (foldl-decomp g (h []) xs ys) ⟩
    foldl g (h []) (xs ++ ys)
      ≡⟨ ≡-sym (hg (xs ++ ys)) ⟩
    h (xs ++ ys)
      ≡∎ where
    open RightInverse hri

  homomorphism₃ : {A B : Set} (hri : RightInverse (List A) B) → 
    let open RightInverse hri in 
    (f : A → B → B) (hf : (xs : List A) → h xs ≡ foldr f (h []) xs)
    (g : B → A → B) (hg : (xs : List A) → h xs ≡ foldl g (h []) xs) → IsMonoidHomomorphism (listMonoid A) (rightInverseMonoid hri (homomorphism₃-lemma hri f hf g hg)) h
  homomorphism₃ {A} {B} hri f hf g hg = mk refl (λ xs ys → (homomorphism₃-lemma hri f hf g hg) xs ys (hr- (h xs)) (hr- (h ys)) (≡-sym (apply (h xs))) (≡-sym (apply (h ys))) ) where    
    open Monoid (rightInverseMonoid hri (homomorphism₃-lemma hri f hf g hg))
    open RightInverse hri

open import Agda.Builtin.Equality

open import prelude

module _ where

  {- Non empty lists -}

  infixr 5 _∷+_
  data List+ (A : Set) : Set where
    [_]+ : (x : A) → List+ A
    _∷+_ : (x : A) (xs : List+ A) → List+ A

  ∷+-injective : {A : Set} {x y : A} {xs ys : List+ A} → x ∷+ xs ≡ y ∷+ ys → x ≡ y ∧ xs ≡ ys
  ∷+-injective refl = refl , refl
  ∷+-cong : {A : Set} {x y : A} {xs ys : List+ A} → x ≡ y → xs ≡ ys → x ∷+ xs ≡ y ∷+ ys
  ∷+-cong refl refl = refl
 
  infixr 5 _+++_
  _+++_ : {A : Set} → List+ A →  List+ A → List+ A
  [ x ]+ +++ ys = x ∷+ ys
  (x ∷+ xs) +++ ys = x ∷+ (xs +++ ys)

  +++-assoc : {A : Set} (xs ys zs : List+ A) → xs +++ (ys +++ zs) ≡ (xs +++ ys) +++ zs
  +++-assoc [ x ]+ ys zs = refl
  +++-assoc (x ∷+ xs) ys zs = ∷+-cong refl (+++-assoc xs ys zs)

  foldl+ : {A B : Set} → (B → A → B) → (A → B) → List+ A → B
  foldl+ f g [ x ]+ = g x
  foldl+ f g (x ∷+ xs) = foldl+ f (f (g x)) xs

  foldl+-cong : {A B : Set} (f f' : B → A → B) (g g' : A → B) → 
    ((x : B) (y : A) → f x y ≡ f' x y) → ((x : A) → g x ≡ g' x) → 
    ((xs : List+ A) → foldl+ f g xs ≡ foldl+ f' g' xs)
  foldl+-cong f f' g g' h1 h2 [ x ]+ = h2 x
  foldl+-cong f f' g g' h1 h2 (x ∷+ xs) = 
    foldl+ f (f (g x)) xs
      ≡⟨ foldl+-cong f f' (f (g x)) (f' (g' x)) h1 (λ x' → 
       f (g x) x'
         ≡⟨ ≡-cong (λ c → f c x') (h2 x) ⟩
       f (g' x) x'
         ≡⟨ h1 (g' x) x' ⟩
       f' (g' x) x'
         ≡∎) xs ⟩
    foldl+ f' (f' (g' x)) xs
      ≡∎

  foldl+-univ₁ : {A B : Set} (f : B → A → B) (h : (A → B) → List+ A → B) → 
    ((g : A → B) (x : A) → h g [ x ]+ ≡ g x) →
    ((g : A → B) (x : A) (xs : List+ A) → h g (x ∷+ xs) ≡ h (f (g x)) xs) →  
    (g : A → B) (xs : List+ A) → h g xs ≡ foldl+ f g xs
  foldl+-univ₁ f h h1 h2 g [ x ]+ = h1 g x
  foldl+-univ₁ f h h1 h2 g (x ∷+ xs) =
    h g (x ∷+ xs)
      ≡⟨ h2 g x xs  ⟩ 
    h (f (g x)) xs
      ≡⟨ foldl+-univ₁ f h h1 h2 (f (g (x))) xs ⟩
    foldl+ f (f (g x)) xs
      ≡∎

  foldl+-univ₂ : {A B : Set} (f : B → A → B) (h : (A → B) → List+ A → B) → 
    ((g : A → B) (xs : List+ A) → h g xs ≡ foldl+ f g xs) → 
    ((g : A → B) (x : A) → h g [ x ]+ ≡ g x) ∧ ((g : A → B) (x : A) (xs : List+ A) → h g (x ∷+ xs) ≡ h (f (g x)) xs) 
  foldl+-univ₂ f h h1 = (λ g x → h1 g [ x ]+) , (λ g x xs → 
    h g (x ∷+ xs)
      ≡⟨ h1 g (x ∷+ xs) ⟩
    foldl+ f g (x ∷+ xs)
      ≡⟨ ≡-sym (h1 (f (g x)) xs) ⟩
    h (f (g x)) xs
      ≡∎)

  foldl+-fusion : {A B C : Set} (f : B → A → B) (f' : C → A → C) (g : A → B) (h : B → C) → 
    ((x : B) (y : A) → h (f x y) ≡ f' (h x) y) →  
     (xs : List+ A) → (h ∘ foldl+ f  g) xs ≡ foldl+ f' (h ∘ g) xs
  foldl+-fusion f f' g h h1  [ x ]+ = refl
  foldl+-fusion f f' g h h1 (x ∷+ xs) = 
    (h ∘ foldl+ f (f (g x))) xs
      ≡⟨ foldl+-fusion f f' (f (g x)) h h1 xs ⟩
    foldl+ f' (h ∘ f (g x)) xs 
      -- ≡-cong (λ c → foldl+ f' c xs) (funext (h ∘ f (g x)) (f' (h (g x))) (h1 (g x))) ⟩
      ≡⟨ foldl+-cong f' f' (λ z → h (f (g x) z)) (f' (h (g x))) (λ x y → refl) (h1 (g x)) xs ⟩ 
    foldl+ f' (f' (h (g x))) xs
      ≡∎

  foldl+-+++₁ : {A B : Set} (f : B → A → B) (g : A → B) (xs ys : List+ A) → 
    foldl+ f g (xs +++ ys) ≡ foldl+ f (λ y → foldl+ f g (xs +++ [ y ]+)) ys
  foldl+-+++₁ f g [ x ]+ ys = refl
  foldl+-+++₁ f g (x ∷+ xs) ys = foldl+-+++₁ f (f (g x)) xs ys 

  foldl+-+++₂ : {A : Set} (f : A → A → A) → 
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs ys : List+ A) → foldl+ f id (xs +++ ys) ≡ f (foldl+ f id xs) (foldl+ f id ys) 
  foldl+-+++₂ f assoc [ x ]+ ys = ≡-sym (foldl+-fusion f f id (f x) (assoc x) ys) 
  foldl+-+++₂ f assoc (x ∷+ xs) ys = 
    foldl+ f (f x) (xs +++ ys)
      ≡⟨ ≡-sym (foldl+-fusion f f id (f x) (assoc x) (xs +++ ys)) ⟩ 
    (f x ∘ foldl+ f id) (xs +++ ys)
      ≡⟨ ≡-cong (λ c → f x c) (foldl+-+++₂ f assoc xs ys) ⟩
    f x (f (foldl+ f id xs) (foldl+ f id ys))
      ≡⟨ assoc x (foldl+ f id xs) (foldl+ f id ys) ⟩
    f ((f x ∘ foldl+ f id) xs) (foldl+ f id ys)
      ≡⟨ ≡-cong (λ c → f c (foldl+ f id ys)) (foldl+-fusion f f id (f x) (assoc x) xs) ⟩
    f (foldl+ f (f x) xs) (foldl+ f id ys)
      ≡∎

  foldr+ : {A B : Set} → (A → B → B) → (A → B) → List+ A → B
  foldr+ f g [ x ]+ = g x
  foldr+ f g (x ∷+ xs) = f x (foldr+ f g xs)

  foldr+-cong : {A B : Set} (f f' : A → B → B) (g g' : A → B) → 
    ((x : A) (y : B) → f x y ≡ f' x y) → ((x : A) → g x ≡ g' x) → 
    ((xs : List+ A) → foldr+ f g xs ≡ foldr+ f' g' xs)
  foldr+-cong f f' g g' h1 h2 [ x ]+ = h2 x
  foldr+-cong f f' g g' h1 h2 (x ∷+ xs) = 
    f x (foldr+ f g xs)
      ≡⟨ ≡-cong (λ c → f x c) (foldr+-cong f f' g g' h1 h2 xs) ⟩
    f x (foldr+ f' g' xs)
      ≡⟨ h1 x (foldr+ f' g' xs) ⟩
    f' x (foldr+ f' g' xs)
      ≡∎

  foldr+-univ₁ : {A B : Set} (f : A → B → B) (g : A → B) (h : List+ A → B) → 
    ((x : A) → h [ x ]+ ≡ g x) →
    ((x : A) (xs : List+ A) → h (x ∷+ xs) ≡ f x (h xs)) →  
    (xs : List+ A) → h xs ≡ foldr+ f g xs
  foldr+-univ₁ f g h h1 h2 [ x ]+ = h1 x
  foldr+-univ₁ f g h h1 h2 (x ∷+ xs) =
    h (x ∷+ xs)
      ≡⟨ h2 x xs ⟩
    f x (h xs)
      ≡⟨ ≡-cong (f x) (foldr+-univ₁ f g h h1 h2 xs) ⟩
    f x (foldr+ f g xs)
      ≡∎

  foldr+-univ₂ : {A B : Set} (f : A → B → B) (g : A → B) (h : List+ A → B) → 
    ((xs : List+ A) → h xs ≡ foldr+ f g xs) → 
    ((x : A) → h [ x ]+ ≡ g x) ∧ ((x : A) (xs : List+ A) → h (x ∷+ xs) ≡ f x (h xs)) 
  foldr+-univ₂ f e h h1 = (λ x → h1 [ x ]+) ,  λ x xs → (
    h (x ∷+ xs)
      ≡⟨ h1 (x ∷+ xs) ⟩
    f x (foldr+ f e xs)
      ≡⟨ ≡-cong (λ c → f x c) (≡-sym (h1 xs)) ⟩
    f x (h xs)
      ≡∎)
  
  foldr+-fusion : {A B C : Set} (f : A → B → B) (f' : A → C → C) (g : A → B) (h : B → C) → 
    ((x : A) (y : B) → h (f x y) ≡ f' x (h y)) →  
     (xs : List+ A) → (h ∘ foldr+ f  g) xs ≡ foldr+ f' (h ∘ g) xs
  foldr+-fusion f f' g h h1 [ x ]+ = refl
  foldr+-fusion f f' g h h1 (x ∷+ xs) = 
    h (f x (foldr+ f g xs))
      ≡⟨ h1 x (foldr+ f g xs) ⟩
    f' x (h (foldr+ f g xs))
      ≡⟨ ≡-cong (λ c → f' x c) (foldr+-fusion f f' g h h1 xs) ⟩
    f' x (foldr+ f' (h ∘ g) xs)
      ≡∎

  foldr+-+++₁ : {A B : Set} (f : A → B → B) (g : A → B) (xs ys : List+ A) → 
    foldr+ f g (xs +++ ys) ≡ foldr+ f (λ y → foldr+ f g (y ∷+ ys)) xs
  foldr+-+++₁ f g [ x ]+ ys = refl
  foldr+-+++₁ f g (x ∷+ xs) ys = ≡-cong (λ c → f x c) (foldr+-+++₁ f g xs ys) 

  foldr+-+++₂ : {A : Set} (f : A → A → A) → 
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs ys : List+ A) → foldr+ f id (xs +++ ys) ≡ f (foldr+ f id xs) (foldr+ f id ys) 
  foldr+-+++₂ f assoc [ x ]+ ys = refl
  foldr+-+++₂ f assoc (x ∷+ xs) ys = 
    f x (foldr+ f id (xs +++ ys))
      ≡⟨ ≡-cong (λ c → f x c) (foldr+-+++₂ f assoc xs ys) ⟩ 
    f x (f (foldr+ f id xs) (foldr+ f id ys))
      ≡⟨ assoc x (foldr+ f id xs) (foldr+ f id ys) ⟩
    f (f x (foldr+ f id xs)) (foldr+ f id ys)
      ≡∎

  fold+-dual₁ : {A : Set} (f : A → A → A)  
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs : List+ A) → foldr+ f id xs ≡ foldl+ f id xs
  fold+-dual₁ f assoc [ x ]+ = refl
  fold+-dual₁ {A} f assoc (x ∷+ xs) = 
    f x (foldr+ f id xs)
      ≡⟨ ≡-cong (λ c → f x c) (fold+-dual₁ f assoc xs) ⟩
    f x (foldl+ f id xs)
      ≡⟨ foldl+-fusion f f id (f x) (assoc x) xs ⟩ 
    foldl+ f (f x) xs
      ≡∎ 

  id-as-foldr+ : {A : Set} (xs : List+ A) → id xs ≡ foldr+ (λ x1 x2  → (x1 ∷+ x2)) (λ x → [ x ]+) xs 
  id-as-foldr+ xs = foldr+-univ₁ (λ x1 x2 → x1  ∷+ x2) (λ x → [ x ]+) id (λ x → refl) (λ x xs → refl) xs

  +++-cong : {A : Set} {xs xs' ys ys' : List+ A} → xs ≡ xs' → ys ≡ ys' → xs +++ ys ≡ xs' +++ ys'
  +++-cong refl refl = refl

  +++-as-foldr+ : {A : Set} (xs ys : List+ A) → 
    xs +++ ys ≡ foldr+ (λ x1 x2 → x1 ∷+ x2) (λ x →  x ∷+ ys)  xs 
  +++-as-foldr+ [ x ]+ ys = refl
  +++-as-foldr+ (x ∷+ xs) ys = ∷+-cong refl (+++-as-foldr+ xs ys) 

  map+ : {A B : Set} → (A → B) → List+ A → List+ B
  map+ f [ x ]+ = [ f x ]+
  map+ f (x ∷+ xs) = f x ∷+ map+ f xs

  map+-cong : {A B : Set} (f f' : A → B) → ((x : A) → f x ≡ f' x) → 
    ((xs : List+ A) → map+ f xs ≡ map+ f' xs)
  map+-cong f f' h1 [ x ]+ = ≡-cong (λ c → [ c ]+) (h1 x) 
  map+-cong f f' h1 (x ∷+ xs) =  ∷+-cong (h1 x) (map+-cong f f' h1 xs) 

  map+-as-foldr+ : {A B : Set} (f : A → B) (xs : List+ A) → 
    map+ f xs ≡ foldr+ (λ x1 x2 → f x1 ∷+ x2) (λ x → [ f x ]+) xs 
  map+-as-foldr+ f xs = foldr+-univ₁ (λ x1 x2 → f x1  ∷+ x2) (λ x → [ f x ]+) (map+ f) (λ x → refl) (λ x xs → refl) xs

  map+-id : {A : Set} (xs : List+ A) → map+ {A} id xs ≡ id xs
  map+-id [ x ]+ = refl
  map+-id (x ∷+ xs) = ∷+-cong refl (map+-id xs) 

  map+-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List+ A) → 
    map+ (f ∘ g) xs ≡ (map+ f ∘ map+ g) xs
  map+-compose f g [ x ]+ = refl
  map+-compose f g (x ∷+ xs) = ∷+-cong refl (map+-compose f g xs) 

  map+-fusion : {A B C : Set} (f : A → B → B) (g : A → B) (h : C → A) (xs : List+ C)  →  
    (foldr+ f  g ∘ map+ h) xs ≡ foldr+ (f ∘ h) (g ∘ h) xs
  map+-fusion f g h [ x ]+ = refl
  map+-fusion f g h (x ∷+ xs) = ≡-cong (λ c → f (h x) c) (map+-fusion f g h xs) 

  map+-+++ : {A B : Set} (f : A → B) (xs ys : List+ A) → map+ f (xs +++ ys) ≡ (map+ f xs +++ map+ f ys)
  map+-+++ f [ x ]+ ys = refl
  map+-+++ f (x ∷+ xs) ys = ∷+-cong refl (map+-+++ f xs ys) 

  first+ : {A : Set} (xs : List+ A) → A
  first+ xs = foldr+ (λ x1 x2 → x1) id xs 

  last+ : {A : Set} (xs : List+ A) → A
  last+ xs = foldr+ (λ x1 x2 → x2) id xs 

  inits+ : {A : Set} (xs : List+ A) → List+ (List+ A)
  inits+ xs = foldr+ (λ x1 x2 → [ x1 ]+ ∷+ (map+ (_∷+_ x1) x2)) ([_]+ ∘ [_]+) xs
--  inits+ xs = foldr+ (λ x1 x2 → x2 +++ [ last+ x2 +++ [ x1 ]+ ]+) (λ x → [ [ x ]+ ]+) xs

  tails+ : {A : Set} (xs : List+ A) → List+ (List+ A)
  tails+ xs = foldr+ (λ x1 x2 → (x1 ∷+ first+ x2)  ∷+ x2) ([_]+ ∘ [_]+) xs
--  tails+ xs = foldr+ (λ x1 x2 → map+ (λ x → x +++ [ x1 ]+) x2 +++ [ [ x1 ]+ ]+) (λ x → [ [ x ]+ ]+) xs

  scanr+ : {A B : Set} → (A → B → B) → (A → B) → List+ A → List+ B
  scanr+ f g [ x ]+ = [ g x ]+
  scanr+ f g (x ∷+ xs) with scanr+ f g xs
  scanr+ f g (x ∷+ xs) | [ y ]+ = f x y ∷+ [ y ]+
  scanr+ f g (x ∷+ xs) | y ∷+ ys = f x y ∷+ y ∷+ ys

  scanr-derivation : {A B : Set} (f : A → B → B) (g : A → B) (xs : List+ A) → (map+ (foldr+ f g) ∘ tails+) xs ≡ scanr+ f g xs 
  scanr-derivation f g [ x ]+ = refl
  scanr-derivation f g (x1 ∷+ [ x2 ]+) = refl
  scanr-derivation f g (x1 ∷+ x2 ∷+ xs) with scanr+ f g (x2 ∷+ xs) | scanr-derivation f g (x2 ∷+ xs)
  scanr-derivation f g (x1 ∷+ x2 ∷+ xs) | [ y ]+ | ()
  scanr-derivation f g (x1 ∷+ x2 ∷+ xs) | _ ∷+ _ | refl = refl

  flatten+ : {A : Set} (xs : List+ (List+ A)) → List+ A
  flatten+ xs = foldr+ (λ x1 x2 → x1 +++ x2) id xs

  map+-flatten+ : {A B : Set} (f : A → B) (xs : List+ (List+ A)) → (map+ f ∘ flatten+) xs ≡ (flatten+ ∘ map+ (map+ f)) xs
  map+-flatten+ f xs = 
    (map+ f ∘ foldr+ _+++_ id) xs
      ≡⟨ foldr+-fusion _+++_ (_+++_ ∘ map+ f) id (map+ f) (map+-+++ f) xs ⟩
    foldr+ (_+++_ ∘ map+ f) (id ∘ map+ f) xs
      ≡⟨ ≡-sym (map+-fusion _+++_ id (map+ f) xs ) ⟩
    (foldr+ _+++_ id ∘ map+ (map+ f)) xs
      ≡∎ 

  segs+ : {A : Set} (xs : List+ A) → List+ (List+ A)
  segs+ xs = (flatten+ ∘ map+ inits+ ∘ tails+) xs
--  segs+ xs = (flatten+ ∘ map+ tails+ ∘ inits+) xs

  reverse+-spec : {A : Set} → List+ A → List+ A
  reverse+-spec [ x ]+ = [ x ]+
  reverse+-spec (x ∷+ xs) = reverse+-spec xs +++ [ x ]+

  reverse+-+++ : {A : Set} (xs ys : List+ A) → reverse+-spec (xs +++ ys) ≡ reverse+-spec ys +++ reverse+-spec xs
  reverse+-+++ [ x ]+ ys = refl
  reverse+-+++ (x ∷+ xs) ys =
    reverse+-spec (xs +++ ys) +++ [ x ]+
      ≡⟨ ≡-cong (λ c → c +++ [ x ]+) (reverse+-+++ xs  ys) ⟩
    (reverse+-spec ys +++ reverse+-spec xs) +++ [ x ]+
      ≡⟨ ≡-sym (+++-assoc (reverse+-spec ys) (reverse+-spec xs) ([ x ]+)) ⟩
    reverse+-spec ys +++ reverse+-spec (x ∷+ xs)
      ≡∎

  reverse+-reverse+ : {A : Set} (xs : List+ A) → reverse+-spec (reverse+-spec xs) ≡ xs
  reverse+-reverse+ [ x ]+ = refl
  reverse+-reverse+ (x ∷+ xs) = 
    reverse+-spec (reverse+-spec xs +++ [ x ]+)
      ≡⟨ reverse+-+++ (reverse+-spec xs) ([ x ]+) ⟩
    x ∷+ reverse+-spec (reverse+-spec xs)
      ≡⟨ ∷+-cong refl (reverse+-reverse+ xs) ⟩
    x ∷+ xs
      ≡∎

  fold+-dual₂ : {A B : Set} (f : A → B → B) (g : A → B) (xs : List+ A) → foldr+ f g xs ≡ foldl+ (λ x1 x2 → f x2 x1) g (reverse+-spec xs)
  fold+-dual₂ f g [ x ]+ = refl
  fold+-dual₂ f g (x ∷+ [ y ]+) = refl
  fold+-dual₂ f g (x ∷+ y ∷+ ys) = 
    foldr+ f g (x ∷+ y ∷+ ys)
      ≡⟨ ≡-cong (λ c → f x c) (fold+-dual₂ f g (y ∷+ ys)) ⟩
    f x (foldl+ (λ x1 x2 → f x2 x1) g (reverse+-spec ys +++ [ y ]+))
      ≡⟨ ≡-sym (foldl+-+++₁ (λ x1 x2 → f x2 x1) g (reverse+-spec ys) (y ∷+ [ x ]+)) ⟩
    foldl+ (λ x1 x2 → f x2 x1) g (reverse+-spec ys +++ reverse+-spec (x ∷+ [ y ]+)) 
      ≡⟨ ≡-cong (λ c → foldl+ (λ x1 x2 → f x2 x1) g c) (≡-sym (reverse+-+++ (x ∷+ [ y ]+) ys)) ⟩
    foldl+ (λ x1 x2 → f x2 x1) g (reverse+-spec ([ x ]+ +++ [ y ]+ +++ ys))
      ≡∎ 
        
  reverse+ : {A : Set} → (List+ A) → List+ A
  reverse+ xs = foldl+ (λ x1 x2 → x2 ∷+ x1) ([_]+) xs
 
  reverse+-derivation : {A : Set} (xs : List+ A) → reverse+ xs ≡ reverse+-spec xs 
  reverse+-derivation xs =
    foldl+ (λ x1 x2 → x2 ∷+ x1) [_]+ xs
      ≡⟨ ≡-cong (λ c → foldl+ (λ x1 x2 → x2 ∷+ x1) [_]+ c) (≡-sym (reverse+-reverse+ xs)) ⟩
    foldl+ (λ x1 x2 → x2 ∷+ x1) [_]+ (reverse+-spec (reverse+-spec xs))
      ≡⟨ (≡-sym (fold+-dual₂ _∷+_ [_]+ (reverse+-spec xs))) ⟩
    foldr+ _∷+_ [_]+ (reverse+-spec xs)
      ≡⟨ ≡-sym (id-as-foldr+ (reverse+-spec xs)) ⟩
    reverse+-spec xs
      ≡∎


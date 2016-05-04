open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List

open import prelude

module _ where

  {- Lists -}

  ∷-injective : {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
  ∷-injective refl = refl , refl
  ∷-cong : {A : Set} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
  ∷-cong refl refl = refl

  [_] : {A : Set} → A → List A
  [ x ] = x ∷ []

  infixr 5 _++_
  _++_ : {A : Set} → List A →  List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  ++-unit : {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-unit [] = refl
  ++-unit (x ∷ xs) = ∷-cong refl (++-unit xs)

  ++-assoc : {A : Set} (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = ∷-cong refl (++-assoc xs ys zs)

  foldl : {A B : Set} → (B → A → B) → B → List A → B
  foldl f e [] = e
  foldl f e (x ∷ xs) = foldl f (f e x) xs

  foldl-cong : {A B : Set} (f f' : B → A → B) (e e' : B) → 
    ((x : B) (y : A) → f x y ≡ f' x y) → e ≡ e' → 
    ((xs : List A) → foldl f e xs ≡ foldl f' e' xs)
  foldl-cong f f' e e' h1 h2 [] = h2
  foldl-cong f f' e e' h1 h2 (x ∷ xs) = 
    foldl f (f e x) xs
      ≡⟨ foldl-cong f f' (f e x) (f' e' x) h1 (
      f e x
        ≡⟨ ≡-cong (λ c → f c x) h2 ⟩
      f e' x
        ≡⟨ h1 e' x ⟩
      f' e' x
        ≡∎) xs ⟩
    foldl f' (f' e' x) xs
      ≡∎

  foldl-univ₁ : {A B : Set} (f : B → A → B) (h : B → List A → B) → 
    ((e : B) → h e [] ≡ e) →
    ((e : B) (x : A) (xs : List A) → h e (x ∷ xs) ≡ h (f e x) xs) →  
    (e : B)  (xs : List A) → h e xs ≡ foldl f e xs
  foldl-univ₁ f h h1 h2 e [] = h1 e
  foldl-univ₁ f h h1 h2 e (x ∷ xs) =
    h e (x ∷ xs) 
      ≡⟨ h2 e x xs ⟩ 
    h (f e x) xs
      ≡⟨ foldl-univ₁ f h h1 h2 (f e x) xs ⟩
    foldl f (f e x) xs 
      ≡∎

  foldl-univ₂ : {A B : Set} (f : B → A → B) (h : B → List A → B) → 
    ((e : B) (xs : List A) → h e xs ≡ foldl f e xs) → 
    ((e : B) → h e [] ≡ e) ∧ ((e : B) (x : A) (xs : List A) → h e (x ∷ xs) ≡ h (f e x) xs) 
  foldl-univ₂ f h h1 = (λ e → h1 e []) , (λ e x xs → 
    h e (x ∷ xs)
      ≡⟨ h1 e (x ∷ xs) ⟩
    foldl f e (x ∷ xs)
      ≡⟨ ≡-sym (h1 (f e x) xs) ⟩
    h (f e x) xs
      ≡∎)

  foldl-fusion : {A B C : Set} (f : B → A → B) (f' : C → A → C) (e : B) (h : B → C) → 
    ((x : B) (y : A) → h (f x y) ≡ f' (h x) y) →  
    (xs : List A) → (h ∘ foldl f  e) xs ≡ foldl f' (h e) xs
  -- Can we use foldl-univ₁?
  foldl-fusion f f' e h h1 [] = refl
  foldl-fusion f f' e h h1 (x ∷ xs) = 
    (h ∘ foldl f (f e x)) xs
      ≡⟨ foldl-fusion f f' (f e x) h h1 xs ⟩
    foldl f' (h (f e x)) xs
      ≡⟨ ≡-cong (λ c → foldl f' c xs) (h1 e x) ⟩
    foldl f' (h e) (x ∷ xs)
      ≡∎

  foldl-++₁ : {A B : Set} (f : B → A → B) (e : B) (xs ys : List A) → 
    foldl f e (xs ++ ys) ≡ foldl f (foldl f e xs) ys
  foldl-++₁ f e [] ys = refl
  foldl-++₁ f e (x ∷ xs) ys = foldl-++₁ f (f e x) xs ys

  foldl-++₂ : {A : Set} (f : A → A → A) (e : A) → 
    (left-unit : (x : A) → f e x ≡ x)
    (right-unit : (x : A) → f x e ≡ x)
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs ys : List A) → foldl f e (xs ++ ys) ≡ f (foldl f e xs) (foldl f e ys) 
  foldl-++₂ f e left-unit right-unit assoc [] ys = ≡-sym (left-unit (foldl f e ys)) 
  foldl-++₂ f e left-unit right-unit assoc (x ∷ xs) ys = 
    foldl f (f e x) (xs ++ ys)
      -- Refactor?
      ≡⟨ ≡-cong (λ c → foldl f c (xs ++ ys)) (
      f e x
        ≡⟨ left-unit x ⟩
      x
        ≡⟨ ≡-sym (right-unit x) ⟩
      f x e
        ≡∎) ⟩
    foldl f (f x e) (xs ++ ys)
      ≡⟨ ≡-sym (foldl-fusion f f e (f x) (assoc x) (xs ++ ys)) ⟩ 
    f x (foldl f e (xs ++ ys))
      ≡⟨ ≡-cong (λ c → f x c) (foldl-++₂ f e left-unit right-unit assoc xs ys) ⟩
    f x (f (foldl f e xs) (foldl f e ys))
      ≡⟨ assoc x (foldl f e xs) (foldl f e ys) ⟩
    f ((f x ∘ foldl f e) xs) (foldl f e ys)
      -- Refactor?
      ≡⟨ ≡-cong (λ c → f c (foldl f e ys)) (foldl-fusion f f e (f x) (assoc x) xs) ⟩
    f (foldl f (f x e) xs) (foldl f e ys)
      ≡⟨ ≡-cong (λ c → f (foldl f c xs) (foldl f e ys)) (
      f x e
        ≡⟨ right-unit x ⟩
      x
        ≡⟨ ≡-sym (left-unit x) ⟩
      f e x
        ≡∎) ⟩
    f (foldl f (f e x) xs) (foldl f e ys)
      ≡∎

  foldr : {A B : Set} → (A → B → B) → B → List A → B
  foldr f e [] = e
  foldr f e (x ∷ xs) = f x (foldr f e xs)

  foldr-cong : {A B : Set} (f f' : A → B → B) (e e' : B) → 
    ((x : A) (y : B) → f x y ≡ f' x y) → e ≡ e' → 
    ((xs : List A) → foldr f e xs ≡ foldr f' e' xs)
  foldr-cong f f' e e' h1 h2 [] = h2
  foldr-cong f f' e e' h1 h2 (x ∷ xs) = 
    f x (foldr f e xs)
      ≡⟨ ≡-cong (λ c → f x c) (foldr-cong f f' e e' h1 h2 xs) ⟩
    f x (foldr f' e' xs)
      ≡⟨ h1 x (foldr f' e' xs) ⟩
    f' x (foldr f' e' xs)
      ≡∎

  foldr-univ₁ : {A B : Set} (f : A → B → B) (e : B) (h : List A → B) → 
    (h [] ≡ e) →
    ((x : A) (xs : List A) → h (x ∷ xs) ≡ f x (h xs)) →  
    (xs : List A) → h xs ≡ foldr f e xs
  foldr-univ₁ f e h h1 h2 [] = h1
  foldr-univ₁ f e h h1 h2 (x ∷ xs) =
    h (x ∷ xs)
      ≡⟨ h2 x xs ⟩
    f x (h xs)
      ≡⟨ ≡-cong (f x) (foldr-univ₁ f e h h1 h2 xs) ⟩
    f x (foldr f e xs)
      ≡∎

  foldr-univ₂ : {A B : Set} (f : A → B → B) (e : B) (h : List A → B) → 
    ((xs : List A) → h xs ≡ foldr f e xs) → 
    (h [] ≡ e) ∧ ((x : A) (xs : List A) → h (x ∷ xs) ≡ f x (h xs)) 
  foldr-univ₂ f e h h1 = h1 [] ,  λ x xs → (
    h (x ∷ xs)
      ≡⟨ h1 (x ∷ xs) ⟩
    f x (foldr f e xs)
      ≡⟨ ≡-cong (λ c → f x c) (≡-sym (h1 xs)) ⟩
    f x (h xs)
      ≡∎)
  
  foldr-fusion : {A B C : Set} (f : A → B → B) (f' : A → C → C) (e : B) (h : B → C) → 
    ((x : A) (y : B) → h (f x y) ≡ f' x (h y)) →  
    (xs : List A) → (h ∘ foldr f  e) xs ≡ foldr f' (h e) xs
  foldr-fusion f f' e h h1 xs = foldr-univ₁ f' (h e) (h ∘ foldr f e) refl (λ x xs → h1 x (foldr f e xs)) xs

  foldr-++₁ : {A B : Set} (f : A → B → B) (e : B) (xs ys : List A) → 
    foldr f e (xs ++ ys) ≡ foldr f (foldr f e ys) xs
  foldr-++₁ f e [] ys = refl
  foldr-++₁ f e (x ∷ xs) ys = ≡-cong (λ c → f x c) (foldr-++₁ f e xs ys) 

  foldr-++₂ : {A : Set} (f : A → A → A) (e : A) → 
    (left-unit : (x : A) → f e x ≡ x)
    (right-unit : (x : A) → f x e ≡ x)
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs ys : List A) → foldr f e (xs ++ ys) ≡ f (foldr f e xs) (foldr f e ys) 
  foldr-++₂ f e left-unit right-unit assoc [] ys = ≡-sym (left-unit (foldr f e ys)) 
  foldr-++₂ f e left-unit right-unit assoc (x ∷ xs) ys = 
    f x (foldr f e (xs ++ ys))
      ≡⟨ ≡-cong (λ c → f x c) (foldr-++₂ f e left-unit right-unit assoc xs ys) ⟩ 
    f x (f (foldr f e xs) (foldr f e ys))
      ≡⟨ assoc x (foldr f e xs) (foldr f e ys) ⟩
    f (f x (foldr f e xs)) (foldr f e ys)
      ≡∎

  fold-dual₁ : {A : Set} (f : A → A → A) (e : A) 
    (left-unit : (x : A) → f e x ≡ x)
    (right-unit : (x : A) → f x e ≡ x)
    (assoc : (x y z : A) → f x (f y z) ≡ f (f x y) z)
    (xs : List A) → foldr f e xs ≡ foldl f e xs
  fold-dual₁ f e left-unit right-unit assoc [] = refl
  fold-dual₁ {A} f e left-unit right-unit assoc (x ∷ xs) = 
    f x (foldr f e xs)
      ≡⟨ ≡-cong (λ c → f x c) (fold-dual₁ f e left-unit right-unit assoc xs) ⟩
    f x (foldl f e xs)
      -- Refactor?
      ≡⟨ foldl-fusion f f e (f x) (assoc x) xs ⟩ 
    foldl f (f x e) xs
      ≡⟨ ≡-cong (λ c → foldl f c xs) (
      f x e
        ≡⟨ right-unit x ⟩ 
      x
        ≡⟨ ≡-sym (left-unit x) ⟩
      f e x
        ≡∎) ⟩
    foldl f (f e x) xs
      ≡∎ 

  id-as-foldr : {A : Set} (xs : List A) → id xs ≡ foldr (λ x1 x2 → x1 ∷ x2) [] xs 
  id-as-foldr xs = foldr-univ₁ (λ x1 x2 → x1 ∷ x2) [] id refl (λ x xs → refl) xs

  ++-cong : {A : Set} {xs xs' ys ys' : List A} → xs ≡ xs' → ys ≡ ys' → xs ++ ys ≡ xs' ++ ys'
  ++-cong refl refl = refl

  ++-as-foldr : {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr (λ x1 x2 → x1 ∷ x2) ys xs 
  ++-as-foldr xs ys = foldr-univ₁ (λ x1 x2 → x1 ∷ x2) ys (λ xs → xs ++ ys) refl (λ x xs → refl) xs

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  map-cong : {A B : Set} (f f' : A → B) → ((x : A) → f x ≡ f' x) → 
    ((xs : List A) → map f xs ≡ map f' xs)
  map-cong f f' h1 [] = refl
  map-cong f f' h1 (x ∷ xs) = ∷-cong (h1 x) (map-cong f f' h1 xs) 

  map-as-foldr : {A B : Set} (f : A → B) (xs : List A) → 
    map f xs ≡ foldr (λ x1 x2 → f x1 ∷ x2) [] xs 
  map-as-foldr f xs = foldr-univ₁ (λ x1 x2 → f x1 ∷ x2) [] (map f) refl (λ x xs → refl) xs

  map-id : {A : Set} (xs : List A) → map {A} id xs ≡ id xs
  map-id [] = refl
  map-id (x ∷ xs) = ∷-cong refl (map-id xs)

  map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A)  → 
    map (f ∘ g) xs ≡ (map f ∘ map g) xs
  map-compose f g [] = refl
  map-compose f g (x ∷ xs) = ∷-cong refl (map-compose f g xs)

  map-fusion : {A B C : Set} (f : A → B → B) (e : B) (h : C → A) (xs : List C)  →  
    (foldr f  e ∘ map h) xs ≡ foldr (f ∘ h) e xs
  map-fusion f e h [] = refl
  map-fusion f e h (x ∷ xs) = ≡-cong (λ c → f (h x) c) (map-fusion f e h xs) 

  map-++ : {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs ++ map f ys)
  map-++ f [] ys = refl
  map-++ f (x ∷ xs) ys = ∷-cong refl (map-++ f xs ys) 

  filter : {A : Set} (p : A → Bool) → List A → List A
  filter p [] = []
  filter p (x ∷ xs) with p x
  filter p (x ∷ xs) | false = x ∷ xs
  filter p (x ∷ xs) | true = xs

  -- first : oops!

  -- last : oops!

  inits : {A : Set} (xs : List A) → List (List A)
  inits xs = foldr (λ x1 x2 → [ [ x1 ] ] ++ map (λ x → x1 ∷ x) x2) [] xs

  -- tails : oops!

  scanr : {A B : Set} → (A → B → B) → B → List A → List B
  scanr f e [] = [ e ]
  scanr f e (x ∷ xs) with scanr f e xs
  scanr f e (x ∷ xs) | [] = [] -- oops!
  scanr f e (x ∷ xs) | y ∷ ys = f x y ∷ ys

  flatten : {A : Set} (xs : List (List A)) → List A
  flatten xs = foldr (λ x1 x2 → x1 ++ x2) [] xs

  map-flatten : {A B : Set} (f : A → B) (xs : List (List A)) → (map f ∘ flatten) xs ≡ (flatten ∘ map (map f)) xs
  map-flatten f xs = 
    (map f ∘ foldr _++_ []) xs
      ≡⟨ foldr-fusion _++_ (_++_ ∘ map f) [] (map f) (map-++ f) xs ⟩
    foldr (_++_ ∘ map f) [] xs
      ≡⟨ ≡-sym (map-fusion _++_ [] (map f) xs ) ⟩
    foldr _++_ [] (map (map f) xs)
      ≡∎ 

  reverse-spec : {A : Set} → List A → List A
  reverse-spec [] = []
  reverse-spec (x ∷ xs) = reverse-spec xs ++ [ x ]

  reverse-++ : {A : Set} (xs ys : List A) → reverse-spec (xs ++ ys) ≡ reverse-spec ys ++ reverse-spec xs
  reverse-++ [] ys = ≡-sym (++-unit (reverse-spec ys))
  reverse-++ (x ∷ xs) ys =
    reverse-spec (xs ++ ys) ++ x ∷ []
      ≡⟨ ≡-cong (λ c → c ++ [ x ]) (reverse-++ xs  ys) ⟩
    (reverse-spec ys ++ reverse-spec xs) ++ x ∷ []
      ≡⟨ ≡-sym (++-assoc (reverse-spec ys) (reverse-spec xs) (x ∷ [])) ⟩
    reverse-spec ys ++ reverse-spec xs ++ x ∷ []
      ≡∎

  reverse-reverse : {A : Set} (xs : List A) → reverse-spec (reverse-spec xs) ≡ xs
  reverse-reverse [] = refl
  reverse-reverse (x ∷ xs) = 
    reverse-spec (reverse-spec xs ++ x ∷ [])
      ≡⟨ reverse-++ (reverse-spec xs) (x ∷ []) ⟩
    x ∷ reverse-spec (reverse-spec xs)
      ≡⟨ ∷-cong refl (reverse-reverse xs) ⟩
    x ∷ xs
      ≡∎

  fold-dual₂ : {A B : Set} (f : A → B → B) (e : B) (xs : List A) → foldr f e xs ≡ foldl (λ x1 x2 → f x2 x1) e (reverse-spec xs)
  fold-dual₂ f e [] = refl
  fold-dual₂ f e (x ∷ xs) =
    f x (foldr f e xs)
      ≡⟨ ≡-cong (λ c → f x c) (fold-dual₂ f e xs) ⟩
    f x (foldl (λ x2 x1 → f x1 x2) e (reverse-spec xs))
      ≡⟨ ≡-sym (foldl-++₁ (λ x1 x2 → f x2 x1) e (reverse-spec xs) (x ∷ [])) ⟩
    foldl (λ x1 x2 → f x2 x1) e (reverse-spec xs ++ x ∷ [])
      ≡∎
  
  reverse : {A : Set} → List A → List A
  reverse xs = foldl (λ x1 x2 → x2 ∷ x1) [] xs

  reverse-derivation : {A : Set} (xs : List A) → reverse xs ≡ reverse-spec xs 
  reverse-derivation xs =
    foldl (λ x1 x2 → x2 ∷ x1) [] xs
      ≡⟨ ≡-cong (λ c → foldl (λ x1 x2 → x2 ∷ x1) [] c) (≡-sym (reverse-reverse xs)) ⟩
    foldl (λ x1 x2 → x2 ∷ x1) [] (reverse-spec (reverse-spec xs))
      ≡⟨ (≡-sym (fold-dual₂ _∷_ [] (reverse-spec xs))) ⟩
    foldr _∷_ [] (reverse-spec xs)
      ≡⟨ ≡-sym (id-as-foldr (reverse-spec xs)) ⟩
    reverse-spec xs
      ≡∎

  unfoldr : {A B : Set} (g : (n : Nat) → B → (A ∧ B) ?!) (n : Nat) (y : B) → List A
  unfoldr g zero yz = []
  unfoldr g (suc n) ysn with g n ysn
  unfoldr g (suc n) ysn | inl (x , yn) = x ∷ unfoldr g n yn
  unfoldr g (suc n) ysn | inr top = []

  fusedr : {A B : Set} (f : A → B → B) (e : B) (g : (n : Nat) → B → (A ∧ B) ?!) (n : Nat) (y : B) → B
  fusedr f e g zero yz = e
  fusedr f e g (suc n) ysn with g n ysn 
  fusedr f e g (suc n) ysn | inl (x , yn) = f x (fusedr f e g n yn)
  fusedr f e g (suc n) ysn | inr top = e

  foldr-unfoldr : {A B : Set} (f : A → B → B) (e : B) (g : (n : Nat) → B → (A ∧ B) ?!) (n : Nat) (yn : B) → foldr f e (unfoldr g n yn)  ≡ fusedr f e g n yn
  foldr-unfoldr f e g zero yz = refl
  foldr-unfoldr f e g (suc n) ysn with g n ysn
  foldr-unfoldr f e g (suc n) ysn | inl (x , yn) = ≡-cong (λ c → f x c) (foldr-unfoldr f e g n yn)
  foldr-unfoldr f e g (suc n) ysn | inr top = refl


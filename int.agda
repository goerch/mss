--open import Agda.Builtin.Equality
--open import Agda.Builtin.Nat
--open import Agda.Builtin.Int

open import prelude 
open import nat 

module _ where

  {- Integral numbers -}

  pos-injective : {n o : Nat} → pos n ≡ pos o → n ≡ o
  pos-injective refl = refl
  negsuc-injective : {n o : Nat} → negsuc n ≡ negsuc o → n ≡ o
  negsuc-injective refl = refl

  {- Order -}

  infix 4 _≤I_
  data _≤I_ : Int → Int → Set where
    pp : {n o : Nat} → n ≤N o → pos n ≤I pos o
    np : {n o : Nat} → negsuc n ≤I pos o
    nn : {n o : Nat} → n ≤N o → negsuc o ≤I negsuc n

  ≤I-refl : {x : Int} → x ≤I x
  ≤I-refl {pos n} = pp ≤N-refl
  ≤I-refl {negsuc n} = nn ≤N-refl

  ≤I-anti : {x y : Int} → x ≤I y → y ≤I x → x ≡ y
  ≤I-anti (pp h1) (pp h2) = ≡-cong pos (≤N-anti h1 h2)
  ≤I-anti np ()
  ≤I-anti (nn h1) (nn h2) = ≡-cong negsuc (≤N-anti h2 h1)

  ≤I-trans : {x y z : Int} → x ≤I y → y ≤I z → x ≤I z
  ≤I-trans (pp h1) (pp h2) = pp (≤N-trans h1 h2)
  ≤I-trans np (pp h2) = np
  ≤I-trans (nn h1) np = np
  ≤I-trans (nn h1) (nn h2) = nn (≤N-trans h2 h1)

  ≤I-total : (x y : Int) → (x ≤I y) ∨ (y ≤I x)
  ≤I-total (pos n) (pos o) with ≤N-total n o
  ≤I-total (pos n) (pos o) | inl h1 = inl (pp h1)
  ≤I-total (pos n) (pos o) | inr h1 = inr (pp h1)
  ≤I-total (pos n) (negsuc o) = inr np
  ≤I-total (negsuc n) (pos o) = inl np
  ≤I-total (negsuc n) (negsuc o) with ≤N-total n o
  ≤I-total (negsuc n) (negsuc o) | inl h1 = inr (nn h1)
  ≤I-total (negsuc n) (negsuc o) | inr h1 = inl (nn h1)

  infixr 1 _≤I⟨_⟩_ 
  _≤I⟨_⟩_ : (x : Int) {y z : Int} → (x ≤I y) → (y ≤I z) → (x ≤I z)
  _≤I⟨_⟩_ x x≤y y≤z = ≤I-trans x≤y y≤z

  infix 2 _≤I∎
  _≤I∎ : (x : Int) → x ≤I x
  _≤I∎  _ = ≤I-refl

  {- Addition -}

  infixl 6 _-N_
  _-N_ : Nat → Nat → Int
  n -N zero = pos n
  zero -N suc o = negsuc o
  suc n -N suc o = n -N o
  
  infixl 6 _+I_ 
  _+I_ : Int → Int → Int
  pos x1 +I pos x2 = pos (x1 + x2)
  pos x1 +I negsuc x2 = x1 -N (suc x2)
  negsuc x1 +I pos x2 = x2 -N (suc x1)
  negsuc x1 +I negsuc x2 = negsuc (x1 + x2)

  example-+I = pos 1 +I pos 2

  +I-unit : (x : Int) → (x +I pos 0) ≡ x
  +I-unit (pos n) = ≡-cong pos (+N-unit n)
  +I-unit (negsuc zero) = refl
  +I-unit (negsuc (suc n)) = refl

  +I-comm : (x y : Int) → x +I y ≡ y +I x
  +I-comm (pos n) (pos o) = ≡-cong pos (+N-comm n o)
  +I-comm (pos n) (negsuc o) = refl
  +I-comm (negsuc n) (pos o) = refl
  +I-comm (negsuc n) (negsuc o) = ≡-cong negsuc (+N-comm n o)

  n≤Isuc-n : {n : Nat} → (pos n) ≤I (pos (suc n))
  n≤Isuc-n {zero} = pp zn
  n≤Isuc-n {suc n} with n≤Isuc-n {n}
  n≤Isuc-n {suc n} | pp h1 = pp (ss h1)

  -1≤I0 : negsuc zero ≤I pos zero
  -1≤I0 = np

  -suc-n≤I-n : ∀ {n : Nat} → (negsuc (suc n)) ≤I (negsuc n)
  -suc-n≤I-n {zero} = nn zn
  -suc-n≤I-n {suc n} with -suc-n≤I-n {n}
  -suc-n≤I-n {suc n} | nn h1 = nn (ss h1)

  n≤In+o : {n o : Nat} → (pos n) ≤I (pos (n + o))
  n≤In+o {zero} = pp zn
  n≤In+o {suc n} {o} with n≤In+o {n} {o}
  n≤In+o {suc n} | pp h1 = pp (ss h1)

  -n-o≤I-n : {n o : Nat} → (negsuc (n + o)) ≤I (negsuc n)
  -n-o≤I-n {zero} = nn zn
  -n-o≤I-n {suc n} {o} with -n-o≤I-n {n} {o}
  -n-o≤I-n {suc n} | nn h1 = nn (ss h1) 

  -n≤Io-n : {n o : Nat} → (zero -N n) ≤I (o -N n) 
  -n≤Io-n {zero} {o} = pp zn
  -n≤Io-n {suc n} {zero} = ≤I-refl
  -n≤Io-n {suc zero} {suc o} = np
  -n≤Io-n {suc (suc n)} {suc o} = 
    negsuc (suc n)
      ≤I⟨ -suc-n≤I-n ⟩
    negsuc n
      ≤I⟨ -n≤Io-n {suc n} {o} ⟩
    (o -N suc n)
      ≤I∎

  -N-mono-right : {n o p : Nat} → o ≤N p → (o -N n) ≤I (p -N n)
  -N-mono-right {n} {.0} {p} zn =  -n≤Io-n {n} {p} 
  -N-mono-right {zero} (ss h1) = pp (ss h1) 
  -N-mono-right {suc n} (ss h1) = -N-mono-right {n} h1

  n-o≤In : {n o : Nat} → (n -N o) ≤I pos n
  n-o≤In {n} {zero} = ≤I-refl
  n-o≤In {zero} {suc o} = np
  n-o≤In {suc n} {suc o} = 
    (n -N o)
      ≤I⟨ n-o≤In {n} {o} ⟩
    pos n
      ≤I⟨ n≤Isuc-n ⟩
    pos (suc n)
      ≤I∎

  -N-mono-left : {n o p : Nat} → o ≤N p → (n -N p) ≤I (n -N o)
  -N-mono-left {n} {.0} {p} zn = n-o≤In {n} {p} 
  -N-mono-left {zero} (ss h1) = nn h1
  -N-mono-left {suc n} (ss h1) = -N-mono-left h1

  +I-mono : {x y z : Int} → y ≤I z → (x +I y) ≤I (x +I z)
  +I-mono {pos n} {pos o} {pos p} (pp h1) = pp (+N-mono {n} {o} {p} h1)
  +I-mono {pos n} {pos o} {negsuc p} ()
  +I-mono {pos n} {negsuc o} {pos p} np = 
    n -N (suc o)
      ≤I⟨ -N-mono-left {n} {zero} {suc o} zn ⟩ 
    pos n
      ≤I⟨ n≤In+o ⟩
    pos (n + p)
      ≤I∎
  +I-mono {pos n} {negsuc o} {negsuc p} (nn h1) = -N-mono-left {n} {suc p} {suc o} (ss h1) 
  +I-mono {negsuc n} {pos o} {pos p} (pp h1) = -N-mono-right {suc n} {o} {p} h1 
  +I-mono {negsuc n} {pos o} {negsuc p} ()
  +I-mono {negsuc n} {negsuc o} {pos p} np = 
    negsuc (n + o)
      ≤I⟨ -n-o≤I-n ⟩
    negsuc n
      ≤I⟨ -N-mono-right {suc n} {zero} {p}  zn ⟩
    (p -N suc n)
      ≤I∎
  +I-mono {negsuc n} {negsuc o} {negsuc p} (nn h1) = nn (+N-mono {n} {p} {o} h1)

  {- Maximum -}

  ↑I : Int → Int → Int
  ↑I (pos x) (pos y) = pos (↑N x y)
  ↑I (pos x) (negsuc y) = pos x
  ↑I (negsuc x) (pos y) = pos y
  ↑I (negsuc x) (negsuc y) = negsuc (↓N x y)

  example-↑I = ↑I (pos 1) (pos 2)

  ↑I-comm : (x y : Int) → ↑I x y ≡ ↑I y x
  ↑I-comm (pos n) (pos o) = ≡-cong pos (↑N-comm n o)
  ↑I-comm (pos n) (negsuc o) = refl
  ↑I-comm (negsuc n) (pos o) = refl
  ↑I-comm (negsuc n) (negsuc o) = ≡-cong negsuc (↓N-comm n o)

  ↑I-assoc : (x y z : Int) → ↑I x (↑I y z) ≡ ↑I (↑I x y) z
  ↑I-assoc (pos x) (pos y) (pos z) = ≡-cong pos (↑N-assoc x y z) 
  ↑I-assoc (pos x) (pos y) (negsuc z) = refl
  ↑I-assoc (pos x) (negsuc y) (pos n) = refl
  ↑I-assoc (pos x) (negsuc y) (negsuc n) = refl
  ↑I-assoc (negsuc x) (pos y) (pos z) = refl
  ↑I-assoc (negsuc x) (pos y) (negsuc z) = refl
  ↑I-assoc (negsuc x) (negsuc y) (pos z) = refl
  ↑I-assoc (negsuc x) (negsuc y) (negsuc z) = ≡-cong negsuc (↓N-assoc x y z) 

  ≤I⇒↑I : {x y : Int} → x ≤I y → ↑I x y ≡ y
  ≤I⇒↑I (pp p) = ≡-cong pos (≤N⇒↑N p)
  ≤I⇒↑I np = refl
  ≤I⇒↑I {negsuc o} {negsuc n} (nn p) = ≡-cong negsuc (≤N⇒↓N p) 

  ↑I⇒≤I : {x y : Int} → ↑I x y ≡ y → x ≤I y
  ↑I⇒≤I {pos n} {pos o} h1 = pp (↑N⇒≤N (pos-injective h1))
  ↑I⇒≤I {pos n} {negsuc o} ()
  ↑I⇒≤I {negsuc n} {pos o} refl = np
  ↑I⇒≤I {negsuc n} {negsuc o} p = nn (↓N⇒≤N (negsuc-injective p))





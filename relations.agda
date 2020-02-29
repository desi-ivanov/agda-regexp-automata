module relations where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import introduction using (*-uno)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)


≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  -- -----
  → n ≡ m
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total : ℕ → ℕ → Set where
  forward : {m n : ℕ}
    → m ≤ n
    -------
    → Total m n
  flipped : {m n : ℕ}
    → n ≤ m
    -------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

+-monor-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monor-≤ zero    p q p≤q  =  p≤q
+-monor-≤ (suc n) p q p≤q  =  s≤s (+-monor-≤ n p q p≤q)

+-monol-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monol-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monor-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  --------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monol-≤ m n p m≤n) (+-monor-≤ n p q p≤q)

*-monor-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monor-≤ zero    p q p≤q  =  z≤n
*-monor-≤ (suc n) p q p≤q
  rewrite
    *-uno (suc n) p
  | *-uno (suc n) q
    = +-mono-≤ p q (n * p) (n * q) (p≤q) (*-monor-≤ n p q p≤q)

*-monol-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monol-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monor-≤ p m n m≤n


*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monol-≤ m n p m≤n) (*-monor-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n


<-inv : ∀ {m n : ℕ}
  → suc m < suc n
  ---------------
  → m < n
<-inv (s<s m<n) = m<n

<inv : ∀ (m n : ℕ)
  → suc m < suc n
  ---------------
  → m < n
<inv m n (s<s m<n) = m<n

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -------
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

<-transp : ∀ (m n p : ℕ)
  → m < n
  → n < p
    -------
  → m < p
<-transp zero n (suc p) m<n n<p = z<s
<-transp (suc m) (suc n) (suc p) (s<s m<n) (s<s n<p) = s<s (<-transp m n p m<n n<p)

data Trichotomy (n m : ℕ ) : Set  where
  tlt : n < m → Trichotomy n m
  teq : n ≡ m → Trichotomy n m
  tgt : m < n → Trichotomy n m

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = teq refl
<-trichotomy zero (suc n) = tlt z<s
<-trichotomy (suc m) zero = tgt z<s
<-trichotomy (suc m) (suc n) = helper (<-trichotomy m n)
  where
    helper : Trichotomy m n → Trichotomy (suc m) (suc n)
    helper (tlt m<n) = tlt (s<s m<n)
    helper (teq m≡n) = teq (cong suc m≡n)
    helper (tgt n<m) = tgt (s<s n<m)












-- avoid remoing whitelines atom

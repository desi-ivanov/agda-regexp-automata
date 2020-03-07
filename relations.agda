module relations where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import introduction using (*-uno; *-distrib-+; +-identity)

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

≤-trans' : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans' zero n p m≤n n≤p = z≤n
≤-trans' (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans' m n p m≤n n≤p)


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

+-monor-< : ∀ (m n p : ℕ)
  → n < p
  -------
  → m + n < m + p
+-monor-< zero n p n<p = n<p
+-monor-< (suc m) n p n<p = s<s (+-monor-< m n p n<p)

+-monol-< : ∀ (m n p : ℕ)
  → n < p
  -------
  → n + m < p + m
+-monol-< m n p n<p rewrite +-comm n m | +-comm p m = +-monor-< m n p n<p

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monol-< p m n m<n) (+-monor-< n p q p<q)

-- ≤-iff-<
≤→< : ∀ (m n : ℕ)
  → suc m ≤ n
  -----------
  → m < n
≤→< zero (suc n) _ = z<s
≤→< (suc m) (suc n) (s≤s m≤n) = s<s (≤→< m n m≤n)

-- ≤-iff-<
≤←< : ∀ (m n : ℕ)
  → m < n
  -----------
  → suc m ≤ n
≤←< zero (suc n) z<s = s≤s z≤n
≤←< (suc m) (suc n) (s<s m<n) = s≤s (≤←< m n m<n)

<subset≤ : ∀ (m n : ℕ)
  → m < n
  --------
  → m ≤ n
<subset≤ zero n m<n = z≤n
<subset≤ (suc m) (suc n) (s<s m<n) = s≤s (<subset≤ m n m<n)

<-trans-revisited : ∀ (m n p : ℕ)
  → m < n
  → n < p
  --------
  → m < p
<-trans-revisited m (suc n) p m<n n<p = ≤→< m p (≤-trans' (suc m) (suc n) p (≤←< m (suc n) m<n) (<subset≤ (suc n) p n<p))

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)


o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)
e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)


o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  -------
  → even (m + n)
o+o≡e (suc zero) (suc x) = suc (suc x)
o+o≡e (suc (suc x)) on = suc (suc (o+o≡e x on))


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

data BinStartsOne : Bin → Set where
  isOne : BinStartsOne (⟨⟩ I)
  flwByOne : ∀ (b : Bin)
    → BinStartsOne b
      ---------------
    → BinStartsOne (b I)
  flwByZero : ∀ (b : Bin)
    → BinStartsOne b
      ---------------
    → BinStartsOne (b O)

data Can : Bin → Set where
  zeroIsCan : Can (⟨⟩ O)
  startsWithOne : ∀ (b : Bin)
    → BinStartsOne b
    -----------------
    → Can b

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (prec O) = prec I
inc (prec I) = (inc prec) O

natToBin : ℕ → Bin
natToBin zero = ⟨⟩ O
natToBin (suc n) = inc (natToBin n)

binToNat : Bin → ℕ
binToNat ⟨⟩ = 0
binToNat (b O) = 2 * binToNat b
binToNat (b I) = suc (2 * binToNat b)

oneway : ∀ (b : Bin)
  → BinStartsOne (b O)
  --------------------
  → BinStartsOne (b I)
oneway ⟨⟩ bb = isOne
oneway (b O) (flwByZero .(b O) bb) = flwByOne (b O) bb
oneway (b I) (flwByZero .(b I) bb) = flwByOne (b I) bb

incPreservesOne : ∀ (b : Bin)
  → BinStartsOne b
  ----------------
  → BinStartsOne (inc b)
incPreservesOne (b O) bo = oneway b bo
incPreservesOne (.⟨⟩ I) isOne = flwByZero (⟨⟩ I) isOne
incPreservesOne (b I) (flwByOne .b bo) = flwByZero (inc b) (incPreservesOne b bo)

incPreservesCan : ∀ (b : Bin)
  → Can b
  --------
  → Can (inc b)
incPreservesCan ⟨⟩ _ = startsWithOne (⟨⟩ I) isOne
incPreservesCan (⟨⟩ O) zeroIsCan = startsWithOne (⟨⟩ I) isOne
incPreservesCan (b O) (startsWithOne (b O) x) = startsWithOne (b I) (oneway b x)
incPreservesCan (b I) (startsWithOne (b I) x) = startsWithOne (inc (b I)) (incPreservesOne (b I) x)

natToBinYieldsCan : ∀ (n : ℕ) → Can (natToBin n)
natToBinYieldsCan zero = zeroIsCan
natToBinYieldsCan (suc n) = incPreservesCan (natToBin n) (natToBinYieldsCan n)


cantofromb : ∀ (b : Bin)
  → Can b
  -------
  → natToBin (binToNat b) ≡ b
cantofromb (⟨⟩ O) zeroIsCan = refl
cantofromb (b O) (startsWithOne .(b O) x) =
  begin
    natToBin (binToNat (b O))
  ≡⟨⟩
    natToBin (2 * binToNat b)
  ≡⟨⟩
    {!   !}
cantofromb (b I) (startsWithOne .(b I) x) =
  begin
    natToBin (suc (2 * binToNat b))
  ≡⟨⟩
    {!   !}












-- avoid remoing whitelines atom

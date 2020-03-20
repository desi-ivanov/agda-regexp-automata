module relations where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import introduction using (*-uno; *-nullo; *-distrib-+; +-identity; Bin; ⟨⟩; _O; _I; inc; natToBin; binToNat)

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

oneway : ∀ (b : Bin)
  → BinStartsOne (b O)
  --------------------
  → BinStartsOne (b I)
oneway ⟨⟩ bb = isOne
oneway (b O) (flwByZero .(b O) bb) = flwByOne (b O) bb
oneway (b I) (flwByZero .(b I) bb) = flwByOne (b I) bb

flwByZeroFlip : ∀ (b : Bin)
  → BinStartsOne (b O)
  ----
  → BinStartsOne b
flwByZeroFlip b (flwByZero .b bb) = bb

lemma2 : ∀ (b : Bin)
  → Can (b I)
  ----------
  → BinStartsOne (b I)
lemma2 b (startsWithOne .(b I) x) = x

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
--  Show that ∀ b : Bin, Can b → natToBin (binToNat b) ≡ b
lemma10 : ∀ (n : ℕ) → 0 < n → 0 < n + (n + 0)
lemma10 (suc zero) z<s = z<s
lemma10 (suc (suc n)) z<s = z<s

lemma9 : ∀ {b : Bin}
  → BinStartsOne b
    --------------
  → 0 < binToNat b
lemma9 isOne = z<s
lemma9 (flwByOne b y) = z<s
lemma9 (flwByZero b y) with lemma9 y
... | x =  lemma10 (binToNat b) x

lemma8 : ∀ (n : ℕ) → 2 * n ≡ n + n
lemma8 zero = refl
lemma8 (suc n) rewrite lemma8 n | +-identity n = refl

lemma7 : ∀ (n : ℕ)
    → 0 < n
    --------
    → natToBin (2 * n) ≡ (natToBin n) O
lemma7 (suc zero) s = refl
lemma7 (suc (suc n)) s rewrite (+-identity n) =
  begin
    inc (inc (natToBin (n + suc (suc n))))
  ≡⟨ cong (λ x → inc (inc (natToBin (x)))) (+-comm n (suc (suc n))) ⟩
    inc (inc (natToBin (suc (suc n) + n)))
  ≡⟨⟩
    inc (inc (natToBin (suc (suc n + n))))
  ≡⟨  cong (λ x → inc (inc (natToBin (suc (x))))) (+-comm (suc n) n) ⟩
    inc (inc (natToBin (suc (n + suc n))))
  ≡⟨⟩
    inc (inc (natToBin (suc n + suc n)))
  ≡⟨ cong (λ x → inc (inc (natToBin (x)))) (sym (lemma8 (suc n))) ⟩
    inc (inc (natToBin (2 * (suc n))))
  ≡⟨ cong (λ x → inc (inc x)) (lemma7 (suc n) z<s) ⟩
    (inc (inc (natToBin n)) O)
  ≡⟨⟩
    refl

lemma5 : ∀ {b : Bin}
  → BinStartsOne b
  → inc (inc (b O O)) ≡ ((b I) O)
lemma5 isOne = refl
lemma5 (flwByOne b b₁) = refl
lemma5 (flwByZero b b₁) = refl

lemma4 : ∀ {b : Bin}
  → BinStartsOne b
  → inc (inc ((b O) I)) ≡ ((b I) I)
lemma4 isOne = refl
lemma4 (flwByOne b x) = refl
lemma4 (flwByZero b x) = refl

lemma1 : ∀  (b : Bin)
  → BinStartsOne b
  ----------------
  → natToBin (2 * binToNat b) ≡ b O

lemma6 : ∀ {b : Bin}
  → BinStartsOne b
    --------------
  → natToBin (binToNat b) ≡ b

lemma1 b x rewrite lemma7 (binToNat b) (lemma9 x) | lemma6 x = refl

lemma6 isOne = refl
lemma6 (flwByOne b bs) rewrite lemma1 b bs = refl
lemma6 (flwByZero b bs) rewrite lemma1 b bs = refl

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
  ≡⟨ lemma1 b (flwByZeroFlip b x) ⟩
    b O
  ∎
cantofromb (⟨⟩ I) (startsWithOne .(⟨⟩ I) x) = refl
cantofromb (b I) (startsWithOne .(b I) (flwByOne .b x)) =
  begin
    natToBin (binToNat (b I))
  ≡⟨⟩
    natToBin (suc (2 * binToNat b))
  ≡⟨⟩
    inc (natToBin (2 * binToNat b))
  ≡⟨ cong inc (lemma1 b x) ⟩
    inc (b O)
  ≡⟨⟩
    b I
  ∎




--

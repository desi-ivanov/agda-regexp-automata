open import Data.Nat as ℕ using (ℕ; zero; suc; _≥_; _≤_; _<_; s≤s; z≤n; _+_; _*_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F) renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-inject+)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product using (_×_; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v; _++_ to _++v_) hiding (take; drop)
open import Data.Vec.Properties using (lookup-++ˡ)
open import VecUtil
open import Data.Fin.Subset using (⁅_⁆)
module PumpingLemmaExample where
Σ = ℕ
open import String Σ
open import Dfa Σ

----------------------------------------------------------------------------
-- DFA accepting binary multiples of 3.
-- The state 3F is the error state

exampleDfa : Dfa 4
exampleDfa = record { S = 0F ; δ = delta ; F = ⁅ 0F ⁆ }
  where
    delta : Fin 4 → Σ → Fin 4
    delta 0F 0 = 0F
    delta 0F 1 = 1F

    delta 1F 0 = 2F
    delta 1F 1 = 0F

    delta 2F 0 = 1F
    delta 2F 1 = 2F

    delta _ _ = 3F


str1 = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []

-- applying pumping lemma on exampleDfa using str1
res1 = proj₂ (pumpingLemma exampleDfa) str1 tt (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- the computation of pumpingLemma on exampleDfa and str1 generates the following substrings
-- x := 1 ∷ []
-- y := 0 ∷ 1 ∷ 0 ∷ []
-- z := 1 ∷ []
-- str1 ≡ x ++ y ++ z

examplePumping1 : exampleDfa ↓ (1 ∷ []  ++ (0 ∷ 1 ∷ 0 ∷ []) ^ 0 ++ 1 ∷ [])
examplePumping1 = tt

examplePumping2 : exampleDfa ↓ (1 ∷ []  ++ (0 ∷ 1 ∷ 0 ∷ []) ^ 99 ++ 1 ∷ [])
examplePumping2 = tt

examplePumping3 : ¬ exampleDfa ↓ (1 ∷ []  ++ (1 ∷ 1 ∷ 0 ∷ []) ^ 99 ++ 1 ∷ [])
examplePumping3 = λ neg → neg


--------------------------------------------------------------------------------
-- Proving non-regularity of a language

I = 1 ∷ []
O = 0 ∷ []

L : ℕ → String
L n = (I ^ n) ++ (O ^ n)

_∈L : String → Set
x ∈L = ∃[ n ] (x ≡ L n)

^-join-+ : (s : String) (n m : ℕ)
  → (s ^ n) ++ (s ^ m) ≡ s ^ (n + m)
^-join-+ s 0F     0F = refl
^-join-+ s 0F     (suc m) = refl
^-join-+ s (suc n) m rewrite
      ++-assoc s (s ^ n) (s ^ m)
    | sym (^-join-+ s n m) = refl

^-join-* : (s : String) (n m : ℕ)
  → (s ^ n) ^ m ≡ s ^ (n * m)
^-join-* s 0F 0F = refl
^-join-* s 0F (suc m) = ^-join-* s 0F m
^-join-* s (suc n) 0F = ^-join-* s n 0F
^-join-* s (suc n) (suc m) rewrite
            ^-join-* s (suc n) m
          | ++-assoc s (s ^ n) (s ^ (m + n * m))
          | ^-join-+ s n (m + n * m)
          | *-comm n (suc m)
          | *-comm m n
          | sym (+-assoc n m (n * m))
          | sym (+-assoc m n (n * m))
          | +-comm m n = refl

char-^-length-++ : (c : Σ) (n : ℕ) (t : String)
  → length ((c ∷ []) ^ n ++ t) ≡ n + length t
char-^-length-++ c 0F t = refl
char-^-length-++ c (suc n) t rewrite char-^-length-++ c n t = refl

char-^-length : (c : Σ) (n : ℕ)
  → length ((c ∷ []) ^ n) ≡ n
char-^-length c 0F = refl
char-^-length c (suc n) rewrite char-^-length c n = refl

L-length=n+n : (n : ℕ) → length (L n) ≡ n + n
L-length=n+n 0F = refl
L-length=n+n (suc n) rewrite char-^-length-++ 1 n (0 ∷ (O ^ n)) | char-^-length 0 n = refl

dfa-states>0 : ∀{n} → (dfa : Dfa n) → 1 ≤ n
dfa-states>0 {suc n} dfa = s≤s z≤n

lemmaℕ≤ : (m : ℕ) → 1 ≤ m → 1 + m ≤ m + m
lemmaℕ≤ m lq = +-monoˡ-≤ m lq

length-++ : (xs ys : String) → length xs + length ys ≡ length (xs ++ ys)
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

absurd1 : ∀{s} {ts : String} → ¬ (s ∷ ts ≡ [])
absurd1 = λ ()

listlem0 : {a b : Σ} {s t : String} → (a ∷ s) ≡ (b ∷ t) → a ≡ b
listlem0 {a} {.a} {s} {.s} refl = refl

listlem1 : {c : Σ} {s t : String} → (c ∷ s) ≡ (c ∷ t) → s ≡ t
listlem1 refl = refl

listlem2 : ∀{s t l : String} → (s ++ t) ≡ (s ++ l) → t ≡ l
listlem2 {[]}  eq = eq
listlem2 {x ∷ s} {t} {l} eq = listlem2 (listlem1 eq)

char-pow-++ : ∀{c n x y}
  → ((c ∷ []) ^ n) ≡ x ++ y
  → ∃[ l ] ∃[ m ] (x ≡ (c ∷ []) ^ l × y ≡ (c ∷ []) ^ m × n ≡ l + m)
char-pow-++ {c} {0F} {[]} {[]} eq = 0 , 0 , refl , refl , refl
char-pow-++ {c} {n} {[]} refl = 0 , n , refl , refl , refl
char-pow-++ {c} {suc n} {x ∷ xs} {y} eq with listlem0 eq
char-pow-++ {c} {suc n} {.c ∷ xs} {y}  eq | refl with char-pow-++ {c} {n}{xs}{y} (listlem1 eq)
... | l , m , eq1 , eq2 , eq3  =
  suc l , m , cong (c ∷_) eq1 , eq2 , (cong suc eq3)

power>0 : ∀{l y} → y ≡ I ^ l → y ≢ ε → 1 ≤ l
power>0 {0F} refl y = ⊥-elim(y refl)
power>0 {suc l} eq neq = s≤s z≤n

xyz-to-power-base : ∀{n m x y z}
  → (I ^ n) ++ (O ^ m) ≡ x ++ y ++ z
  → length (x ++ y) ≤ n
  → ∃[ l ] ∃[ p ] ∃[ q ] (x ≡ I ^ l
                        × y ≡ I ^ p
                        × z ≡ (I ^ q) ++ (O ^ m))
xyz-to-power-base {0F} {0F} {[]} {[]} {[]} o t = zero , zero , zero , refl , refl , refl
xyz-to-power-base {0F} {suc m} {[]} {[]} {x ∷ z} e t = zero , zero , zero , refl , refl , sym e
xyz-to-power-base {suc n} {0F} {x} {y} {z} e t rewrite ++-idʳ (I ^ n) with char-pow-++ {1} {suc n} {x} {y ++ z} e
... | l , m , eq1 , eq2 , eq3 with char-pow-++ {1} {m} {y} (sym eq2)
... | l2 , m2 , eq4 , eq5 , eq6 rewrite sym (++-idʳ (I ^ m2)) = l , l2 , m2 , eq1 , eq4 , eq5
xyz-to-power-base {suc n} {suc m} {[]} {[]} {x ∷ z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {[]} {[]} {.1 ∷ z} e les | refl with xyz-to-power-base {n} {suc m} {[]} {[]} {z} (listlem1 e) z≤n
... | l , p , q , eq1 , eq2 , eq3 = l , p , suc q , eq1 , eq2 , cong (1 ∷_) eq3
xyz-to-power-base {suc n} {suc m} {[]} {x ∷ y} {z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {[]} {.1 ∷ y} {z} e (s≤s les) | refl with xyz-to-power-base {n} {suc m} {[]} {y} {z} (listlem1 e) les
... | l , p , q , eq1 , eq2 , eq3  = l , suc p , q , eq1 , cong (1 ∷_) eq2 , eq3
xyz-to-power-base {suc n} {suc m} {c ∷ x} {y} {z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {.1 ∷ x} {y} {z} e (s≤s les) | refl with xyz-to-power-base {n} {suc m} {x} {y} {z} (listlem1 e) les
... | l , p , q , eq1 , eq2 , eq3 = suc l , p , q , cong (1 ∷_) eq1 , eq2 , eq3

xyz-to-power : ∀{n x y z}
  → (I ^ n) ++ (O ^ n) ≡ x ++ y ++ z
  → length (x ++ y) ≤ n
  → y ≢ ε
  → ∃[ l ] ∃[ p ] ∃[ q ] (x ≡ I ^ l
                        × y ≡ I ^ p
                        × 0 < p
                        × z ≡ (I ^ q) ++ (O ^ n))
xyz-to-power {n} {x} {y} {z} e les neq with xyz-to-power-base {n} {n} {x} {y} {z} e les
... | l , p , q , eq1 , eq2 , eq3 = l , p , q , eq1 , eq2 , power>0 eq2 neq , eq3

powSame : ∀{s n m a} → (a ∷ s) ^ n ≡ (a ∷ s) ^ m → n ≡ m
powSame {s} {0F} {0F} e = refl
powSame {s} {0F} {suc n} ()
powSame {s} {suc n} {0F} ()
powSame {s} {suc n} {suc m} {a} eq with listlem2 {a ∷ s} {(a ∷ s) ^ n} {(a ∷ s) ^ m} eq
... | u = cong suc (powSame u)

exponents-equal-base : (m p n q : ℕ)
  → I ^ m ++ O ^ n ≡ I ^ p ++ O ^ q
  → m ≡ p × n ≡ q
exponents-equal-base 0F 0F      _ _ eq = refl , powSame eq
exponents-equal-base 0F (suc p) n q eq  with char-pow-++ {0} {n} {I ^ (suc p)} {O ^ q} eq
... | zero , _ , () , _ , _
... | suc a , _ , e , _ , _ = contradiction (listlem0 e) λ ()
exponents-equal-base (suc m) 0F n q eq with char-pow-++ {0} {q} {I ^ (suc m)} {O ^ n} (sym eq)
... | zero , _ , () , _ , _
... | suc a , _ , e , _ , _ = contradiction (listlem0 e) λ ()
exponents-equal-base (suc m) (suc p) n q eq with exponents-equal-base m p n q (listlem1 eq)
... | fst , snd = cong suc fst , snd

exponents-equal : ∀{n m} → (I ^ n ++ O ^ m) ∈L → n ≡ m
exponents-equal {n} {m} (p , snd) with exponents-equal-base n p m p snd
... | m≡p , n≡p rewrite m≡p | n≡p = refl

p≮p : ∀{p} → ¬ (p < p)
p≮p (s≤s pp) = p≮p pp

<-implies-≢ : ∀{p n} → p < n → n ≢ p
<-implies-≢ pn refl = p≮p pn

+-monoR-≤ : ∀{m n} (p : ℕ) → m ≤ n → m ≤ p + n
+-monoR-≤ {m} {n} p mn with +-mono-≤ {_}{_}{_}{p} mn z≤n
... | u rewrite +-identityʳ m | +-comm p n = u

nLess0 : (p n : ℕ) → 1 ≤ p → n < p * suc n
nLess0 (suc p) zero    lt = s≤s z≤n
nLess0 (suc p) (suc n) lt with nLess0 (suc p) n lt
... | z with +-monoʳ-≤ 1 z
... | u rewrite *-comm p (suc (suc n))
  | *-comm p (suc n)
  | sym (+-assoc n p (p + n * p))
  | +-comm n p
  | +-assoc p n (p + n * p)
  | sym (+-suc p (n + (p + n * p)))
  | sym (+-suc p (suc (n + (p + n * p)))) = +-monoR-≤ p u

nLess1 : (l p n q : ℕ) → 1 ≤ p → n < l + p * suc n + q
nLess1 l p n q x rewrite
    +-assoc l (p * suc n) q
  | +-comm (p * suc n) q
  | sym (+-assoc l q (p * suc n)) = +-monoR-≤ (l + q) (nLess0 p n x)

absurd-sum : (l p n q : ℕ)
  → 1 ≤ p
  → l + p * (1 + n) + q ≢ n
absurd-sum l p n q lt = <-implies-≢ (nLess1 l p n q lt)

L-not-regular : ¬ ∃₂ λ (n : ℕ) (dfa : Dfa n)
                  → ∀ (s : String)
                  → s ∈L ⇔ dfa ↓ s
L-not-regular (n , dfa , s∈L⇔dfa↓s) with proj₂
  (pumpingLemma dfa)
  (L n)
  (_⇔_.to (s∈L⇔dfa↓s (L n)) (n , refl))
  (subst (suc n ≤_)
          (sym (L-length=n+n n))
          (lemmaℕ≤ n (dfa-states>0 dfa))
  )
... | x , y , z , eq , neq , lm , pump with xyz-to-power eq lm neq
... | l , p , q , x≡I^l , y≡I^p , 0<p , z≡I^q++I^n rewrite
  y≡I^p | x≡I^l | z≡I^q++I^n with
  _⇔_.from
    (s∈L⇔dfa↓s (I ^ l ++ I ^ p ^ (1 + n) ++ I ^ q ++ O ^ n))
    (pump (1 + n))
... | fst , snd rewrite
      ^-join-* I p (1 + n)
    | sym (++-assoc (I ^ l) (I ^ (p * (1 + n))) (I ^ q ++ O ^ n))
    | ^-join-+ I l (p * (1 + n))
    | sym (++-assoc (I ^ (l + (p * (1 + n)))) (I ^ q) (O ^ n))
    | ^-join-+ I (l + p * (1 + n)) q
  = absurd-sum l p n q 0<p (exponents-equal (fst , snd))















--

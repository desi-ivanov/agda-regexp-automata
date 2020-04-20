module Dfa where
open import Data.Char using (Char)
open import Data.Nat as ℕ using (ℕ; zero; suc; _≥_; _≤_; _<_; s≤s; z≤n; _+_; _*_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F) renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-inject+)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List using (List; _∷_; []; _++_; length; take; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-cancelʳ)
open import Data.Product using (_×_; Σ; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v; _++_ to _++v_) hiding (take; drop)
open import Data.Vec.Properties using (lookup-++ˡ)
open import VecUtil

String : Set
String = List Char

record Dfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Fin n
    isF : Fin n → Bool

δ̂ : ∀{n} → (Fin n → Char → Fin n) → (q : Fin n) → String → Fin n
δ̂ δ q [] = q
δ̂ δ q (x ∷ s) = δ̂ δ (δ q x) s

infix 10 _↓_
_↓_ : ∀{n} → Dfa n → String → Set
dfa ↓ s  = T (Dfa.isF dfa (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s))

_↓?_ : ∀{n} → (dfa : Dfa n) → (s : String) → Dec (dfa ↓ s)
dfa ↓? s with Dfa.isF dfa (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s)
... | false = no (λ z → z)
... | true = yes tt

complement : ∀{n} → Dfa n → Dfa n
complement dfa =
  record
    { S = Dfa.S dfa
    ; δ = Dfa.δ dfa
    ; isF = λ x → not (Dfa.isF dfa x)
    }

not-elim : ∀{b} → T b → T (not b) → ⊥
not-elim {false} x y = x
not-elim {true} x y = y

¬not-elim : ∀{b} → ¬ T b → ¬ T (not b) → ⊥
¬not-elim {false} x y = y tt
¬not-elim {true} x y = y (x tt)

complement-closure : ∀{s n} {dfa : Dfa n}
  → dfa ↓ s ⇔ ¬ (complement dfa ↓ s)
complement-closure {s}{n}{dfa} = record { to = to {s}{n}{dfa} ; from = from {s}{n}{dfa} }
  where
    to : ∀{s n} {dfa : Dfa n} → dfa ↓ s → ¬ (complement dfa ↓ s)
    to {s} {n} {dfa} p with dfa ↓? s
    ... | yes q = λ x → not-elim p x
    ... | no ¬p = λ _ → ¬p p
    from : ∀{s n} {dfa : Dfa n} → ¬ (complement dfa ↓ s) → dfa ↓ s
    from {s} {n} {dfa} np with (complement dfa) ↓? s | dfa ↓? s
    ... | yes p | yes q = q
    ... | yes p | no ¬q = ⊥-elim (np p)
    ... | no ¬p | yes q = q
    ... | no ¬p | no ¬q = ⊥-elim (¬not-elim ¬q np)

infixl 6 _^_
_^_ : String → ℕ → String
s ^ zero = []
s ^ (suc n) = s ++ s ^ n

lemma-δ̂ : ∀{n}
  (dfa : Dfa n)
  → (s : String)
  → (t : String)
  → (q : Fin n)
  → δ̂ (Dfa.δ dfa) q (s ++ t) ≡ δ̂ (Dfa.δ dfa) (δ̂ (Dfa.δ dfa) q s) t
lemma-δ̂ dfa [] t q = refl
lemma-δ̂ dfa (c ∷ s) t q = lemma-δ̂ dfa s t (Dfa.δ dfa q c)

smallPumping : ∀{n}
  → (dfa : Dfa n)
  → (s : String)
  → (q : Fin n)
  → q ≡ δ̂ (Dfa.δ dfa) q s
  → ∀(m : ℕ) → q ≡ δ̂ (Dfa.δ dfa) q (s ^ m)
smallPumping dfa s q eq zero = refl
smallPumping dfa s q eq (suc m) with smallPumping dfa s q eq m | lemma-δ̂ dfa s (s ^ m) q
... | ind | lm2 with subst (λ x → δ̂ (Dfa.δ dfa) q (s ++ (s ^ m)) ≡ δ̂ (Dfa.δ dfa) x (s ^ m)) (sym eq) lm2
... | conc = trans ind (sym conc)

bigPumping : ∀{n} {dfa : Dfa n}
  → (s : String)
  → (t : String)
  → (u : String)
  → let p = δ̂ (Dfa.δ dfa) (Dfa.S dfa) s in
     p ≡ δ̂ (Dfa.δ dfa) p t
  → dfa ↓ (s ++ t ++ u)
  → (m : ℕ)
  → dfa ↓ (s ++ t ^ m ++ u)
bigPumping {n} {dfa} s t u eq2 dec m with smallPumping dfa t (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s) eq2 m
... | nlbl with lemma-δ̂ dfa (s ++ t) u (Dfa.S dfa)
... | lm with lemma-δ̂ dfa s (t ^ m) (Dfa.S dfa)
... | lm2 with lemma-δ̂ dfa s t (Dfa.S dfa)
... | lm3 with trans nlbl (sym lm2)
... | ok with trans eq2 (sym lm3)
... | calm with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ t) ++ u) ≡ δ̂ (Dfa.δ dfa) x u) (sym calm) lm
... | almost with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ t) ++ u) ≡ δ̂ (Dfa.δ dfa) x u) ok almost
... | gotit with lemma-δ̂ dfa (s ++ (t ^ m)) u (Dfa.S dfa)
... | doable with trans gotit (sym doable)
... | notrly with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) x ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ (t ^ m)) ++ u)) (++-assoc s t u) notrly
... | gg with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) (s ++ t ++ u) ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) x) (++-assoc s (t ^ m) u) gg
... | easy = subst (λ x → T (Dfa.isF dfa x)) easy dec

path : ∀{m} → Dfa m → Fin m → (s : String) → Vec (Fin m) (length s)
path dfa q [] = []v
path dfa q (c ∷ s) = q ∷v (path dfa (Dfa.δ dfa q c) s)

take++drop : (n : ℕ) → (s : String) → s ≡ take n s ++ drop n s
take++drop zero s = refl
take++drop (suc n) [] = refl
take++drop (suc n) (c ∷ s) = cong (c ∷_) (take++drop n s)

lemminoTakeDrop1 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → s ≡ take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ++ drop (toℕ j) s
lemminoTakeDrop1 {c ∷ s} {fzero} {fsuc j} (s≤s z≤n) = cong (c ∷_) (take++drop (toℕ j) s)
lemminoTakeDrop1 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop1 {s} i<j)

lemminoTakeDrop2 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → drop (toℕ i) (take (toℕ j) s) ≢ []
lemminoTakeDrop2 {c ∷ s} {fzero} {fsuc j} i<j = λ ()
lemminoTakeDrop2 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) eq = ⊥-elim (lemminoTakeDrop2 {s} i<j eq)

lemminoTakeDrop3 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ≡ take (toℕ j) s
lemminoTakeDrop3 {c ∷ s} {fzero} {fsuc j} i<j = refl
lemminoTakeDrop3 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop3 {s} i<j)

lemminoTakeDrop5 : (s : String) → (i : Fin (length s)) → length (take (toℕ i) s) ≡ toℕ i
lemminoTakeDrop5 (x ∷ s) Data.Fin.0F = refl
lemminoTakeDrop5 (x ∷ s) (fsuc i) = cong suc (lemminoTakeDrop5 s i)

lemminoTakeDrop4 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → length (take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s)) ≡ toℕ j
lemminoTakeDrop4 {x ∷ s} {fzero} {fsuc j} i<j rewrite sym (lemminoTakeDrop3 {x ∷ s} i<j) = cong suc (lemminoTakeDrop5 s j)
lemminoTakeDrop4 {x ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong suc (lemminoTakeDrop4 {s} i<j)

tripartition : (s : String)
  → (i j : Fin (length s))
  → i <ᶠ j
  → (∃₂ λ (x : String) (y : String) → ∃ λ (z : String) →
      s ≡ x ++ y ++ z
      × y ≢ []
      × x ≡ take (toℕ i) s
      × (x ++ y) ≡ take (toℕ j) s
      × length (x ++ y) ≡ toℕ j
    )
tripartition s i j i<j = take (toℕ i) s , drop (toℕ i) (take (toℕ j) s) , drop (toℕ j) s
  , lemminoTakeDrop1 i<j
  , lemminoTakeDrop2 i<j
  , refl
  , lemminoTakeDrop3 i<j
  , lemminoTakeDrop4 i<j

lemmino≢ : ∀{p}{m n : Fin p} → fsuc m ≢ fsuc n → m ≢ n
lemmino≢ {_} {fzero} {fzero} neq =  λ _ → neq refl
lemmino≢ {_} {fsuc m} {fsuc n} neq eq = ⊥-elim (neq (cong fsuc eq))

<-total : ∀{p}{m n : Fin p} → m ≢ n → (m <ᶠ n) ⊎ (n <ᶠ m)
<-total {_} {fzero} {fzero} neq = ⊥-elim (neq refl)
<-total {_} {fzero} {fsuc n} neq = inj₁ (s≤s z≤n)
<-total {_} {fsuc m} {fzero} neq = inj₂ (s≤s z≤n)
<-total {_} {fsuc m} {fsuc n} neq with <-total (lemmino≢ neq)
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ y = inj₂ (s≤s y)

n<1+n : (n : ℕ) → n < suc n
n<1+n zero = s≤s z≤n
n<1+n (suc n) = s≤s (n<1+n n)

lemmamtoℕ : ∀{n} → (j : Fin (suc n)) → toℕ j ≤ n
lemmamtoℕ {n} fzero = z≤n
lemmamtoℕ {suc n} (fsuc j) = s≤s (lemmamtoℕ j)

lemman<m : ∀{n m} → n < m → ∃[ p ] ((suc n) + p ≡ m)
lemman<m {zero} {suc m} n<m = m , refl
lemman<m {suc n} {suc m} (s≤s n<m) with lemman<m {n} {m} n<m
...| p , snd = p , cong suc snd

piccionaiaLimit : ∀{n}
  → (vec : Vec (Fin n) (suc n))
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × (vec ! i ≡ vec ! j))
piccionaiaLimit {n} vec with pigeonhole (n<1+n n) (λ i → vec ! i)
... | i , j , neq , eq with <-total neq
... | inj₁ x = i , j , x , lemmamtoℕ j , eq
... | inj₂ y = j , i , y , lemmamtoℕ i , (sym eq)

piccionaia : ∀{n m}
  → (vec : Vec (Fin n) m)
  → n < m
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × (vec ! i ≡ vec ! j))
piccionaia {n} {m} vec n<m with lemman<m n<m
... | p , eq rewrite sym eq with splitAt (suc n) vec
... | l , r , e with piccionaiaLimit l
... | i , j , i<j , j≤n , eq2 with trans (subst (_≡ l ! j) (sym (lookup-++ˡ l r i)) eq2) (sym (lookup-++ˡ l r j))
... | injEq rewrite sym e with toℕ-inject+ p i | toℕ-inject+ p j
... | toinjI | toinjJ with subst (_≤ n) toinjJ j≤n
... | j≤m with subst (suc (toℕ (inject+ p i)) ≤_) toinjJ (subst (λ x → suc x ≤ toℕ j) toinjI i<j)
... | inji<j = inject+ p i , inject+ p j , inji<j , j≤m , injEq

lemmaPath : ∀{m}
  → (dfa : Dfa m)
  → (s : String)
  → (i : Fin (length s))
  → (q : Fin m)
  → (path dfa q s ! i) ≡ δ̂ (Dfa.δ dfa) q (take (toℕ i) s)
lemmaPath dfa (c ∷ s) fzero q = refl
lemmaPath dfa (c ∷ s) (fsuc i) q = lemmaPath dfa s i (Dfa.δ dfa q c)

pumingLemmaBase : ∀{n : ℕ}
  → (dfa : Dfa n)
  → ∀(w : String)
  → dfa ↓ w
  → n < length w
  → ∃[ x ] ∃[ y ] ∃[ z ] (
      w ≡ x ++ y ++ z
      × ¬(y ≡ [])
      × length (x ++ y) ≤ n
      × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
    )
pumingLemmaBase {n} dfa w dec gt with piccionaia (path dfa (Dfa.S dfa) w) gt
... | i , j , i<j , lt , eq  with tripartition w i j i<j
... | x , y , z , eq2 , y≢[] , bydef1 , bydef2 , lenp with lemmaPath dfa w i (Dfa.S dfa) | lemmaPath dfa w j (Dfa.S dfa)
... | lp1 | lp2 with subst (λ v → (path dfa (Dfa.S dfa) w) ! i ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) v) (sym bydef1) lp1
... | u1 with subst (λ v → (path dfa (Dfa.S dfa) w) ! j ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) v) (sym bydef2) lp2
... | u2 with trans u2 (lemma-δ̂ dfa x y (Dfa.S dfa))
... | u3 with subst (_≡ δ̂ (Dfa.δ dfa) (δ̂ (Dfa.δ dfa) (Dfa.S dfa) x) y) (sym eq) u3
... | u4 = x , y , z , ( eq2 , y≢[] , subst (_≤ n) (sym lenp) lt , bigPumping {n}{dfa} x y z (trans (sym u1) u4) (subst (dfa ↓_) eq2 dec) )

pumpingLemma : {m : ℕ}
  → (dfa : Dfa m)
  → ∃[ n ] (
    ∀(w : String)
    → dfa ↓ w
    → n < length w
    → ∃[ x ] ∃[ y ] ∃[ z ] (
        w ≡ x ++ y ++ z
        × ¬(y ≡ [])
        × length (x ++ y) ≤ n
        × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
      )
  )
pumpingLemma {m} dfa = m , pumingLemmaBase dfa

----------------------------------------------------------------------------

-- DFA accepting binary multiples of 3.
-- The state 3F is the error state

exampleDfa : Dfa 4
exampleDfa = record { S = 0F ; δ = δ ; isF = isF }
  where
    δ : Fin 4 → Char → Fin 4
    δ 0F '0' = 0F
    δ 0F '1' = 1F

    δ 1F '0' = 2F
    δ 1F '1' = 0F

    δ 2F '0' = 1F
    δ 2F '1' = 2F

    δ _ _ = 3F

    isF : Fin 4 → Bool
    isF 0F = true
    isF _ = false

str1 = '1' ∷ '0' ∷ '1' ∷ '0' ∷ '1' ∷ []

-- applying pumping lemma on exampleDfa using str1
res1 = proj₂ (pumpingLemma exampleDfa) str1 tt (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- the computation of pumpingLemma on exampleDfa and str1 generates the following substrings
-- x := '1' ∷ []
-- y := '0' ∷ '1' ∷ '0' ∷ []
-- z := '1' ∷ []
-- str1 ≡ x ++ y ++ z

examplePumping1 : exampleDfa ↓ ('1' ∷ []  ++ ('0' ∷ '1' ∷ '0' ∷ []) ^ 0 ++ '1' ∷ [])
examplePumping1 = tt

examplePumping2 : exampleDfa ↓ ('1' ∷ []  ++ ('0' ∷ '1' ∷ '0' ∷ []) ^ 99 ++ '1' ∷ [])
examplePumping2 = tt

examplePumping3 : ¬ exampleDfa ↓ ('1' ∷ []  ++ ('1' ∷ '1' ∷ '0' ∷ []) ^ 99 ++ '1' ∷ [])
examplePumping3 = λ neg → neg


--------------------------------------------------------------------------------
-- Proving non-regularity of a language

I = '1' ∷ []
O = '0' ∷ []

generator : ℕ → String
generator n = (I ^ n) ++ (O ^ n)

L : String → Set
L x = ∃[ n ] (x ≡ generator n)

^-join-+ : (s : String) → (n m : ℕ) → (s ^ n) ++ (s ^ m) ≡ s ^ (n + m)
^-join-+ s 0F     0F = refl
^-join-+ s 0F     (suc m) = refl
^-join-+ s (suc n) m rewrite
      ++-assoc s (s ^ n) (s ^ m)
    | sym (^-join-+ s n m) = refl

^-join-* : (s : String) → (n m : ℕ) → (s ^ n) ^ m ≡ s ^ (n * m)
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

char-^-length-++ : (c : Char) → (n : ℕ) → (t : String) → length ((c ∷ []) ^ n ++ t) ≡ n + length t
char-^-length-++ c 0F t = refl
char-^-length-++ c (suc n) t rewrite char-^-length-++ c n t = refl

char-^-length : (c : Char) → (n : ℕ) → length ((c ∷ []) ^ n) ≡ n
char-^-length c 0F = refl
char-^-length c (suc n) rewrite char-^-length c n = refl

generator-length=n+n : (n : ℕ) → length (generator n) ≡ n + n
generator-length=n+n 0F = refl
generator-length=n+n (suc n) rewrite char-^-length-++ '1' n ('0' ∷ (O ^ n)) | char-^-length '0' n = refl

dfa-states>0 : ∀{n} → (dfa : Dfa n) → 1 ≤ n
dfa-states>0 {suc n} dfa = s≤s z≤n

lemmaℕ≤ : (m : ℕ) → 1 ≤ m → 1 + m ≤ m + m
lemmaℕ≤ m lq = +-monoˡ-≤ m lq

length-++ : ∀ {A : Set} (xs ys : List A) → length xs + length ys ≡ length (xs ++ ys)
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

absurd1 : ∀{s} {ts : String} → ¬ (s ∷ ts ≡ [])
absurd1 = λ ()

listlem0 : {a b : Char} {s t : String} → (a ∷ s) ≡ (b ∷ t) → a ≡ b
listlem0 {a} {.a} {s} {.s} refl = refl

listlem1 : {c : Char} {s t : String} → (c ∷ s) ≡ (c ∷ t) → s ≡ t
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

power>0 : ∀{l y} → y ≡ I ^ l → y ≢ [] → 1 ≤ l
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
xyz-to-power-base {suc n} {0F} {x} {y} {z} e t rewrite ++-identityʳ (I ^ n) with char-pow-++ {'1'} {suc n} {x} {y ++ z} e
... | l , m , eq1 , eq2 , eq3 with char-pow-++ {'1'} {m} {y} (sym eq2)
... | l2 , m2 , eq4 , eq5 , eq6 rewrite sym (++-identityʳ (I ^ m2)) = l , l2 , m2 , eq1 , eq4 , eq5
xyz-to-power-base {suc n} {suc m} {[]} {[]} {x ∷ z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {[]} {[]} {.'1' ∷ z} e les | refl with xyz-to-power-base {n} {suc m} {[]} {[]} {z} (listlem1 e) z≤n
... | l , p , q , eq1 , eq2 , eq3 = l , p , suc q , eq1 , eq2 , cong ('1' ∷_) eq3
xyz-to-power-base {suc n} {suc m} {[]} {x ∷ y} {z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {[]} {.'1' ∷ y} {z} e (s≤s les) | refl with xyz-to-power-base {n} {suc m} {[]} {y} {z} (listlem1 e) les
... | l , p , q , eq1 , eq2 , eq3  = l , suc p , q , eq1 , cong ('1' ∷_) eq2 , eq3
xyz-to-power-base {suc n} {suc m} {c ∷ x} {y} {z} e t with listlem0 e
xyz-to-power-base {suc n} {suc m} {.'1' ∷ x} {y} {z} e (s≤s les) | refl with xyz-to-power-base {n} {suc m} {x} {y} {z} (listlem1 e) les
... | l , p , q , eq1 , eq2 , eq3 = suc l , p , q , cong ('1' ∷_) eq1 , eq2 , eq3

xyz-to-power : ∀{n x y z}
  → (I ^ n) ++ (O ^ n) ≡ x ++ y ++ z
  → length (x ++ y) ≤ n
  → y ≢ []
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

exponents-equal : (m p n q : ℕ) → I ^ m ++ O ^ n
                           ≡ I ^ p ++ O ^ q
                           → m ≡ p × n ≡ q
exponents-equal 0F 0F      _ _ eq = refl , powSame eq
exponents-equal 0F (suc p) n q eq  with char-pow-++ {'0'} {n} {I ^ (suc p)} {O ^ q} eq
... | zero , _ , () , _ , _
... | suc a , _ , e , _ , _ = contradiction (listlem0 e) λ ()
exponents-equal (suc m) 0F n q eq with char-pow-++ {'0'} {q} {I ^ (suc m)} {O ^ n} (sym eq)
... | zero , _ , () , _ , _
... | suc a , _ , e , _ , _ = contradiction (listlem0 e) λ ()
exponents-equal (suc m) (suc p) n q eq with exponents-equal m p n q (listlem1 eq)
... | fst , snd = cong suc fst , snd

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
  → l + p * suc n + q ≡ n
  → ⊥
absurd-sum l p n q lt = <-implies-≢ (nLess1 l p n q lt)

L-not-regular : ¬ ∃₂ λ (n : ℕ) (dfa : Dfa n)
                  → ∀ (s : String)
                  → L s ⇔ dfa ↓ s
L-not-regular (n , dfa , iff) with proj₂
  (pumpingLemma dfa)
  (generator n)
  (_⇔_.to (iff (generator n)) (n , refl))
  (subst (suc n ≤_) (sym (generator-length=n+n n)) (lemmaℕ≤ n (dfa-states>0 dfa)))
... | x , y , z , eq , neq , lm , pump with xyz-to-power {n}{x}{y}{z} eq lm neq
... | l , p , q , x≡I^l , y≡I^p , 0<p , z≡I^q++I^n rewrite y≡I^p | x≡I^l | z≡I^q++I^n with
  _⇔_.from (iff (I ^ l ++ I ^ p ^ (1 + n) ++ I ^ q ++ O ^ n)) (pump (1 + n))
... | fst , snd rewrite
  ^-join-* I p (1 + n)
  | sym (++-assoc (I ^ l) (I ^ (p * (1 + n))) (I ^ q ++ O ^ n))
  | ^-join-+ I l (p * (1 + n))
  | sym (++-assoc (I ^ (l + (p * (1 + n)))) (I ^ q) (O ^ n))
  | ^-join-+ I (l + p * (1 + n)) q with exponents-equal (l + p * suc n + q) fst n fst snd
... | a , b = absurd-sum l p n q 0<p (trans a (sym b))

















--

module DfaNfa where
open import Dfa renaming (δ̂ to δ̂ᵈ; _↓_ to _↓ᵈ_; _↓?_ to _↓ᵈ?_)
open import Nfa renaming (δ̂ to δ̂ⁿ; _↓_ to _↓ⁿ_; _↓?_ to _↓ⁿ?_)
open import Data.Bool using (Bool; false; true; not; T; _∨_; _∧_)
open import Data.Char using (Char)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _<_; _+_; _≤_; s≤s; z≤n; pred)
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; toℕ; fromℕ≤; fromℕ; inject≤)
  renaming (suc to fsuc; zero to fzero)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Fin.Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Vec
  using (zipWith; _[_]=_; here; there; toList; replicate; sum; _[_]%=_; reverse)
  renaming (_∷_ to _∷v_; [] to []v)
open import String
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

-- Dfa ⊆ Nfa

DfaToNfa : ∀{n} → Dfa n → Nfa n
DfaToNfa dfa =
  record
    { S = Dfa.S dfa
    ; δ = λ q c → ⁅ Dfa.δ dfa q c ⁆
    ; F = build (Dfa.isF dfa)
    }

lemma-build-! : ∀{n}{A : Set}
  → (i : Fin n)
  → (f : Fin n → A)
    -----------------
  → build f ! i ≡ f i
lemma-build-! Data.Fin.0F f = refl
lemma-build-! (fsuc i) f = lemma-build-! i (λ z → f (fsuc z))

replicate-false : ∀{n}
  → (f : Fin n → Bool)
    ---------------------------------------------
  → any (λ x → replicate false ! x ∧ f x) ≡ false
replicate-false {zero} f = refl
replicate-false {suc n} f = replicate-false (λ z → f (fsuc z))

any-singleton : ∀{n}
  → (f : Fin n → Bool)
  → (q : Fin n)
    ---------------------------------
  → any (λ p → ⁅ q ⁆ ! p ∧ f p) ≡ f q
any-singleton {n} f fzero with f fzero
... | false = replicate-false f
... | true = refl
any-singleton f (fsuc q) = any-singleton (λ z → f (fsuc z)) q

isF≡accepts : ∀{n}
  → (dfa : Dfa n)
  → (s : String)
  → (q : Fin n)
    -------------------------------------------------------------
  → Dfa.isF dfa (δ̂ᵈ (Dfa.δ dfa) q s) ≡ accepts (DfaToNfa dfa) q s
isF≡accepts {n} dfa [] q = sym (lemma-build-! q (Dfa.isF dfa))
isF≡accepts {n} dfa (c ∷ s) q with Dfa.δ dfa q c
... | p = trans (isF≡accepts dfa s p) (sym (any-singleton (λ r → accepts (DfaToNfa dfa) r s) p))

dfa⊆nfa : ∀{s n} {dfa : Dfa n}
  → dfa ↓ᵈ s ⇔ (DfaToNfa dfa) ↓ⁿ s
dfa⊆nfa {s}{n}{dfa} = record { to = to {s}{n}{dfa} ; from = from {s}{n}{dfa} }
  where
    to : ∀{s n} {dfa : Dfa n} → dfa ↓ᵈ s → DfaToNfa dfa ↓ⁿ s
    to {s} {n} {dfa} x = subst (λ y → T y) (isF≡accepts dfa s (Dfa.S dfa)) x

    from : ∀{s n} {dfa : Dfa n} → DfaToNfa dfa ↓ⁿ s → dfa ↓ᵈ s
    from {s} {n} {dfa} x = subst (λ y → T y) (sym (isF≡accepts dfa s (Dfa.S dfa))) x

-- Nfa ⊆ Dfa

subsetToNat : ∀{n} → Subset n → ℕ
subsetToNat ss = sum (mapS ss (λ i →  2 ^ toℕ i) 0)

postulate
  subsetToNat< : ∀{n} → (ss : Subset n) → subsetToNat ss < 2 ^ n

1≤2^n : (n : ℕ) → 1 ≤ 2 ^ n
1≤2^n zero = s≤s z≤n
1≤2^n (suc n) rewrite +-identityʳ (2 ^ n) = ≤-stepsʳ (2 ^ n) (1≤2^n n)

n≤2^n : (n : ℕ) → n ≤ (2 ^ n)
n≤2^n Data.Fin.0F = z≤n
n≤2^n (suc n) rewrite +-identityʳ (2 ^ n) = subst (_≤(2 ^ n) + (2 ^ n)) (+-comm n 1) (+-mono-≤ (n≤2^n n) (1≤2^n n))

1+n<m⟶n<m : ∀{n m} → suc n < m → n < m
1+n<m⟶n<m {zero} (s≤s x) = s≤s z≤n
1+n<m⟶n<m {suc n} (s≤s x) = s≤s (1+n<m⟶n<m x)

n<1+n : (n : ℕ) → n < suc n
n<1+n Data.Fin.0F = s≤s z≤n
n<1+n (suc n) = s≤s (n<1+n n)

toSubset : ∀{n} → Fin (2 ^ n) → Subset n
toSubset {n} m = incMTimes (toℕ m) (toℕ<n m) ∅
  where
    inc : ∀{m} → Subset m → (liv : ℕ) → liv < m → Subset m
    inc ss zero lt = ss [ fromℕ≤ lt ]%= λ{ false → true ; true → true}
    inc ss (suc liv) lt with fromℕ≤ lt
    ... | rl with ss ! rl
    inc ss (suc liv) lt | rl | false = ss [ rl ]%= λ _ → true
    inc ss (suc liv) lt | rl | true = inc (ss [ rl ]%= λ _ → false) liv (1+n<m⟶n<m lt)

    incMTimes : ∀{m} → (n : ℕ) → n < 2 ^ m → Subset m → Subset m
    incMTimes zero lt ss = ss
    incMTimes {zero} (suc n) lt ss = ss
    incMTimes {suc m} (suc n) lt ss = incMTimes n (1+n<m⟶n<m lt) (reverse (inc (reverse ss) m (n<1+n m)))

toPowersetFin : ∀{n} → Subset n → Fin (2 ^ n)
toPowersetFin ss = fromℕ≤ (subsetToNat< ss)

NfaToDfa : ∀{n} → Nfa n → Dfa (2 ^ n)
NfaToDfa {n} nfa =
  record
    { S = inject≤ (Nfa.S nfa) (n≤2^n n)
    ; δ = λ q c → toPowersetFin (Uδ (toSubset q) c)
    ; isF = λ p → any {n} λ q → (toSubset p ! q) ∧ (Nfa.F nfa ! q)
    }
  where
    Uδ : Subset n → Char → Subset n
    Uδ Qset c = U (mapS Qset (λ q → Nfa.δ nfa q c) ∅)

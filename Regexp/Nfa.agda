module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_; _<?_; _≤?_; s≤s; z≤n)
open import Data.Fin
  using (Fin; inject+; toℕ; raise; fromℕ≤; _ℕ-_; reduce≥)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; []) renaming (_++_ to _++ˢ_)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v) hiding (concat)
open import VecUtil
open import Equivalence

record Nfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    F : Subset n

δ̂ : ∀{n} → Nfa n → (Subset n) → String → (Subset n)
δ̂ {n} nfa qs [] = qs
δ̂ {n} nfa qs (x ∷ s) = δ̂ nfa (onestep qs x) s
  where
    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = U (mapS qs (λ q → Nfa.δ nfa q c) ∅)

infix 10 _↓′_
_↓′_ : ∀{n} → Nfa n → String → Set
nfa ↓′ s  = Nonempty ((Nfa.F nfa) ∩ (δ̂ nfa ⁅ Nfa.S nfa ⁆ s))


any : ∀{n} → (P : Fin n → Bool) → Bool
any {zero}  f = false
any {suc _} f = f fzero ∨ any λ x → f (fsuc x)

accepts : ∀{n} → Nfa n → Fin n → String → Bool
accepts nfa q []       = Nfa.F nfa ! q
accepts nfa q (c ∷ s) = any λ p → Nfa.δ nfa q c ! p ∧ accepts nfa p s

infix 10 _↓_
_↓_ : ∀{n} → Nfa n → String → Set
nfa ↓ s  = T (accepts nfa (Nfa.S nfa) s)


_↓?_ : ∀{n} → (nfa : Nfa n) → (s : String) → Dec (nfa ↓ s)
nfa ↓? s with accepts nfa (Nfa.S nfa) s
... | false = no (λ z → z)
... | true = yes tt

lem≤ : ∀{m n} → ¬ 1 + m ≤ n → m ≥ n
lem≤ {_} {zero} ¬p = z≤n
lem≤ {zero} {suc n} ¬p = ⊥-elim (¬p (s≤s z≤n))
lem≤ {suc m} {suc n} ¬p = s≤s (lem≤ (λ z → ¬p (s≤s z)))

concatNfa : ∀{n m} → Nfa n → Nfa m → Nfa (n + m)
concatNfa {n} {m} nfaL nfaR =
  record
    { S = inject+ m (Nfa.S nfaL)
    ; δ = δ
    ; F = ∅ ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (n + m) → Char → Subset (n + m)
    δ q c with toℕ q <? n
    δ q c | yes q<n with fromℕ≤ (q<n) ∈? Nfa.F nfaL
    δ q c | yes q<n | yes fin = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | yes q<n | no ¬fin = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++             ∅
    δ q c | no ¬q<n           =               ∅             ++ (Nfa.δ nfaR (reduce≥ q (lem≤ ¬q<n)) c)

unionNfa : ∀{n m} → Nfa n → Nfa m → Nfa (n + m)
unionNfa {n} {m} nfaL nfaR =
  record
    { S = inject+ m (Nfa.S nfaL)
    ; δ = δ
    ; F = (Nfa.F nfaL) ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (n + m) → Char → Subset (n + m)
    δ q c with toℕ q <? n
    δ q c | yes q<n with fromℕ≤ (q<n) ≟ Nfa.S nfaL
    δ q c | yes q<n | yes isS = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | yes q<n | no ¬isS = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++             ∅
    δ q c | no ¬q<n           =               ∅             ++ (Nfa.δ nfaR (reduce≥ q (lem≤ ¬q<n)) c)


















--

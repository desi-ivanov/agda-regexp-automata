module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_; _<?_; _≤?_; s≤s; z≤n)
open import Data.Fin
  using (Fin; inject+; toℕ; raise; fromℕ≤; _ℕ-_; reduce≥)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T)
open import Data.Bool.Properties using (T?)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; []; ++-idˡ) renaming (_++_ to _++ˢ_)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v) hiding (concat; splitAt)
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any using (index) renaming (any to any?)
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans; cong)

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

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero    i       = inj₂ i
splitAt (suc m) fzero    = inj₁ fzero
splitAt (suc m) (fsuc i) = Data.Sum.map fsuc (λ x → x) (splitAt m i)

concatNfa : ∀{n m} → Nfa n → Nfa m → Nfa (1 + n + m)
concatNfa {n} {m} nfaL nfaR =
  record
    { S = fzero
    ; δ = δ
    ; F = F
    }
  where
    δ : Fin (1 + n + m) → Char → Subset (1 + n + m)
    δ q c with splitAt 1 q
    δ q c | inj₁ z with Nfa.S nfaL ∈? Nfa.F nfaL
    δ q c | inj₁ z | yes isf           = ∅ {1} ++ (Nfa.δ nfaL (Nfa.S nfaL) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₁ z | no ¬isf           = ∅ {1} ++ (Nfa.δ nfaL (Nfa.S nfaL) c) ++             ∅
    δ q c | inj₂ mn with splitAt n mn
    δ q c | inj₂ mn | inj₁ l with l ∈? Nfa.F nfaL
    δ q c | inj₂ mn | inj₁ l | yes isf = ∅ {1} ++ (Nfa.δ nfaL l c)            ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₂ mn | inj₁ l | no ¬isf = ∅ {1} ++ (Nfa.δ nfaL l c)            ++             ∅
    δ q c | inj₂ mn | inj₂ r           = ∅ {1} ++             ∅               ++ (Nfa.δ nfaR r c)

    F : Subset (1 + n + m)
    F with Nfa.S nfaL ∈? Nfa.F nfaL
    F | yes p = ⁅ fzero ⁆ ++ (Nfa.F nfaR)
    F | no ¬p =     ∅     ++ (Nfa.F nfaR)

unionNfa : ∀{n m} → Nfa n → Nfa m → Nfa (n + m)
unionNfa {n} {m} nfaL nfaR =
  record
    { S = inject+ m (Nfa.S nfaL)
    ; δ = δ
    ; F = (Nfa.F nfaL) ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (n + m) → Char → Subset (n + m)
    δ q c with splitAt n q
    δ q c | inj₁ l with l ≟ Nfa.S nfaL
    δ q c | inj₁ l | yes isS = (Nfa.δ nfaL l c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₁ l | no ¬isS = (Nfa.δ nfaL l c) ++             ∅
    δ q c | inj₂ r           =             ∅               ++ (Nfa.δ nfaR r c)


starNfa : ∀{n} → Nfa n → Nfa (suc n)
starNfa nfa with any? T? (Nfa.F nfa)
starNfa {n} nfa | yes p =
  record
    { S = fzero
    ; δ = δ
    ; F = ⁅ fzero ⁆ ++ Nfa.F nfa
    }
  where
    δ : Fin (suc n) → Char → Subset (suc n)
    δ q c with splitAt 1 q
    δ q c | inj₁ z = ∅ ++ (Nfa.δ nfa (Nfa.S nfa) c)
    δ q c | inj₂ p with p ∈? Nfa.F nfa
    δ q c | inj₂ p | yes isf = ∅ ++ (⁅ Nfa.S nfa ⁆ ∪ (Nfa.δ nfa p) c)
    δ q c | inj₂ p | no ¬isf = ∅ ++                  (Nfa.δ nfa p) c
starNfa {suc n} nfa | no ¬p =
  record
    { S = fzero
    ; δ = λ _ _ → ⁅ fsuc fzero ⁆
    ; F = ⁅ fzero ⁆
    }
















--

module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
  using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; ⋃; Nonempty)
  renaming (⊥ to EmptySubset)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; [])
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v)
open import VecUtil
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

record Nfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    F : Subset n

δ̂ : ∀{n} → Nfa n → (Subset n) → String → (Subset n)
δ̂ {n} nfa qs [] = qs
δ̂ {n} nfa qs (x ∷ s) = δ̂ nfa (onestep qs x) s
  where
    computeifpresent : Fin n → Char → Subset n
    computeifpresent q c with qs ! q
    ... | false = EmptySubset
    ... | true = Nfa.δ nfa q c

    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = ⋃ (toList (build (λ q → computeifpresent q c)))

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

-- lemma-path : ∀{n s} {nfa : Nfa n}
--   → nfa ↓ s
--   → ∃[ v ]()

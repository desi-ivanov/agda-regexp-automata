module DfaNfa (Σ : Set) where
open import Data.Nat using (ℕ; suc; zero; _^_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset using (Subset; ⁅_⁆) renaming (⊥ to ∅)
open import Data.Bool using (Bool; false; _∨_; _∧_; if_then_else_; T)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Equivalence using (_⇔_; _≃_)
open import String Σ using (String; []; _∷_)
open import VecUtil using (U; mapS)
open import SubsetFinIso renaming (subset-fin-iso to ISO)

∈ᵇ-syntax = lookup
syntax ∈ᵇ-syntax v i = i ∈ᵇ v

record DFA (n : ℕ) : Set₂ where
  field
    S : Fin n
    δ : Fin n → Σ → Fin n
    F : Fin n → Bool

open DFA

δd* : ∀{n} → DFA n → Fin n → String → Fin n
δd* A q [] = q
δd* A q (x ∷ xs) = δd* A (δ A q x) xs

_↓ᵈ_ : ∀{n} → DFA n → String → Set
A ↓ᵈ s = T (F A (δd* A (S A) s))

record Nfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Σ → Subset n
    F : Fin n → Bool

open Nfa

δn* : ∀{n} → Nfa n → Subset n → String → Subset n
δn* {n} A qs [] = qs
δn* {n} A qs (c ∷ s) = δn* A (U (mapS qs (λ q → δ A q c) ∅)) s

any : ∀{n} → (P : Fin n → Bool) → Bool
any {zero}  P = false
any {suc _} P = P fzero ∨ any λ x → P (fsuc x)

infix 10 _↓ⁿ_
_↓ⁿ_ : ∀{n} → Nfa n → String → Set
A ↓ⁿ s = T(any λ q → F A q ∧ q ∈ᵇ (δn* A ⁅ S A ⁆ s))

NFAtoDFA : ∀{n} → Nfa n → DFA (2 ^ n)
NFAtoDFA {n} N = record
  { S = _≃_.to ISO ⁅ S N ⁆
  ; δ = λ qs c → _≃_.to ISO (U (mapS (_≃_.from ISO qs) (λ q → δ N q c) ∅))
  ; F = λ qs → any λ q → F N q ∧ q ∈ᵇ _≃_.from ISO qs
  }

prop : ∀{n} → (N : Nfa n) → ∀(qs) → (s : String) →
  δn* N qs s ≡ _≃_.from ISO (δd* (NFAtoDFA N) (_≃_.to ISO qs) s)
prop N qs []      rewrite _≃_.from∘to ISO qs = refl
prop N qs (x ∷ s) rewrite prop N (U (mapS qs (λ q → δ N q x) ∅)) s
                        | _≃_.from∘to ISO qs = refl

theorem1 : ∀{n : ℕ} → (N : Nfa n) → (s : String) →
      N ↓ⁿ s ⇔ NFAtoDFA N ↓ᵈ s
theorem1 {n} N s rewrite prop N ⁅ S N ⁆ s =
  record { to = λ x → x ; from = λ x → x }

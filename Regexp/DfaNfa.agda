module DfaNfa where
open import Dfa renaming (δ̂ to δ̂ᵈ; _↓_ to _↓ᵈ_; _↓?_ to _↓ᵈ?_)
open import Nfa renaming (δ̂ to δ̂ⁿ; _↓_ to _↓ⁿ_; _↓?_ to _↓ⁿ?_)
open import Data.Bool using (Bool; false; true; not; T; _∨_; _∧_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
  using (Fin)
  renaming (suc to fsuc; zero to fzero)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; ⋃; Nonempty)
  renaming (⊥ to EmptySubset)
open import Data.Vec
  using (zipWith; _[_]=_; here; there; toList; replicate)
  renaming (_∷_ to _∷v_; [] to []v)
open import String
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans)
open Eq.≡-Reasoning

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














--

module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
  using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; ⋃; Nonempty)
  renaming (⊥ to EmptySubset)
open import Data.Bool using (false; true)
open import String using (String; _∷_; [])
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v)
open import VecUtil
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

infix 10 _↓_
_↓_ : ∀{n} → Nfa n → String → Set
nfa ↓ s  = Nonempty ((Nfa.F nfa) ∩ (δ̂ nfa ⁅ Nfa.S nfa ⁆ s))

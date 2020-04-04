module ENfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin
  using (Fin; fromℕ≤)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; ⋃; Nonempty)
  renaming (⊥ to EmptySubset)
open import Data.Bool using (false; true)
open import String using (String) renaming (_∷_ to _∷ˢ_; [] to []ˢ)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v)
open import VecUtil

record eNfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    εδ : Fin n → Subset n
    F : Subset n

{-# TERMINATING #-}
ecloseQ : {n : ℕ} → eNfa n → Subset n → Fin n → Subset n → Subset n
ecloseQS : {n : ℕ} → eNfa n → Subset n → Subset n → Subset n

ecloseQ enfa qs q visited with qs ! q | visited ! q
... | false | false = EmptySubset
... | false | true = EmptySubset
... | true | false = ⁅ q ⁆ ∪ (ecloseQS enfa (eNfa.εδ enfa q) (⁅ q ⁆ ∪ visited))
... | true | true = EmptySubset

ecloseQS enfa qs visited = ⋃ (toList (build λ q → ecloseQ enfa qs q visited))

eclose : ∀{n} → eNfa n → Subset n → Subset n
eclose {n} enfa qs = ecloseQS enfa qs EmptySubset

δ̂ : ∀{n} → eNfa n → (Subset n) → String → (Subset n)
δ̂ {n} enfa qs []ˢ = eclose enfa qs
δ̂ {n} enfa qs (x ∷ˢ s) = δ̂ enfa (eclose enfa (onestep (eclose enfa qs) x)) s
  where
    computeifpresent : Fin n → Char → Subset n
    computeifpresent q c with qs ! q
    ... | false = EmptySubset
    ... | true = eNfa.δ enfa q c

    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = ⋃ (toList (build (λ q → computeifpresent q c)))


infix 10 _↓_
_↓_ : ∀{n} → eNfa n → String → Set
enfa ↓ s  = Nonempty (eNfa.F enfa ∩ (δ̂ enfa ⁅ eNfa.S enfa ⁆ s))

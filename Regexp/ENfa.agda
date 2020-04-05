module ENfa where
open import Data.Char using (Char)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
  using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; ⋃; Nonempty)
  renaming (⊥ to ∅)
open import Data.Bool using (false; true)
open import String using (String; _∷_; [])
open import Data.Vec using (toList)
open import VecUtil

record eNfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    εδ : Fin n → Subset n
    F : Subset n

ecloseQ : {n : ℕ} → eNfa n → Subset n → Fin n → Subset n → ℕ → Subset n
ecloseQS : {n : ℕ} → eNfa n → Subset n → Subset n → ℕ → Subset n

ecloseQ enfa qs q visited m with qs ! q | visited ! q
... | false | false = ∅
... | false | true = ∅
... | true | true = ∅
ecloseQ enfa qs q visited zero | true | false = ∅
ecloseQ enfa qs q visited (suc m) | true | false = ⁅ q ⁆ ∪ (ecloseQS enfa (eNfa.εδ enfa q) (⁅ q ⁆ ∪ visited) (m))

ecloseQS enfa qs visited zero = ∅
ecloseQS enfa qs visited (suc m) = ⋃ (toList (build λ q → ecloseQ enfa qs q visited m))

eclose : ∀{n} → eNfa n → Subset n → Subset n
eclose {n} enfa qs = ecloseQS enfa qs ∅ n

δ̂ : ∀{n} → eNfa n → (Subset n) → String → (Subset n)
δ̂ {n} enfa qs [] = eclose enfa qs
δ̂ {n} enfa qs (c ∷ s) = δ̂ enfa (eclose enfa (onestep (eclose enfa qs) c)) s
  where
    computeifpresent : Fin n → Char → Subset n
    computeifpresent q c with qs ! q
    ... | false = ∅
    ... | true = eNfa.δ enfa q c

    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = ⋃ (toList (build (λ q → computeifpresent q c)))


infix 10 _↓_
_↓_ : ∀{n} → eNfa n → String → Set
enfa ↓ s  = Nonempty (eNfa.F enfa ∩ (δ̂ enfa ⁅ eNfa.S enfa ⁆ s))

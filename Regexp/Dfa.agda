module Dfa where
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; [])
open import Equivalence

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

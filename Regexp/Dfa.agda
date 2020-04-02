module Dfa where
open import Data.Char as Char
open import Data.Nat using (ℕ; zero; suc; _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Fin using (Fin; _≟_)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_)
open import String using (String; foldl; _∷_; [])
open import Equivalence
open import Axiom.Extensionality.Propositional using (Extensionality)
record Dfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Fin n
    isF : Fin n → Bool

δ̂ : ∀{n} → (Fin n → Char → Fin n) → (q : Fin n) → String → Fin n
δ̂ δ q [] = q
δ̂ δ q (x ∷ s) = δ̂ δ (δ q x) s

infix 10 _∈_
_∈_ : ∀{n} → String → Dfa n → Bool
s ∈ dfa = Dfa.isF dfa (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s)

complement : ∀{n} → Dfa n → Dfa n
complement dfa =
  record
    { S = Dfa.S dfa
    ; δ = Dfa.δ dfa
    ; isF = λ x → not (Dfa.isF dfa x)
    }

complement-closure : ∀{s n} {dfa : Dfa n}
  → T(s ∈ dfa) ⇔ ¬ T (s ∈ (complement dfa))
complement-closure {s}{n}{dfa} = record { to = to {s}{n}{dfa} ; from = from {s}{n}{dfa} }
  where
    to : ∀{s n} {dfa : Dfa n} → T (s ∈ dfa) → ¬ T (s ∈ complement dfa)
    to {s} {n} {dfa} p with s ∈ dfa
    ... | true = λ z → z
    from : ∀{s n} {dfa : Dfa n} → ¬ T (s ∈ complement dfa) → T (s ∈ dfa)
    from {s} {n} {dfa} np with s ∈ complement dfa | s ∈ dfa
    ... | false | false = np tt
    ... | false | true = tt
    ... | true | false = np tt
    ... | true | true = tt

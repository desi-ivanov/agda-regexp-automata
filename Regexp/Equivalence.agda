module Equivalence where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _≥_; _≤_; _<_; s≤s; z≤n; _+_; _*_; _^_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F) renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-inject+)
open import Data.Product using (_×_; Σ; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Fin.Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

_IFF_ : {A B : Set} → (A → B) → (B → A) → A ⇔ B
f IFF g = record { to = f ; from = g }


infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

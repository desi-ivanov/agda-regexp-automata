module RegExpSet where
open import Data.List
open import Regexp using (RegExp)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Char as Char using ()
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)

RegExpSet = List RegExp

EmptyRegExpSet : List RegExp
EmptyRegExpSet = []

open RegExp
_≟_ : (E F : RegExp) → Dec (E ≡ F)
⟨⟩ ≟ ⟨⟩ = yes refl
⟨⟩ ≟ ⟨ε⟩ = no (λ ())
⟨⟩ ≟ Atom c = no (λ ())
⟨⟩ ≟ (F + F₁) = no (λ ())
⟨⟩ ≟ (F · F₁) = no (λ ())
⟨⟩ ≟ (F *) = no (λ ())
⟨ε⟩ ≟ ⟨⟩ = no (λ ())
⟨ε⟩ ≟ ⟨ε⟩ = yes refl
⟨ε⟩ ≟ Atom c = no (λ ())
⟨ε⟩ ≟ (F + F₁) = no (λ ())
⟨ε⟩ ≟ (F · F₁) = no (λ ())
⟨ε⟩ ≟ (F *) = no (λ ())
Atom c ≟ ⟨⟩ = no (λ ())
Atom c ≟ ⟨ε⟩ = no (λ ())
Atom c ≟ Atom c₁ with Char._≟_ c c₁
(Atom c ≟ Atom .c) | yes refl = yes refl
(Atom c ≟ Atom c₁) | no ¬p = no λ{ refl → ¬p refl }
Atom c ≟ (F + F₁) = no (λ ())
Atom c ≟ (F · F₁) = no (λ ())
Atom c ≟ (F *) = no (λ ())
(E + E₁) ≟ ⟨⟩ = no (λ ())
(E + E₁) ≟ ⟨ε⟩ = no (λ ())
(E + E₁) ≟ Atom c = no (λ ())
(E + E₁) ≟ (F + F₁) with E ≟ F | E₁ ≟ F₁
... | yes refl | yes refl = yes refl
... | yes p | no ¬p = no (λ {refl → ¬p refl } )
... | no ¬p | yes p = no (λ {refl → ¬p refl } )
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl } )
(E + E₁) ≟ (F · F₁) = no (λ ())
(E + E₁) ≟ (F *) = no (λ ())
(E · E₁) ≟ ⟨⟩ = no (λ ())
(E · E₁) ≟ ⟨ε⟩ = no (λ ())
(E · E₁) ≟ Atom c = no (λ ())
(E · E₁) ≟ (F + F₁) = no (λ ())
(E · E₁) ≟ (F · F₁) with E ≟ F | E₁ ≟ F₁
... | yes refl | yes refl = yes refl
... | yes p | no ¬p = no (λ {refl → ¬p refl } )
... | no ¬p | yes p = no (λ {refl → ¬p refl } )
... | no ¬p | no ¬p₁ = no (λ {refl → ¬p refl } )
(E · E₁) ≟ (F *) = no (λ ())
(E *) ≟ ⟨⟩ = no (λ ())
(E *) ≟ ⟨ε⟩ = no (λ ())
(E *) ≟ Atom c = no (λ ())
(E *) ≟ (F + F₁) = no (λ ())
(E *) ≟ (F · F₁) = no (λ ())
(E *) ≟ (F *) with E ≟ F
... | yes refl = yes refl
... | no ¬p = no λ{ refl → ¬p refl }

_∈?_ : (x : RegExp) → (xs : List RegExp) → Dec (x ∈ xs)
x ∈? [] = no (λ ())
x ∈? (x₁ ∷ xs) with x ≟ x₁
... | yes p = yes (here p)
... | no ¬p with x ∈? xs
... | yes p = yes (there p)
... | no ¬p₁ = no λ{ (here px) → ¬p px; (there a) → ¬p₁ a }

_∪_ : List RegExp → List RegExp → List RegExp
[] ∪ ys = ys
(x ∷ xs) ∪ ys with x ∈? (xs ∪ ys)
... | yes p = xs ∪ ys
... | no ¬p = x ∷ (xs ∪ ys)

_⊆_ : List RegExp → List RegExp → Set
xs ⊆ ys = All (_∈ ys) xs

postulate
  ∪-preserves-⊆ʳ : ∀{a b} → (a ⊆ b) → (c : List RegExp) → a ⊆ (b ∪ c)
  ∪-preserves-⊆ˡ : ∀{a b} → (a ⊆ b) → (c : List RegExp) → a ⊆ (c ∪ b)
  ∪-injects-∪⊆ʳ : ∀{a b c} → c ⊆ (a ∪ b) → (c ∪ b) ⊆ (a ∪ b)
  ∪-injects-⊆ʳ : ∀{a b c} → c ⊆ a → b ⊆ a → (c ∪ b) ⊆ a
  ∪-self-⊆ : ∀{a b} → b ⊆ a → (b ∪ a) ⊆ a
  ∷-preserves-⊆ : ∀{a b c} → b ⊆ a → b ⊆ (c ∷ a)
  ∪-preserves-Pˡ : ∀{a b} {P : RegExp → Set} → Any P a → Any P (a ∪ b)
  ∪-preserves-Pʳ : ∀{a b} {P : RegExp → Set} → Any P b → Any P (a ∪ b)
  ⊆-preserves-¬P : ∀{a b} {P : RegExp → Set} → a ⊆ b → ¬ (Any P b) → ¬ (Any P a)

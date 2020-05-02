open import Data.List
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)
open import Data.Empty using (⊥; ⊥-elim)

module RegExpSet (Σ : Set) (_≟Σ_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import Regexp Σ using (RegExp)

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
Atom c ≟ Atom c₁ with _≟Σ_ c c₁
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
--------------------------------------------------------------------------------
-- Properties of _∪_ and _⊆_

∷-preserves-⊆ : ∀{a b c} → b ⊆ a → b ⊆ (c ∷ a)
∷-preserves-⊆ {a} {_} {c} [] = []
∷-preserves-⊆ {a} {_} {c} (px ∷ f) = there px ∷ ∷-preserves-⊆ f

⊆-refl : ∀{a} → a ⊆ a
⊆-refl {[]} = []
⊆-refl {x ∷ a} = here refl ∷ ∷-preserves-⊆ (⊆-refl {a})

⊆-union-selfʳ : (a b : RegExpSet) → b ⊆ (a ∪ b)
⊆-union-selfʳ [] b = ⊆-refl
⊆-union-selfʳ (x ∷ a) b with ⊆-union-selfʳ a b
... | IH with x ∈? (a ∪ b)
⊆-union-selfʳ (x ∷ a) b | IH | yes p = IH
⊆-union-selfʳ (x ∷ a) b | IH | no ¬p = ∷-preserves-⊆ IH

⊆-preserves-∈ : ∀{a b c} → b ⊆ a → c ∈ b → c ∈ a
⊆-preserves-∈ (here refl ∷ pxs) (here py) = here py
⊆-preserves-∈ (there px ∷ pxs) (here refl) = there px
⊆-preserves-∈ (px ∷ pxs) (there pys) = ⊆-preserves-∈ pxs pys

⊆-trans : ∀{a b c} → a ⊆ b → b ⊆ c → a ⊆ c
⊆-trans {_} {b} {c} [] pr = []
⊆-trans {_} {b} {c} (px ∷ pl) pr = ⊆-preserves-∈ pr px ∷ ⊆-trans pl pr

∪-preserves-∈ˡ : ∀{a b c} → c ∈ a → c ∈ (a ∪ b)
∪-preserves-∈ˡ {x ∷ a} {b} {.x} (here refl) with x ∈? (a ∪ b)
∪-preserves-∈ˡ {x ∷ a} {b} {.x} (here refl) | yes p = p
∪-preserves-∈ˡ {x ∷ a} {b} {.x} (here refl) | no ¬p = here refl
∪-preserves-∈ˡ {x ∷ a} {b} {c} (there pys) with ∪-preserves-∈ˡ {a}{b}{c} pys
... | ind with x ∈? (a ∪ b)
∪-preserves-∈ˡ {x ∷ a} {b} {c} (there pys) | ind | yes p = ind
∪-preserves-∈ˡ {x ∷ a} {b} {c} (there pys) | ind | no ¬p = there ind

∷-preserves-∈ : ∀{a b}{c : RegExp} → b ∈ a → b ∈ (c ∷ a)
∷-preserves-∈ p = there p

∪-preserves-∈ʳ : ∀{a b c} → c ∈ b → c ∈ (a ∪ b)
∪-preserves-∈ʳ {[]} {ys} {c} p = p
∪-preserves-∈ʳ {x ∷ xs} {ys} {c} p with ∪-preserves-∈ʳ {xs}{ys}{c} p
... | ind with x ∈? (xs ∪ ys)
∪-preserves-∈ʳ {x ∷ xs} {ys} {c} p | ind | yes p₁ = ind
∪-preserves-∈ʳ {x ∷ xs} {ys} {c} p | ind | no ¬p = there ind

∪-preserves-⊆ʳ : ∀{a b} → (a ⊆ b) → (c : List RegExp) → a ⊆ (b ∪ c)
∪-preserves-⊆ʳ [] cs = []
∪-preserves-⊆ʳ (px ∷ pxs) cs = ∪-preserves-∈ˡ px ∷ (∪-preserves-⊆ʳ pxs cs)

∪-preserves-⊆ˡ : ∀{a b} → (a ⊆ b) → (c : List RegExp) → a ⊆ (c ∪ b)
∪-preserves-⊆ˡ [] cs = []
∪-preserves-⊆ˡ (px ∷ pxs) cs = ∪-preserves-∈ʳ {cs} px ∷ (∪-preserves-⊆ˡ pxs cs)

∪-self-⊆ : ∀{a b} → b ⊆ a → (b ∪ a) ⊆ a
∪-self-⊆ [] = ⊆-refl
∪-self-⊆ {a}{x ∷ xs} (px ∷ pl) with ∪-self-⊆ pl
... | ind with x ∈? (xs ∪ a)
∪-self-⊆ {a} {x ∷ xs} (px ∷ pl) | ind | yes p = ind
∪-self-⊆ {a} {x ∷ xs} (px ∷ pl) | ind | no ¬p = px ∷ ind

∪-injects-∪⊆ʳ : ∀{a b c} → c ⊆ (a ∪ b) → (c ∪ b) ⊆ (a ∪ b)
∪-injects-∪⊆ʳ {_} {[]} {[]} s = s
∪-injects-∪⊆ʳ {a} {[]} {c ∷ cs} (px ∷ s) with ∪-injects-∪⊆ʳ {a}{[]}{cs} s
... | IH with c ∈? (cs ∪ [])
∪-injects-∪⊆ʳ {a} {[]} {c ∷ cs} (px ∷ s) | IH | yes p = IH
∪-injects-∪⊆ʳ {a} {[]} {c ∷ cs} (px ∷ s) | IH | no ¬p = px ∷ IH
∪-injects-∪⊆ʳ {a} {b} {[]} s = ⊆-union-selfʳ a b
∪-injects-∪⊆ʳ {a} {b} {c ∷ cs} (px ∷ s) with ∪-injects-∪⊆ʳ {a}{b} s
... | IH with c ∈? (cs ∪ b)
∪-injects-∪⊆ʳ {a} {b} {c ∷ cs} (px ∷ s) | IH | yes p = IH
∪-injects-∪⊆ʳ {a} {b} {c ∷ cs} (px ∷ s) | IH | no ¬p = px ∷ IH

∪-injects-⊆ʳ : ∀{a b c} → c ⊆ a → b ⊆ a → (c ∪ b) ⊆ a
∪-injects-⊆ʳ {a} {b} {[]} f s = s
∪-injects-⊆ʳ {a} {b} {x ∷ c} (px ∷ f) s with ∪-injects-⊆ʳ {a}{b}{c} f s
... | IH with x ∈? (c ∪ b)
∪-injects-⊆ʳ {a} {b} {x ∷ c} (px ∷ f) s | IH | yes p = IH
∪-injects-⊆ʳ {a} {b} {x ∷ c} (px ∷ f) s | IH | no ¬p = px ∷ IH

Px∈s : ∀{A : Set}{s : List A}{P : A → Set}{x} → P x → x ∈ s → Any P s
Px∈s {_} {.(_ ∷ _)} p (here refl) = here p
Px∈s {_} {.(_ ∷ _)} p (there t) = there (Px∈s p t)

∪-preserves-Pˡ : ∀{a b} {P : RegExp → Set} → Any P a → Any P (a ∪ b)
∪-preserves-Pˡ {x ∷ a} {b} {P} (here px) with x ∈? (a ∪ b)
∪-preserves-Pˡ {x ∷ a} {b} {P} (here px) | yes p = Px∈s px p
∪-preserves-Pˡ {x ∷ a} {b} {P} (here px) | no ¬p = here px
∪-preserves-Pˡ {x ∷ a} {b} {P} (there an) with ∪-preserves-Pˡ {a} {b}{P} an
... | IH with x ∈? (a ∪ b)
∪-preserves-Pˡ {x ∷ a} {b} {P} (there an) | IH | yes p = IH
∪-preserves-Pˡ {x ∷ a} {b} {P} (there an) | IH | no ¬p = there IH

∪-preserves-Pʳ : ∀{a b} {P : RegExp → Set} → Any P b → Any P (a ∪ b)
∪-preserves-Pʳ {[]} {bs} {P} p = p
∪-preserves-Pʳ {x ∷ a} {bs} {P} pin with x ∈? (a ∪ bs)
∪-preserves-Pʳ {x ∷ a} {bs} {P} pin | yes p = ∪-preserves-Pʳ {a}{bs}{P} pin
∪-preserves-Pʳ {x ∷ a} {bs} {P} pin | no ¬p = there (∪-preserves-Pʳ {a}{bs}{P} pin)

⊆-preserves-¬P : ∀{a b} {P : RegExp → Set} → a ⊆ b → ¬ (Any P b) → ¬ (Any P a)
⊆-preserves-¬P {_} {b} {P} (px ∷ ss) np (here px₁) = ⊥-elim (np (Px∈s px₁ px) )
⊆-preserves-¬P {_} {b} {P} (px ∷ ss) np (there abs) = ⊆-preserves-¬P ss np abs

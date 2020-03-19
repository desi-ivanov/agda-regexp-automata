module negation where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import isomorphism using (_≃_; extensionality)
open import relations using (_<_)
open import connectives using (⟨_,_⟩; _×_; proj₁; proj₂)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.
<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive (suc n) (_<_.s<s x) = <-irreflexive n x

-- Show that strict inequality satisfies trichotomy, that is,
-- for any naturals m and n exactly one of the following holds:
-- m < n
-- m ≡ n
-- m > n
-- Here “exactly one” means that not only one of the three must hold,
-- but that when one holds the negation of the other two must also hold.
trichotomy<₁ : ∀ (m n : ℕ) → m < n → ¬ (m ≡ n)
trichotomy<₁ (suc m) (suc n) (_<_.s<s mn) refl = <-irreflexive m mn
trichotomy<₂ : ∀ {m n : ℕ} → m < n → ¬ (n < m)
trichotomy<₂ (_<_.s<s mn) (_<_.s<s nm) = trichotomy<₂ mn nm

-- Show that conjunction, disjunction,
-- and negation are related by a version of De Morgan’s Law.
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record
  { to      = λ z → ⟨ (λ x → z (inj₁ x)) , (λ x → z (inj₂ x)) ⟩
  ; from    = λ { ⟨ x , x₁ ⟩ (inj₁ x₂) → x x₂
                ; ⟨ x , x₁ ⟩ (inj₂ y) → x₁ y
                }
  ; from∘to = λ z → extensionality λ x → ⊥-elim (z x)
  ; to∘from = λ { ⟨ x , x₁ ⟩ → refl}
  }

-- Do we also have the following  ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- toin : ∀ {A B : Set} → A × B → ¬ ((¬ A) ⊎ (¬ B))
-- toin ⟨ x , x₁ ⟩ (inj₁ x₂) = x₂ x
-- toin ⟨ x , x₁ ⟩ (inj₂ y) = y x₁
-- postulate
--   negneg : ∀ {A : Set} → ¬ ¬ A → A
-- postulate
--   to : ∀ {A B : Set}   → ¬ (A × B) → (¬ A) ⊎ (¬ B)
-- from : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
-- from (inj₁ x) ⟨ x₁ , x₂ ⟩ = x x₁
-- from (inj₂ x) ⟨ x₁ , x₂ ⟩ = x
-- foo : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- foo = record
--   { to = to
--   ; from = from
--   ; from∘to = λ z → extensionality λ x → ⊥-elim (z x)
--   ; to∘from = λ{
--           (inj₁ x) → begin
--               to (from (inj₁ x))
--             ≡⟨⟩
--             {!   !}
--               -- (¬ A) ⊎ (¬ B)
--             ≡⟨⟩
--             {!   !}
--             ≡⟨⟩
--               {!   !}
--           ; (inj₂ y) → {!   !}}
--   }


postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))



-- Classical logic stretch
-- excluded middle implies double negation elimination
em-implies-doubleneg : ∀ {A : Set}
  → A ⊎ ¬ A
  → (¬ ¬ A) → A
em-implies-doubleneg (inj₁ x) nnx = x
em-implies-doubleneg (inj₂ nx) nnx = ⊥-elim (nnx nx)

em-implies-peirce : ∀ {A B : Set}
  → A ⊎ ¬ A
  → ((A → B) → A) → A
em-implies-peirce (inj₁ x) = λ _ → x
em-implies-peirce (inj₂ y) k = k (λ x → ⊥-elim (y x))

em-implies-disjunction : ∀ {A B : Set}
  → A ⊎ ¬ A
  → (A → B) → ¬ A ⊎ B
em-implies-disjunction (inj₁ x) y = inj₂ (y x)
em-implies-disjunction (inj₂ nx) y = inj₁ nx

em-implies-demorgan : ∀ {A B : Set}
  → A ⊎ ¬ A
  → B ⊎ ¬ B
  → ¬ ((¬ A) × (¬ B)) → A ⊎ B
em-implies-demorgan (inj₁ a) _ n = inj₁ a
em-implies-demorgan (inj₂ na) (inj₁ b) n = inj₂ b
em-implies-demorgan (inj₂ na) (inj₂ nb) n = ⊥-elim (n  ⟨ na , nb ⟩ )

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- Show that any negated formula is stable, and that the conjunction of two
-- stable formulas is stable.

dne->stable : ∀ {A : Set} → ¬ A → Stable A
dne->stable a = λ x → ⊥-elim (x a)

conj->stable : ∀ {A B : Set} → (Stable A) × (Stable B) → Stable ((Stable A) × (Stable B))
conj->stable z _ = z




























--

module introduction_examples where
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Even : ℕ → Set where
  zero : Even zero
  next : ∀{n}
    → Even n
    → Even (suc (suc n))

sum-is-even : ∀{n m}
  → Even n
  → Even m
    ------------
  → Even (n + m)
sum-is-even zero em = em
sum-is-even (next en) em = next (sum-is-even en em)

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

¬_ : Set → Set
¬ A = A → ⊥

⊥-elim : ∀ {A : Set}
  → ⊥
  → A
⊥-elim ()

contradiction : ∀{P Q} → P → ¬ P → Q
contradiction p ¬p = ⊥-elim (¬p p)

data Odd : ℕ → Set where
  one : Odd (suc zero)
  next : ∀{n}
    → Odd n
    → Odd (suc (suc n))

even⇒suc-odd : ∀{x} → Even x → Odd (suc x)
even⇒suc-odd zero = one
even⇒suc-odd (next a) = next (even⇒suc-odd a)

odd⇒suc-even : ∀{x} → Odd x → Even (suc x)
odd⇒suc-even one = next zero
odd⇒suc-even (next a) = next (odd⇒suc-even a)

ℕ-Even-or-Odd : ∀(x : ℕ) → Even x ⊎ Odd x
ℕ-Even-or-Odd zero = inj₁ zero
ℕ-Even-or-Odd (suc x) with ℕ-Even-or-Odd x
... | inj₁ ev = inj₂ (even⇒suc-odd ev)
... | inj₂ od = inj₁ (odd⇒suc-even od)

even⇒¬odd : ∀{x : ℕ} → Even x → ¬ Odd x
even⇒¬odd zero = λ ()
even⇒¬odd (next ev) (next od) = ⊥-elim((even⇒¬odd ev) od)

ℕ-not-both-even-odd : ∀{x : ℕ} → ¬ (Even x × Odd x)
ℕ-not-both-even-odd ⟨ ev , od ⟩ = ⊥-elim (even⇒¬odd ev od)

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬even⇒suc-even : ∀{x : ℕ} → ¬ Even x → Even (suc x)
¬even⇒suc-even {zero} ne = ⊥-elim (ne zero)
¬even⇒suc-even {suc zero} ne = next zero
¬even⇒suc-even {suc (suc x)} ne = next (¬even⇒suc-even (λ z → ne (next z)))

Even? : ∀(x : ℕ) → Dec (Even x)
Even? x with ℕ-Even-or-Odd x
... | inj₁ xEven = yes xEven
... | inj₂ xOdd = no (λ xEven → ℕ-not-both-even-odd ⟨ xEven , xOdd ⟩)



--

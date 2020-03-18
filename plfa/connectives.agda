module connectives where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open isomorphism.≃-Reasoning


data _×_ (A B : Set) : Set where
  ⟨_,_⟩ :
      A
    → B
    ------
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  --------
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
  --------
  → B
proj₂ ⟨ x , y ⟩ = y

record _×'_ (A B : Set) : Set where
  field
    proj1' : A
    porj2' : B
open _×'_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record {
    to = λ x → ⟨ (proj₂ x), (proj₁ x) ⟩
    ; from = λ x → ⟨ (proj₂ x), (proj₁ x) ⟩
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record {
    to = λ x → ⟨ proj₁ (proj₁ x) , ⟨ proj₂ (proj₁ x) , proj₂ x ⟩ ⟩
    ; from = λ x → ⟨ ⟨ proj₁ x , proj₁ (proj₂ x) ⟩ , proj₂ (proj₂ x) ⟩
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× =
  record {
    to = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩
    ; from = λ x → record {
                          to = proj₁ x
                          ; from = proj₂ x
                        }
    ; from∘to = λ x → refl
    ; to∘from = λ{ ⟨ x , y ⟩ → refl }
  }


data ⊤ : Set where
  tt :
    --
    ⊤


η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ x → proj₂ x
    ; from = λ x → ⟨ tt , x ⟩
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ y → refl
    }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

infixr 1 _⊎_

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

⊎-flip : {A B : Set} →  A ⊎ B → B ⊎ A
⊎-flip (inj₁ x) = inj₂ x
⊎-flip (inj₂ x) = inj₁ x

⊎-flip∘⊎-flip-identity : ∀ {A B : Set} (w : A ⊎ B) → ⊎-flip (⊎-flip w) ≡ w
⊎-flip∘⊎-flip-identity (inj₁ x) = refl
⊎-flip∘⊎-flip-identity (inj₂ x) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = ⊎-flip
  ; from = ⊎-flip
  ; from∘to = ⊎-flip∘⊎-flip-identity
  ; to∘from = ⊎-flip∘⊎-flip-identity
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to =      λ { (inj₁ (inj₁ x)) → inj₁ x
                ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
                ; (inj₂ x)→ inj₂ (inj₂ x)
                }
  ; from =    λ { (inj₁ x) → inj₁ (inj₁ x)
                ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
                ; (inj₂ (inj₂ x)) → inj₂ x
                }
  ; from∘to = λ { (inj₁ (inj₁ x)) → refl
                ; (inj₁ (inj₂ x)) → refl
                ; (inj₂ x) → refl
                }
  ; to∘from = λ { (inj₁ x) → refl
                ; (inj₂ (inj₁ x)) → refl
                ; (inj₂ (inj₂ x)) → refl
                }
  }

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { to = λ{ (inj₂ x) → x}
  ; from = λ{ x → inj₂ x }
  ; from∘to = λ{ (inj₂ x) → refl}
  ; to∘from = λ{ x → refl }
  }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ = record
  { to = λ{ (inj₁ x) → x}
  ; from = λ{ x → inj₁ x }
  ; from∘to = λ{ (inj₁ x) → refl}
  ; to∘from = λ{ x → refl }
  }

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }


⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , y ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , y ⟩ = inj₂ ⟨ x , y ⟩


⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩

-- Does the converse hold? If so, prove; if not, give a counterexample.
--     ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- No. Eg: when only A and D hold, A × B cannot hold, neither C × D









--

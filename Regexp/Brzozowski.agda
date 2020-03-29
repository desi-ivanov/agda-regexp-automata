module Brzozowski where
open import Regexp
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Char as Char
open import String using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)

open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data Nullable : RegExp → Set where
  null⟨ε⟩ : Nullable ⟨ε⟩
  null+l : ∀{F G} → Nullable F → Nullable (F + G)
  null+r : ∀{F G} → Nullable G → Nullable (F + G)
  null, : ∀{F G} → Nullable F → Nullable G → Nullable (F , G)
  null* : ∀{F} → Nullable (F *)

⊥-elim-sum : ∀ {A B : Set} → ¬ A → ¬ B → A ⊎ B → ⊥
⊥-elim-sum a b (inj₁ x) = a x
⊥-elim-sum a b (inj₂ y) = b y

⊥-elim-product : ∀ {A B : Set} → ¬ A ⊎ ¬ B → A × B → ⊥
⊥-elim-product (inj₁ x) ⟨ fst , snd ⟩ = x fst
⊥-elim-product (inj₂ y) ⟨ fst , snd ⟩ = y snd

sumnullable : ∀ {E F} → Nullable (E + F) → Nullable E ⊎ Nullable F
sumnullable (null+l a) = inj₁ a
sumnullable (null+r a) = inj₂ a

seqnullable : ∀ {E F} → Nullable (E , F) → Nullable E × Nullable F
seqnullable (null, x y) = ⟨ x , y ⟩


isNullable : (E : RegExp) → Dec (Nullable E)
isNullable ⟨⟩ = no (λ ())
isNullable ⟨ε⟩ = yes null⟨ε⟩
isNullable (Atom c) = no (λ ())
isNullable (r + s) with isNullable r | isNullable s
isNullable (r + s) | yes p | yes p₁ = yes (null+l p)
isNullable (r + s) | yes p | no ¬p = yes (null+l p)
isNullable (r + s) | no ¬p | yes p = yes (null+r p)
isNullable (r + s) | no p | no p2 = no (λ x → ⊥-elim-sum p p2 (sumnullable x))
isNullable (r , s)  with isNullable r | isNullable s
isNullable (r , s) | yes p | yes p₁ = yes (null, p p₁)
isNullable (r , s) | yes p | no ¬p = no λ x → ⊥-elim-product (inj₂ ¬p) (seqnullable x)
isNullable (r , s) | no ¬p | yes p = no λ x → ⊥-elim-product (inj₁ ¬p) (seqnullable x)
isNullable (r , s) | no ¬p | no ¬p₁ = no λ x → ⊥-elim-product (inj₁ ¬p) (seqnullable x)
isNullable (r *) = yes null*

infixl 11 _[_]
_[_] : RegExp → Char → RegExp
⟨⟩ [ a ] = ⟨⟩
⟨ε⟩ [ a ]   = ⟨⟩
(Atom b) [ a ]  with b ≟ a
... | yes p = ⟨ε⟩
... | no ¬p = ⟨⟩
(F + G) [ a ] = F [ a ] + G [ a ]
(F , G) [ a ] with isNullable F
...        | yes  _ = (F [ a ]) , G + G [ a ]
...        | no _ = (F [ a ]) , G
(F *) [ a ] = (F [ a ]) ,  F *

postulate
  split-* : ∀ {a}{s}{E}
    → (a ∷ s) ∈ℒ(E *)
      ---------------
    → (a ∷ s) ∈ℒ(E) ⊎  (∃[ t ] (∃[ u ] ( (a ∷ s) ≡ (a ∷ t) ++ u × (a ∷ t) ∈ℒ(E) × u ∈ℒ(E *) )))

theorem1 : ∀ {E : RegExp}
  → ε ∈ℒ(E) ⇔ Nullable E
theorem1 = record { to = to ; from = from }
  where
    to : ∀ {E} → ε ∈ℒ E → Nullable E
    to {⟨ε⟩} x = null⟨ε⟩
    to {E + F} (∈ℒ+l x) = null+l (to x)
    to {E + F} (∈ℒ+r x) = null+r (to x)
    to {E , F} (∈ℒ-,eps-l x x₁) = null, (to x) (to x₁)
    to {E , F} (∈ℒ-,eps-r x x₁) = null, (to x) (to x₁)
    to {E *} x = null*

    from : ∀ {E} →  Nullable E → ε ∈ℒ E
    from null⟨ε⟩ = ∈ℒ[]
    from (null+l x) = ∈ℒ+l (from x)
    from (null+r x) = ∈ℒ+r (from x)
    from (null, x y) = ∈ℒ-,eps-l (from x) (from y)
    from null* = ∈ℒ*-0

theorem2 : ∀ {a}{v}{F}
  →  v ∈ℒ(F [ a ]) ⇔ (a ∷ v) ∈ℒ(F)
theorem2  = record { to = to ; from = from }
  where
    to : ∀ {a}{v}{E} → v ∈ℒ(E [ a ]) → (a ∷ v) ∈ℒ( E )
    to {a} {v} {Atom c} x with c ≟ a
    to {_} {[]} {Atom c} x | yes refl = ∈ℒc c

    to {a} {v} {E + F} (∈ℒ+l x) = ∈ℒ+l (to x)
    to {a} {v} {E + F} (∈ℒ+r x) = ∈ℒ+r (to x)

    to {a} {v} {E , F} x with isNullable E
    to {a} {_} {E , F} (∈ℒ+l (∈ℒ-,  x x₁)) | yes p = ∈ℒ-, (to x) x₁
    to {a} {[]} {E , F} (∈ℒ+l (∈ℒ-,eps-l x x₁)) | yes p = ∈ℒ-,eps-r (to x) x₁
    to {a} {x₂ ∷ v} {E , F} (∈ℒ+l (∈ℒ-,eps-l x x₁)) | yes p = ∈ℒ-, (to x) x₁
    to {a} {v} {E , F} (∈ℒ+l (∈ℒ-,eps-r x x₁)) | yes p = ∈ℒ-,eps-r (to x) x₁

    to {a} {[]} {E , F} (∈ℒ+r  x) | yes p = ∈ℒ-,eps-l ((_⇔_.from theorem1) p) (to x)
    to {a} {v ∷ vs} {E , F} (∈ℒ+r  x) | yes p = ∈ℒ-,eps-l ((_⇔_.from theorem1) p) (to  x)

    to {a} {_} {E , F} (∈ℒ-, x y) | no ¬p = ∈ℒ-, (to  x) y
    to {a} {[]} {E , F} (∈ℒ-,eps-l x x₁) | no ¬p = ∈ℒ-,eps-r (to x) x₁
    to {a} {x₂ ∷ v} {E , F} (∈ℒ-,eps-l x x₁) | no ¬p = ∈ℒ-, (to  x) x₁
    to {a} {v} {E , F} (∈ℒ-,eps-r x x₁) | no ¬p = ∈ℒ-,eps-r (to x) x₁

    to {a} {v} {E *} (∈ℒ-, {t} {u} x y) = ∈ℒ*-+ (to x) y
    to {a} {v} {E *} (∈ℒ-,eps-l x x₁) = ∈ℒ*-+ (to x) x₁
    to {a} {v} {E *} (∈ℒ-,eps-r x x₁) = subst (_∈ℒ(E *)) (++-idʳ (a ∷ v)) (∈ℒ*-+ (to x) x₁)

    from : ∀ {a}{v}{F} → (a ∷ v) ∈ℒ F → v ∈ℒ F [ a ]
    from {_} {_} {Atom c} (∈ℒc .c) with c ≟ c
    from {_} {_} {Atom c} (∈ℒc .c) | yes p = ∈ℒ[]
    from {_} {_} {Atom c} (∈ℒc .c) | no ¬p = ⊥-elim (¬p refl)

    from {a} {v} {F + G} (∈ℒ+l x) = ∈ℒ+l (from x)
    from {a} {v} {F + G} (∈ℒ+r x) = ∈ℒ+r (from x)

    from {a} {v} {F , G} x with isNullable F
    from {a} {_} {F , G} (∈ℒ-, {a} {b} {[]} {t} x y) | yes p = ∈ℒ+l (∈ℒ-,eps-l (from x) y)
    from {a} {_} {F , G} (∈ℒ-, {a} {b} {x₁ ∷ s} {t} x y) | yes p = ∈ℒ+l (∈ℒ-, (from x) y)
    from {a} {v} {F , G} (∈ℒ-,eps-l x y) | yes p = ∈ℒ+r (from y)
    from {a} {v} {F , G} (∈ℒ-,eps-r x y) | yes p = ∈ℒ+l (∈ℒ-,eps-r (from x) y)
    from {a} {_} {F , G} (∈ℒ-, {a} {b} {[]} {t} x y) | no ¬p = ∈ℒ-,eps-l (from x) y
    from {a} {_} {F , G} (∈ℒ-, {a} {b} {x₁ ∷ s} {t} x y) | no ¬p = ∈ℒ-, (from x) y
    from {a} {v} {F , G} (∈ℒ-,eps-l x y) | no ¬p = ⊥-elim (¬p ((_⇔_.to theorem1) x))
    from {a} {v} {F , G} (∈ℒ-,eps-r x y) | no ¬p = ∈ℒ-,eps-r (from x) y

    from {a} {v} {F *} x with split-* x
    from {a} {v} {F *} x | inj₁ y = ∈ℒ-,eps-r (from y) ∈ℒ*-0
    from {a} {_} {F *} x | inj₂ ⟨ fst , ⟨ [] , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩  =
      subst (_∈ℒ(F [ a ] , F *)) (sym (++-idʳ fst)) (∈ℒ-,eps-r (from e) f)
    from {a} {_} {F *} x | inj₂ ⟨ [] , ⟨ z ∷ zs , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩ = ∈ℒ-,eps-l (from e) f
    from {a} {_} {F *} x | inj₂ ⟨ y ∷ ys , ⟨ z ∷ zs , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩ = ∈ℒ-, (from e) f

theorem3 : ∀ {v} {F}
  → v ∈ℒ(F) ⇔ Nullable (foldl (λ a E → E [ a ]) F v)
theorem3 = record { to = to ; from = from }
  where
    to : ∀ {v} {F} → v ∈ℒ(F) → Nullable (foldl (λ a E → E [ a ]) F v)
    to {[]} {F} x = _⇔_.to theorem1 x
    to {v ∷ vs} {F} x = to (_⇔_.from theorem2 x)

    from : ∀ {v} {F} → Nullable (foldl (λ a E → E [ a ]) F v) → v ∈ℒ F
    from {[]} {F} x = _⇔_.from theorem1 x
    from {v ∷ vs} {F} x = _⇔_.to theorem2 (from {vs} {F [ v ]} x)


--

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
  ε-seq : ∀ {E F}
    → ε ∈ℒ(E , F)
      ------------------
    → ε ∈ℒ(E) × ε ∈ℒ(F)
  split-seq : ∀ {a}{s} {E F}
    → (a ∷ s) ∈ℒ(E , F)
      ---------------------------------------------------------------------
    → ∃[ t ] (∃[ u ] ( (a ∷ s) ≡ (a ∷ t) ++ u × (a ∷ t) ∈ℒ(E) × u ∈ℒ(F) ))
  split-* : ∀ {a}{s}{E}
    → (a ∷ s) ∈ℒ(E *)
      ---------------
    → (a ∷ s) ∈ℒ(E) ⊎ (∃[ t ] (∃[ u ] ( (a ∷ s) ≡ (a ∷ t) ++ u × (a ∷ t) ∈ℒ(E) × u ∈ℒ(E *) )))


theorem1 : ∀ {E : RegExp}
  → ε ∈ℒ(E) ⇔ Nullable E
theorem1 = record { to = to ; from = from }
  where
    to : ∀ {E} → ε ∈ℒ E → Nullable E
    to {⟨ε⟩} x = null⟨ε⟩
    to {E + F} (∈ℒ+l x) = null+l (to x)
    to {E + F} (∈ℒ+r x) = null+r (to x)
    to {E , F} x with ε-seq x
    to {E , F} x | ⟨ fst , snd ⟩ = null, (to fst) (to snd)
    to {E *} x = null*

    from : ∀ {E} →  Nullable E → ε ∈ℒ E
    from null⟨ε⟩ = ∈ℒ[]
    from (null+l x) = ∈ℒ+l (from x)
    from (null+r x) = ∈ℒ+r (from x)
    from (null, x y) = ∈ℒ-, (from x) (from y)
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

    to {a} {v} {E , F} x with  isNullable E
    to {a} {v} {E , F} (∈ℒ+l x) | yes p with (_⇔_.from theorem1) p
    to {a} {v} {E , F} (∈ℒ+l (∈ℒ-, {s} {t} x y)) | yes p | u  = ∈ℒ-, (to {a} {s} {E} x) y
    to {a} {v} {E , F} (∈ℒ+r x) | yes p = ∈ℒ-, ((_⇔_.from theorem1) p) (to {a} {v} {F} x)
    to {a} {v} {E , F} (∈ℒ-, {s} {t} x y) | no ¬p  =  ∈ℒ-, (to {a} {s} {E} x) y

    to {a} {v} {E *} (∈ℒ-, {t} {u} x y) = ∈ℒ*-+ (to x) y


    from : ∀ {a}{v}{F} → (a ∷ v) ∈ℒ F → v ∈ℒ F [ a ]
    from {_} {_} {Atom c} (∈ℒc .c) with c ≟ c
    from {_} {_} {Atom c} (∈ℒc .c) | yes p = ∈ℒ[]
    from {_} {_} {Atom c} (∈ℒc .c) | no ¬p = ⊥-elim (¬p refl)

    from {a} {v} {F + G} (∈ℒ+l x) = ∈ℒ+l (from x)
    from {a} {v} {F + G} (∈ℒ+r x) = ∈ℒ+r (from x)

    from {a} {v} {F , G} x with isNullable F | split-seq x
    from {a} {v} {F , G} x | yes p | ⟨ _ , ⟨ _ , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩ = ∈ℒ+l (∈ℒ-, (from e) f)
    from {a} {v} {F , G} x | no ¬p | ⟨ _ , ⟨ _ , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩ = ∈ℒ-, (from e) f

    from {a} {v} {F *} x with  split-* x
    from {a} {v} {F *} x | inj₁ y = subst (_∈ℒ(F [ a ] , F *)) (++-idʳ v) (∈ℒ-, (from y) ∈ℒ*-0)
    from {a} {v} {F *} x | inj₂ ⟨ b , ⟨ c , ⟨ refl , ⟨ e , f ⟩ ⟩ ⟩ ⟩ = ∈ℒ-, (from e) f

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

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence

module Brzozowski (Σ : Set) (_≟_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import Regexp Σ
open import String Σ using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)

data Nullable : RegExp → Set where
  null⟨ε⟩ : Nullable ⟨ε⟩
  null+l : ∀{F G} → Nullable F → Nullable (F + G)
  null+r : ∀{F G} → Nullable G → Nullable (F + G)
  null· : ∀{F G} → Nullable F → Nullable G → Nullable (F · G)
  null* : ∀{F} → Nullable (F *)

⊥-elim-⊎ : ∀ {A B : Set} → ¬ A → ¬ B → A ⊎ B → ⊥
⊥-elim-⊎ a b (inj₁ x) = a x
⊥-elim-⊎ a b (inj₂ y) = b y

⊥-elim-× : ∀ {A B : Set} → ¬ A ⊎ ¬ B → A × B → ⊥
⊥-elim-× (inj₁ x) (fst , snd) = x fst
⊥-elim-× (inj₂ y) (fst , snd) = y snd

+-nullable-⊎ : ∀ {E F} → Nullable (E + F) → Nullable E ⊎ Nullable F
+-nullable-⊎ (null+l a) = inj₁ a
+-nullable-⊎ (null+r a) = inj₂ a

·-nullable-× : ∀ {E F} → Nullable (E · F) → Nullable E × Nullable F
·-nullable-× (null· x y) = x , y

isNullable : (E : RegExp) → Dec (Nullable E)
isNullable ⟨⟩ = no (λ ())
isNullable ⟨ε⟩ = yes null⟨ε⟩
isNullable (Atom c) = no (λ ())
isNullable (r + s) with isNullable r | isNullable s
... | yes p | yes q = yes (null+l p)
... | yes p | no ¬q = yes (null+l p)
... | no ¬p | yes q = yes (null+r q)
... | no ¬p | no ¬q = no λ x → ⊥-elim-⊎ ¬p ¬q (+-nullable-⊎ x)
isNullable (r · s)  with isNullable r | isNullable s
... | yes p | yes q = yes (null· p q)
... | _     | no ¬q = no λ x → ⊥-elim-× (inj₂ ¬q) (·-nullable-× x)
... | no ¬p | _     = no λ x → ⊥-elim-× (inj₁ ¬p) (·-nullable-× x)
isNullable (r *) = yes null*

_[_] : RegExp → Σ → RegExp
⟨⟩ [ a ] = ⟨⟩
⟨ε⟩ [ a ] = ⟨⟩
(Atom b)[ a ] with b ≟ a
... | yes p = ⟨ε⟩
... | no ¬p = ⟨⟩
(F + G)[ a ] = F [ a ] + G [ a ]
(F · G)[ a ] with isNullable F
... | yes p = F [ a ] · G + G [ a ]
... | no ¬p = F [ a ] · G
(F *)[ a ] = F [ a ] · F *

split-seq : ∀{s E F} → s ∈ (E · F) → ∃[ u ] ∃[ v ] ((s ≡ u ++ v) × (u ∈ E) × (v ∈ F))
split-seq (in-· p q) = _ , _ , refl , p , q

lemma4 : ∀(u v : String) → [] ≡ u ++ v → u ≡ [] × v ≡ []
lemma4 [] [] refl = refl , refl

ε-seq : ∀{E F} → ε ∈ (E · F) → ε ∈ E × ε ∈ F
ε-seq p with split-seq p
... | u , v , eq , p1 , p2 with lemma4 u v eq
... | eq1 , eq2 rewrite eq1 | eq2 = p1 , p2

split-* : ∀{E s}
  → s ∈ (E *)
  → s ≢ ε
  → ∃[ u ] ∃[ v ] (u ≢ ε × s ≡ u ++ v × u ∈ E × v ∈ (E *))
split-* in-*1 q = ⊥-elim (q refl)
split-* (in-*2 {[]} p q) neps = split-* q neps
split-* (in-*2 {x ∷ s} {t} p q) _ = x ∷ s , t , (λ ()) , refl , p , q

theorem1 : ∀{E : RegExp}
  → ε ∈(E) ⇔ Nullable E
theorem1 = record { to = to ; from = from }
  where
    to : ∀{E} → ε ∈ E → Nullable E
    to {⟨ε⟩} _          = null⟨ε⟩
    to {E + F} (in+l x) = null+l (to x)
    to {E + F} (in+r x) = null+r (to x)
    to {E · F} x with ε-seq x
    ... | ε∈E , ε∈F     = null· (to ε∈E) (to ε∈F)
    to {E *} _          = null*

    from : ∀{E} → Nullable E → ε ∈ E
    from null⟨ε⟩     = in-ε
    from (null+l x)  = in+l (from x)
    from (null+r x)  = in+r (from x)
    from (null· x y) = in-· (from x) (from y)
    from null*       = in-*1

theorem2 : ∀{a : Σ} {v : String} {F : RegExp}
  → v ∈(F [ a ]) ⇔ (a ∷ v) ∈(F)
theorem2 = record { to = to ; from = from }
  where
    to : ∀{a v E} → v ∈(E [ a ]) → (a ∷ v) ∈( E )
    to {a} {v} {Atom c} x with c ≟ a
    to {_} {[]} {Atom c} x | yes refl = in-c c
    to {E = F + G} (in+l x) = in+l (to x)
    to {E = F + G} (in+r x) = in+r (to x)
    to {E = F · G} x with isNullable F
    to {E = F · G} (in+l (in-· x y)) | yes p = in-· (to x) y
    to {E = F · G} (in+r x)          | yes p = in-· (_⇔_.from theorem1 p) (to x)
    to {E = F · G} (in-· x y)        | no ¬p = in-· (to x) y
    to {E = F *} (in-· x y) = in-*2 (to x) y

    from : ∀ {a}{v}{E} → (a ∷ v) ∈ E → v ∈ E [ a ]
    from {_} {_} {Atom c} (in-c .c) with c ≟ c
    ... | yes p = in-ε
    ... | no ¬p = ⊥-elim (¬p refl)
    from {E = F + G} (in+l x) = in+l (from x)
    from {E = F + G} (in+r x) = in+r (from x)
    from {E = F · G} x with isNullable F | split-seq x
    ... | yes p | [] , av , refl , _ , av∈G = in+r (from av∈G)
    ... | yes p | a ∷ u , t , refl , au∈F , t∈G = in+l (in-· (from au∈F) t∈G)
    ... | no ¬p | [] , _ , refl , ε∈F , _ = ⊥-elim (¬p (_⇔_.to theorem1 ε∈F))
    ... | no ¬p | a ∷ u , t , refl , au∈F , t∈G = in-· (from au∈F) t∈G
    from {E = F *} x with split-* x (λ ())
    ... | [] , _ , ¬p , _ , _ , _ = ⊥-elim (¬p refl)
    ... | a ∷ t , v , _ , refl , at∈E , v∈E* = in-· (from at∈E) v∈E*

theorem3 : ∀ {v : String} {F : RegExp}
  → v ∈(F) ⇔ Nullable (foldl _[_] F v)
theorem3 = record { to = to ; from = from }
  where
    to : ∀ {v} {F} → v ∈(F) → Nullable (foldl _[_] F v)
    to {[]} x     = _⇔_.to theorem1 x
    to {v ∷ vs} x = to (_⇔_.from theorem2 x)

    from : ∀ {v} {F} → Nullable (foldl _[_] F v) → v ∈ F
    from {[]} x     = _⇔_.from theorem1 x
    from {v ∷ vs} x = _⇔_.to theorem2 (from x)

_∈?_ : (v : String) → (F : RegExp) → Dec (v ∈ F)
v ∈? F with isNullable (foldl _[_] F v)
... | yes p = yes (_⇔_.from theorem3 p)
... | no ¬p = no (λ z → ¬p (_⇔_.to theorem3 z))

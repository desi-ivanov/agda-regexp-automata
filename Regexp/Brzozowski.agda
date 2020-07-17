import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable using (map; ⌊_⌋)

open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence

module Brzozowski (Σ : Set) (_≟_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import Regexp Σ
open import String Σ using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)

open import Data.Bool using (if_then_else_)

data Nullable : RegExp → Set where
  null⟨ε⟩ : Nullable ⟨ε⟩
  null+l : ∀{F G} → Nullable F → Nullable (F + G)
  null+r : ∀{F G} → Nullable G → Nullable (F + G)
  null· : ∀{F G} → Nullable F → Nullable G → Nullable (F · G)
  null* : ∀{F} → Nullable (F *)

Nullable? : (E : RegExp) → Dec (Nullable E)
Nullable? ⟨⟩ = no (λ ())
Nullable? ⟨ε⟩ = yes null⟨ε⟩
Nullable? (Atom c) = no (λ ())
Nullable? (r + s) with Nullable? r | Nullable? s
... | yes p | _     = yes (null+l p)
... | _     | yes q = yes (null+r q)
... | no ¬p | no ¬q = no λ{ (null+l p) → ⊥-elim (¬p p)
                          ; (null+r q) → ⊥-elim (¬q q) }
Nullable? (r · s)  with Nullable? r | Nullable? s
... | yes p | yes q = yes (null· p q)
... | _     | no ¬q = no λ{ (null· _ q) → ⊥-elim (¬q q) }
... | no ¬p | _     = no λ{ (null· p _) → ⊥-elim (¬p p) }
Nullable? (r *) = yes null*

_[_] : RegExp → Σ → RegExp
⟨⟩ [ a ] = ⟨⟩
⟨ε⟩ [ a ] = ⟨⟩
(Atom b)[ a ] = if ⌊ b ≟ a ⌋
                  then ⟨ε⟩
                  else ⟨⟩
(F + G)[ a ] = F [ a ] + G [ a ]
(F · G)[ a ] = if ⌊ Nullable? F ⌋
                  then F [ a ] · G + G [ a ]
                  else F [ a ] · G
(F *)[ a ] = F [ a ] · F *

split-seq : ∀{s E F}
  → s ∈ (E · F)
  → ∃[ u ] ∃[ v ] ((s ≡ u ++ v) × (u ∈ E) × (v ∈ F))
split-seq (in-· p q) = _ , _ , refl , p , q

ε-seq : ∀{E F} → ε ∈ (E · F) → ε ∈ E × ε ∈ F
ε-seq p with split-seq p
... | [] , [] , refl , p1 , p2 = p1 , p2

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

theorem2 : ∀{a : Σ} {v : String} {E : RegExp}
  → v ∈(E [ a ]) ⇔ (a ∷ v) ∈(E)
theorem2 = record { to = to ; from = from }
  where
    to : ∀{a v E} → v ∈(E [ a ]) → (a ∷ v) ∈( E )
    to {a} {v} {Atom c} x with c ≟ a
    to {_} {[]} {Atom c} x | yes refl = in-c c
    to {E = F + G} (in+l x) = in+l (to x)
    to {E = F + G} (in+r x) = in+r (to x)
    to {E = F · G} x with Nullable? F
    to {E = F · G} (in+l (in-· x y)) | yes p
      = in-· (to x) y
    to {E = F · G} (in+r x)          | yes p
      = in-· (_⇔_.from theorem1 p) (to x)
    to {E = F · G} (in-· x y)        | no ¬p
      = in-· (to x) y
    to {E = F *} (in-· x y) = in-*2 (to x) y

    from : ∀ {a}{v}{E} → (a ∷ v) ∈ E → v ∈ E [ a ]
    from {_} {_} {Atom c} (in-c .c) with c ≟ c
    ... | yes p = in-ε
    ... | no ¬p = ⊥-elim (¬p refl)
    from {E = F + G} (in+l x) = in+l (from x)
    from {E = F + G} (in+r x) = in+r (from x)
    from {E = F · G} x with Nullable? F | split-seq x
    ... | yes p | [] , av , refl , _ , av∈G
      = in+r (from av∈G)
    ... | yes p | a ∷ u , t , refl , au∈F , t∈G
      = in+l (in-· (from au∈F) t∈G)
    ... | no ¬p | [] , _ , refl , ε∈F , _
      = ⊥-elim (¬p (_⇔_.to theorem1 ε∈F))
    ... | no ¬p | a ∷ u , t , refl , au∈F , t∈G
      = in-· (from au∈F) t∈G
    from {E = F *} x with split-* x (λ ())
    ... | [] , _ , ¬p , _ , _ , _ = ⊥-elim (¬p refl)
    ... | a ∷ t , v , _ , refl , at∈E , v∈E*
      = in-· (from at∈E) v∈E*

Iff⇒ = _⇔_.to
Iff⇐ = _⇔_.from

theorem3 : ∀ {v F} → v ∈(F) ⇔ Nullable (foldl _[_] F v)
theorem3 = record { to = to ; from = from }
    where
      to : ∀ {v F} → v ∈(F) → Nullable (foldl _[_] F v)
      to {[]}     x = Iff⇒ theorem1 x
      to {v ∷ vs} x = to (Iff⇐ theorem2 x)

      from : ∀ {v F} → Nullable (foldl _[_] F v) → v ∈ F
      from {[]}     x = Iff⇐ theorem1 x
      from {v ∷ vs} x = Iff⇒ theorem2 (from x)

_∈?_ : (v : String) → (F : RegExp) → Dec (v ∈ F)
v ∈? F with Nullable? (foldl _[_] F v)
... | yes p = yes (Iff⇐ theorem3 p)
... | no ¬p = no (λ z → ¬p (Iff⇒ theorem3 z))

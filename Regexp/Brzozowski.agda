module Brzozowski where
open import Regexp
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Char as Char
open import String using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)

open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data Nullable : RegExp → Set where
  null⟨ε⟩ : Nullable ⟨ε⟩
  null+l : ∀{F G} → Nullable F → Nullable (F + G)
  null+r : ∀{F G} → Nullable G → Nullable (F + G)
  null, : ∀{F G} → Nullable F → Nullable G → Nullable (F · G)
  null* : ∀{F} → Nullable (F *)

⊥-elim-sum : ∀ {A B : Set} → ¬ A → ¬ B → A ⊎ B → ⊥
⊥-elim-sum a b (inj₁ x) = a x
⊥-elim-sum a b (inj₂ y) = b y

⊥-elim-product : ∀ {A B : Set} → ¬ A ⊎ ¬ B → A × B → ⊥
⊥-elim-product (inj₁ x) (fst , snd) = x fst
⊥-elim-product (inj₂ y) (fst , snd) = y snd

sumnullable : ∀ {E F} → Nullable (E + F) → Nullable E ⊎ Nullable F
sumnullable (null+l a) = inj₁ a
sumnullable (null+r a) = inj₂ a

seqnullable : ∀ {E F} → Nullable (E · F) → Nullable E × Nullable F
seqnullable (null, x y) = x , y

isNullable : (E : RegExp) → Dec (Nullable E)
isNullable ⟨⟩ = no (λ ())
isNullable ⟨ε⟩ = yes null⟨ε⟩
isNullable (Atom c) = no (λ ())
isNullable (r + s) with isNullable r | isNullable s
isNullable (r + s) | yes p | yes q = yes (null+l p)
isNullable (r + s) | yes p | no ¬q = yes (null+l p)
isNullable (r + s) | no ¬p | yes q = yes (null+r q)
isNullable (r + s) | no ¬p | no ¬q = no (λ x → ⊥-elim-sum ¬p ¬q (sumnullable x))
isNullable (r · s)  with isNullable r | isNullable s
isNullable (r · s) | yes p | yes q = yes (null, p q)
isNullable (r · s) | yes p | no ¬q = no λ x → ⊥-elim-product (inj₂ ¬q) (seqnullable x)
isNullable (r · s) | no ¬p | yes q = no λ x → ⊥-elim-product (inj₁ ¬p) (seqnullable x)
isNullable (r · s) | no ¬p | no ¬q = no λ x → ⊥-elim-product (inj₁ ¬p) (seqnullable x)
isNullable (r *) = yes null*

der : RegExp → Char → RegExp
der ⟨⟩ a = ⟨⟩
der ⟨ε⟩ a = ⟨⟩
der (Atom b) a with b ≟ a
... | yes p = ⟨ε⟩
... | no ¬p = ⟨⟩
der (F + G) a = der F a + der G a
der (F · G) a with isNullable F
... | yes p = (der F a) · G + der G a
... | no ¬p = (der F a) · G
der (F *) a = (der F a) · F *

lemma3 : ∀{s E F} -> s ∈ (E · F) -> ∃[ u ] ∃[ v ] ((s ≡ u ++ v) × (u ∈ E) × (v ∈ F))
lemma3 (in-· p q) = _ , _ , refl , p , q

lemma4 : ∀(u v : String) -> [] ≡ u ++ v -> u ≡ [] × v ≡ []
lemma4 [] [] refl = refl , refl

ε-seq : ∀{E F} -> ε ∈ (E · F) -> ε ∈ E × ε ∈ F
ε-seq p with lemma3 p
... | u , v , eq , p1 , p2 with lemma4 u v eq
... | eq1 , eq2 rewrite eq1 | eq2 = p1 , p2

split-seq : ∀ {a s E F}
  → (a ∷ s) ∈(E · F)
  → ∃[ t ] (∃[ u ] ( (a ∷ s) ≡ (a ∷ t) ++ u × (a ∷ t) ∈(E) × u ∈(F) )) ⊎ (ε ∈(E) × (a ∷ s) ∈(F))
split-seq {a} {s} {E} {F} x with lemma3 {a ∷ s} {E} {F} x
... | [] , a ∷ s , refl , p1 , p2    = inj₂ (p1 , p2)
... | a ∷ u , [] , refl , p1 , p2    = inj₁ (u , [] , refl , p1 , p2)
... | a ∷ u , b ∷ v , refl , p1 , p2 = inj₁ (u , b ∷ v , refl , p1 , p2)

split-* : ∀{E s}
  -> s ∈ (E *)
  -> ¬ (s ≡ [])
  -> ∃[ u ] ∃[ v ] (¬ (u ≡ []) × s ≡ u ++ v × u ∈ E × v ∈ (E *))
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
    ... | ε∈E , ε∈F     = null, (to ε∈E) (to ε∈F)
    to {E *} _          = null*

    from : ∀{E} → Nullable E → ε ∈ E
    from null⟨ε⟩     = in-ε
    from (null+l x)  = in+l (from x)
    from (null+r x)  = in+r (from x)
    from (null, x y) = in-· (from x) (from y)
    from null*       = in-*1

theorem2 : ∀{a v F}
  → v ∈(der F a) ⇔ (a ∷ v) ∈(F)
theorem2 = record { to = to ; from = from }
  where
    to : ∀{a v E} → v ∈(der E a) → (a ∷ v) ∈( E )
    to {a} {v} {Atom c} x with c ≟ a
    to {_} {[]} {Atom c} x | yes refl = in-c c
    to {a} {v} {E + F} (in+l x) = in+l (to x)
    to {a} {v} {E + F} (in+r x) = in+r (to x)
    to {a} {v} {E · F} x with isNullable E
    to {a} {v} {E · F} (in+l (in-· x y)) | yes p = in-· (to x) y
    to {a} {v} {E · F} (in+r x)          | yes p = in-· (_⇔_.from theorem1 p) (to x)
    to {a} {v} {E · F} (in-· x y)        | no ¬p = in-· (to x) y
    to {a} {_} {E *} (in-· x y) = in-*2 (to x) y

    from : ∀ {a}{v}{F} → (a ∷ v) ∈ F → v ∈ der F a
    from {_} {_} {Atom c} (in-c .c) with c ≟ c
    ... | yes p = in-ε
    ... | no ¬p = ⊥-elim (¬p refl)
    from {a} {v} {F + G} (in+l x) = in+l (from x)
    from {a} {v} {F + G} (in+r x) = in+r (from x)
    from {a} {v} {F · G} x with isNullable F | split-seq x
    ... | yes p | inj₁ (t , u , refl , t∈F , u∈G) = in+l (in-· (from t∈F) u∈G)
    ... | yes p | inj₂ (ε∈F , v∈G)                = in+r (from v∈G)
    ... | no ¬p | inj₁ (t , u , refl , t∈F , u∈G) = in-· (from t∈F) u∈G
    ... | no ¬p | inj₂ (ε∈F , v∈G)                = ⊥-elim (¬p (_⇔_.to theorem1 ε∈F))
    from {_} {_} {F *} x with split-* x (λ ())
    ... | [] , a ∷ v , ¬p , refl , _ , _             = ⊥-elim (¬p refl)
    ... | a ∷ v , [] , ¬p , refl , av∈E , ε∈E*       = in-· (from av∈E) ε∈E*
    ... | a ∷ v , t ∷ ts , ¬p , refl , av∈E , tts∈E* = in-· (from av∈E) tts∈E*

theorem3 : ∀ {v F}
  → v ∈(F) ⇔ Nullable (foldl (λ a E → der E a) F v)
theorem3 = record { to = to ; from = from }
  where
    to : ∀ {v} {F} → v ∈(F) → Nullable (foldl (λ a E → der E a) F v)
    to {[]} {F} x     = _⇔_.to theorem1 x
    to {v ∷ vs} {F} x = to (_⇔_.from theorem2 x)

    from : ∀ {v} {F} → Nullable (foldl (λ a E → der E a) F v) → v ∈ F
    from {[]} x     = _⇔_.from theorem1 x
    from {v ∷ vs} x = _⇔_.to theorem2 (from x)

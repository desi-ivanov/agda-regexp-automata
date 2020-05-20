open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat as ℕ using (ℕ; zero)
open import Data.Fin using (Fin; 0F; 1F; raise; inject+) renaming (suc to fsuc; zero to fzero)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.Any as Any using (Any; any)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List using (List; []; _∷_; [_]; map; length)

module LTS (Σ : Set) (_≟_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import Regexp Σ
open import String Σ using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ)
open import Brzozowski Σ _≟_
  using (isNullable; Nullable; ε-seq; split-seq; split-*)
  renaming (theorem1 to BrzozowskiT1)
open import RegExpSet Σ _≟_

data LTS : RegExp → Σ → RegExp → Set where
  LTS1 : (a : Σ) → LTS (Atom a) a ⟨ε⟩
  LTS2 : ∀{a E F E'}
    → LTS E a E'
    → LTS (E + F) a E'
  LTS3 : ∀{a E F F'}
    → LTS F a F'
    → LTS (E + F) a F'
  LTS4 : ∀ {a E F E'}
    → LTS E a E'
    → LTS (E · F) a (E' · F)
  LTS5 : ∀{a E F F'}
    → Nullable E
    → LTS F a F'
    → LTS (E · F) a F'
  LTS6 : ∀{a E E'}
    → LTS E a E'
    → LTS (E *) a (E' · E *)

data LTSw : RegExp → String → RegExp → Set where
  LTSw[] : (E : RegExp) → LTSw E ε E
  LTSw:: : ∀{E F G x xs} → LTS E x F → LTSw F xs G → LTSw E (x ∷ xs) G

open Nullable

lemma4 : ∀{a : Σ}{w : String}{E : RegExp}
  → ∃[ E' ] (LTS E a E' × w ∈ E') ⇔ (a ∷ w) ∈ E
lemma4 = record { to = to ; from = from }
  where
    to : ∀{a w E} → ∃[ E' ] (LTS E a E' × w ∈ E') → (a ∷ w) ∈ E
    to {.c} {[]} {Atom c} (⟨ε⟩ , (LTS1 .c , r)) = in-c c
    to {.c} {x ∷ xs} {Atom c}  (⟨ε⟩ , (LTS1 .c , ()))

    to {a} {w} {E + E₁} (E' , (LTS2 l , r)) = in+l (to (E' , l , r))
    to {a} {w} {E + E₁} (E' , (LTS3 l , r)) = in+r (to (E' , l , r))

    to {a} {[]} {E · E₁} (E' , (LTS4 l , r)) with ε-seq r
    to {a} {[]} {E · E₁} (.(_ · E₁) , LTS4 {_}{_}{_}{E''} l , r) | fst , snd = in-· (to (E'' , l , fst )) snd
    to {a} {x ∷ w} {E · E₁} (E' , (LTS4 l , r)) with split-seq r
    to {a} {x ∷ .(d ++ e)} {E · E₁} (E' , (LTS4 {_}{_}{_}{E''} l , r)) | inj₁ (d , e , refl , g , h) = in-· (to (E'' , l , g)) h
    to {a} {x ∷ w} {E · E₁} (E' , (LTS4 {_}{_}{_}{E''} l , r)) | inj₂ (fst , snd) = in-· (to (E'' , l , fst)) snd
    to {a} {w} {E · E₁} (E' , (LTS5 {_}{_}{_}{E''} n l , r)) = in-· (_⇔_.from BrzozowskiT1 n) (to (E' , l , r))

    to {a} {[]} {E *} (E' , (LTS6 l , r)) with ε-seq r
    to {a} {[]} {E *} (E' , (LTS6 {_}{_}{E''} l , r)) | fst , snd = in-*2 (to (E'' , l , fst)) snd
    to {a} {x ∷ w} {E *} (E' , (LTS6 {_}{_}{E''} l , r)) with split-seq r
    ... | inj₁ (d , e , refl , g , h) = in-*2 (to (E'' , l , g)) h
    ... | inj₂ (fst , snd) = in-*2 (to (E'' , l , fst)) snd

    from : ∀{a w E} → (a ∷ w) ∈ E → ∃[ E' ] (LTS E a E' × w ∈ E')
    from {.c} {.[]} {Atom c} (in-c .c) = ⟨ε⟩ , LTS1 c , in-ε

    from {a} {w} {E + E₁} (in+l d) with from d
    ... | E' , lts , win = E' , LTS2 lts , win

    from {a} {w} {E + E₁} (in+r d) with from d
    ... | E' , lts , win = E' , LTS3 lts , win

    from {a} {w} {E · E₁} d with split-seq d
    from {a} {_} {E · E₁} d | inj₁ (c , e , refl , g , h) with from g
    from {a} {_} {E · E₁} d | inj₁ (c , e , refl , g , h) | fst , snd , trd = fst · E₁ , LTS4 snd , in-· trd h
    from {a} {w} {E · E₁} d | inj₂ (c , e) with from e
    ... | fst , snd , trd = fst , LTS5 (_⇔_.to BrzozowskiT1 c) snd , trd

    from {a} {w} {E *} d with split-* d λ ()
    from {a} {w} {E *} d | [] , e , f , g , h , i = ⊥-elim (f refl)
    from {a} {w} {E *} d | x ∷ c , [] , f , g , h , i with from h
    from {_} {_} {E *} d | x ∷ c , [] , f , refl , h , i | fst , snd , trd = fst · E * , LTS6 snd , in-· trd i
    from {_} {_} {E *} d | x ∷ c , x₁ ∷ e , f , refl , h , i with from h
    ... | fst , snd , trd  = fst · E * , LTS6 snd , in-· trd i


theorem1 : ∀{E : RegExp} {w : String}
  → w ∈ (E) ⇔ ∃[ E' ] (LTSw E w E' × Nullable E' )
theorem1 = record { to = to ; from = from }
  where
    to : ∀{w} {E} → w ∈ E → ∃[ E' ] (LTSw E w E' × Nullable E')
    to {[]} {E} d = E , LTSw[] E , (_⇔_.to BrzozowskiT1 d)
    to {x ∷ w} {E} d with _⇔_.from (lemma4 {x}{w}{E}) d
    ... | _ , snd , trd with to trd
    ... | a , b , c  = a , LTSw:: snd b , c

    from : ∀{w} {E} → ∃[ E' ] (LTSw E w E' × Nullable E') → w ∈ (E)
    from {[]} {.E'} (E' , LTSw[] .E' , nl) = _⇔_.from BrzozowskiT1 nl
    from {x ∷ w} {E} (E' , LTSw:: {_}{F} dl dr , nl) = _⇔_.to (lemma4 {x}{w}{E }) (F , dl , (from (E' , dr ,  nl)))


D : RegExp → List RegExp
D ⟨⟩ = []
D ⟨ε⟩ = ⟨ε⟩ ∷ []
D (Atom c) = (Atom c) ∷ ⟨ε⟩ ∷ []
D (E + F) = D E ∪ (D F)
D (E · F) with any (isNullable) (D E)
D (E · F) | yes p = map (_· F) (D E) ∪ (D F)
D (E · F) | no ¬p = map (_· F) (D E)
D (E *) = [ E * ] ∪ (map (_· E *) (D E))
open Any.Any
open All.All

map-preserves-∈ : ∀{F x xs} → x ∈ˡ xs → (x · F) ∈ˡ (map (_· F) xs)
map-preserves-∈ {F} (here px) = here (cong (λ z → z · F) px)
map-preserves-∈ {F} (there px) = there (map-preserves-∈ px)

map-preserves-⊆ : ∀{F ss1 ss2} → ss1 ⊆ ss2 → map (_· F) ss1 ⊆ map (_· F) ss2
map-preserves-⊆ {F} [] = []
map-preserves-⊆ {F} (px ∷ p) = (map-preserves-∈ px) ∷ (map-preserves-⊆ p)


map-both-preserves-∈ : ∀{E F x ss} → (x · F) ∈ˡ (map (_· F) ss) → (x · E) ∈ˡ (map (_· E) ss)
map-both-preserves-∈ {E} {F} {.x₁} {x₁ ∷ ss} (here refl) = here refl
map-both-preserves-∈ {E} {F} {x} {x₁ ∷ ss} (there f) = there (map-both-preserves-∈ f)

map-both-preserves-⊆ : ∀{E F ss1 ss2} → (map (_· F) ss1) ⊆ map (_· F) ss2 → (map (_· E) ss1) ⊆ map (_· E) ss2
map-both-preserves-⊆ {_} {_} {[]} x = []
map-both-preserves-⊆ {_} {_} {s ∷ ss1} (px ∷ x) = (map-both-preserves-∈ px) ∷ map-both-preserves-⊆ x

module D-Properties where
  open Nullable
  star-nullable : ∀{E ss} → (E *) ∈ˡ ss → Any Nullable ss
  star-nullable (here refl) = here null*
  star-nullable (there ps) = there (star-nullable ps)

  D-preserves-nullable : ∀{E} → Nullable E → Any Nullable (D E)
  D-preserves-nullable null⟨ε⟩ = here null⟨ε⟩
  D-preserves-nullable (null+l nlbl) = ∪-preserves-Pˡ (D-preserves-nullable nlbl)
  D-preserves-nullable (null+r {E} nlbl) = ∪-preserves-Pʳ {D E} (D-preserves-nullable nlbl)
  D-preserves-nullable (null, {E} nlblL nlblR) with any isNullable (D E)
  D-preserves-nullable (null, {E} {F} nlblL nlblR) | yes p = ∪-preserves-Pʳ {map (_· F) (D E)} (D-preserves-nullable nlblR)
  D-preserves-nullable (null, nlblL nlblR) | no ¬p = ⊥-elim(¬p (D-preserves-nullable nlblL))
  D-preserves-nullable (null* {F}) with (F *) ∈? map (_· F *) (D F)
  D-preserves-nullable (null* {F}) | no ¬p = here null*
  D-preserves-nullable (null* {F}) | yes p = star-nullable p


Lemma2⊆ : ∀ {E F a} → (LTS E a F) → D F ⊆ D E
Lemma2⊆ (LTS1 a) = there (here refl) ∷ []
Lemma2⊆ (LTS2 {F = F} lts) = ∪-preserves-⊆ʳ (Lemma2⊆ lts) (D F)
Lemma2⊆ (LTS3 {E = E} lts) = ∪-preserves-⊆ˡ (Lemma2⊆ lts) (D E)
Lemma2⊆ (LTS4 {_} {E} {F} {E'} lts) with Lemma2⊆ lts
... | IH with any isNullable (D E) | any isNullable (D E')
... | yes p | no ¬p = ∪-preserves-⊆ʳ (map-preserves-⊆ IH) (D F)
... | no ¬p | no ¬p₁ = map-preserves-⊆ IH
... | yes p | yes p₁ = ∪-injects-∪⊆ʳ {map (_· F) (D E)} (∪-preserves-⊆ʳ (map-preserves-⊆ {F} IH) (D F))
... | no ¬p | yes p = contradiction p (⊆-preserves-¬P IH ¬p)
Lemma2⊆ (LTS5 {a}{E}{F}{E'} x lts) with Lemma2⊆ lts
... | IH with any isNullable (D E)
... | yes p = ∪-preserves-⊆ˡ IH (map (_· F) (D E))
... | no ¬p = ⊥-elim(¬p (D-Properties.D-preserves-nullable x))
Lemma2⊆ (LTS6 {a}{E}{E'} lts) with Lemma2⊆ lts
... | IH with any isNullable (D E')
... | yes p with (E *) ∈? map (_· E *) (D E)
... | yes p₁ = ∪-self-⊆ (map-both-preserves-⊆ {E *} (map-preserves-⊆ {E'} IH))
... | no ¬p  = ∪-self-⊆ (∷-preserves-⊆ (map-both-preserves-⊆ {E *} (map-preserves-⊆ {E'} IH)))
Lemma2⊆ (LTS6 {a}{E}{E'} lts) | IH | no ¬p with (E *) ∈? map (_· E *) (D E)
... | yes p = map-both-preserves-⊆ (map-preserves-⊆ {E'} IH)
... | no ¬p₁ = ∷-preserves-⊆ (map-both-preserves-⊆ (map-preserves-⊆ {E'} IH))

Lemma2∈ : ∀{E x F} → LTS E x F → F ∈ˡ D E
Lemma2∈ (LTS1 a) = there (here refl)
Lemma2∈ (LTS2 lts) = ∪-preserves-∈ˡ (Lemma2∈ lts)
Lemma2∈ (LTS3 {_}{E} lts) = ∪-preserves-∈ʳ {D E} (Lemma2∈ lts)
Lemma2∈ (LTS4 {_}{E} lts) with Lemma2∈ lts
... | IH  with any isNullable (D E)
Lemma2∈ (LTS4 {_} {E} lts) | IH | yes p = ∪-preserves-∈ˡ (map-preserves-∈  IH)
Lemma2∈ (LTS4 {_} {E} lts) | IH | no ¬p = map-preserves-∈  IH
Lemma2∈ (LTS5 {_} {E} x lts) with Lemma2∈ lts
... | IH with any isNullable (D E)
Lemma2∈ (LTS5 {_} {E} {F} x lts) | IH | yes p = ∪-preserves-∈ʳ {map (_· F) (D E)} IH
Lemma2∈ (LTS5 {_} {E} x lts) | IH | no ¬p = contradiction (D-Properties.D-preserves-nullable x) ¬p
Lemma2∈ (LTS6 {_} {E} lts) with Lemma2∈ lts
... | IH with (E *) ∈? map (_· E *) (D E)
Lemma2∈ (LTS6 {_} {E} lts) | IH | yes p = map-preserves-∈  IH
Lemma2∈ (LTS6 {_} {E} lts) | IH | no ¬p = there (map-preserves-∈  IH)

LTSwToList₃ : ∀{E E' w} → LTSw E w E' → List RegExp
LTSwToList₃ (LTSw[] E) = []
LTSwToList₃ (LTSw:: {_}{F} x d) = F ∷ LTSwToList₃ d

theorem5 : ∀{E F w} → (l : LTSw E w F) → (LTSwToList₃ l) ⊆ (D E)
theorem5 (LTSw[] E) = []
theorem5 (LTSw:: x l) = Lemma2∈ x ∷ (⊆-trans (theorem5 l) (Lemma2⊆ x))

theorem5′ : ∀{E F G w} → LTSw F w G → D F ⊆ D E → D G ⊆ D E
theorem5′ (LTSw[] E) ss = ss
theorem5′ {E} (LTSw:: x lw) ss = theorem5′ {E} lw (⊆-trans (Lemma2⊆ x) ss)









--

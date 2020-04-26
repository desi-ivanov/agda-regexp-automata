module LTS where
open import Regexp
open import Equivalence
open import Brzozowski using (isNullable; Nullable; ε-seq; split-seq; split-*)
open import Data.Char as Char
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import String using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat as ℕ using (ℕ; zero)
open import Data.Fin using (Fin; 0F; 1F; raise; inject+) renaming (suc to fsuc; zero to fzero)
open import Nfa using (splitAt; splitAt-inject+; splitAt-raise)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ˡ_)
open import Data.List.Relation.Unary.Any as Any using (Any; any)
open import Data.List.Relation.Unary.All as All using (All)
open import RegExpSet
open import Data.List using (List; []; _∷_; [_]; map; length)

D : RegExp → RegExpSet
D ⟨⟩ = EmptyRegExpSet
D ⟨ε⟩ = ⟨ε⟩ ∷ []
D (Atom c) = (Atom c) ∷ ⟨ε⟩ ∷ []
D (E + F) = D E ∪ (D F)
D (E · F) with any (isNullable) (D E)
D (E · F) | yes p = map (_· F) (D E) ∪ (D F)
D (E · F) | no ¬p = map (_· F) (D E)
D (E *) = [ E * ] ∪ (map (_· E *) (D E))

data LTS : RegExp → Char → RegExp → Set where
  LTS1 : (a : Char) → LTS (Atom a) a ⟨ε⟩
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

lem2 : ∀{F x xs x₁} → Any (_≡_ x) xs → Any (_≡_ (x · F)) (x₁ · F ∷ map (_· F) xs)
lem2 {F} (Any.here px) = Any.there (Any.here (cong (λ z → z · F) px))
lem2 (Any.there an) = Any.there (lem2 an)

lem1 : ∀{F ss1 ss2} → ss1 ⊆ ss2 → map (_· F) ss1 ⊆ map (_· F) ss2
lem1 {F} All.[] = All.[]
lem1 {F} (Any.here px All.∷ p) = Any.here (cong (λ z → z · F) px) All.∷ lem1 p
lem1 {F} (Any.there px All.∷ p) = lem2 px All.∷ (lem1 p)

lem4 : ∀{E F x₁ x₂ ss} → Any (_≡_ (x₁ · F)) (map (_· F) ss) → Any (_≡_ (x₁ · E)) (x₂ · E ∷ map (_· E) ss)
lem4 {E} {F} {.x₃} {x₂} {x₃ ∷ ss} (Any.here refl) = Any.there (Any.here refl)
lem4 {E} {F} {x₁} {x₂} {x₃ ∷ ss} (Any.there x) = Any.there (lem4 x)

lem3 : ∀{E F ss1 ss2} → (map (_· F) ss1) ⊆ map (_· F) ss2 → (map (_· E) ss1) ⊆ map (_· E) ss2
lem3 {E} {F} {[]} {ss2} x = All.[]
lem3 {E} {F} {.y ∷ ss1} {y ∷ ss2} (Any.here refl All.∷ x) = (Any.here refl) All.∷ lem3 x
lem3 {E} {F} {x₁ ∷ ss1} {x₂ ∷ ss2} (Any.there px All.∷ x) = lem4 px All.∷ lem3 x

module D-Properties where
  open Nullable
  lem6 : ∀{E ss} → (E *) ∈ˡ ss → Any Nullable ss
  lem6 (Any.here refl) = Any.here null*
  lem6 (Any.there ps) = Any.there (lem6 ps)

  lem5 : ∀{E} → Nullable E → Any Nullable (D E)
  lem5 null⟨ε⟩ = Any.here null⟨ε⟩
  lem5 (null+l nlbl) = ∪-preserves-Pˡ (lem5 nlbl)
  lem5 (null+r {E} nlbl) = ∪-preserves-Pʳ {D E} (lem5 nlbl)
  lem5 (null, {E} nlblL nlblR) with any isNullable (D E)
  lem5 (null, {E} {F} nlblL nlblR) | yes p = ∪-preserves-Pʳ {map (_· F) (D E)} (lem5 nlblR)
  lem5 (null, nlblL nlblR) | no ¬p = ⊥-elim(¬p (lem5 nlblL))
  lem5 (null* {F}) with (F *) ∈? map (_· F *) (D F)
  lem5 (null* {F}) | no ¬p = Any.here null*
  lem5 (null* {F}) | yes p = lem6 p


Lemma2 : ∀ {E F a} → (LTS E a F) → D F ⊆ D E
Lemma2 (LTS1 a) = Any.there (Any.here refl) All.∷ All.[]
Lemma2 (LTS2 {F = F} lts) = ∪-preserves-⊆ʳ (Lemma2 lts) (D F)
Lemma2 (LTS3 {E = E} lts) = ∪-preserves-⊆ˡ (Lemma2 lts) (D E)
Lemma2 (LTS4 {_} {E} {F} {E'} lts) with Lemma2 lts
... | IH with any isNullable (D E) | any isNullable (D E')
... | yes p | no ¬p = ∪-preserves-⊆ʳ (lem1 IH) (D F)
... | no ¬p | no ¬p₁ = lem1 IH
... | yes p | yes p₁ = ∪-injects-∪⊆ʳ {map (_· F) (D E)} (∪-preserves-⊆ʳ (lem1 {F} IH) (D F))
... | no ¬p | yes p = contradiction p (⊆-preserves-¬P IH ¬p)
Lemma2 (LTS5 {a}{E}{F}{E'} x lts) with Lemma2 lts
... | IH with any isNullable (D E)
... | yes p = ∪-preserves-⊆ˡ IH (map (_· F) (D E))
... | no ¬p = ⊥-elim(¬p (D-Properties.lem5 x))
Lemma2 (LTS6 {a}{E}{E'} lts) with Lemma2 lts
... | IH with any isNullable (D E')
... | yes p with (E *) ∈? map (_· E *) (D E)
... | yes p₁ = ∪-self-⊆ (lem3 {E *} (lem1 {E'} IH))
... | no ¬p  = ∪-self-⊆ (∷-preserves-⊆ (lem3 {E *} (lem1 {E'} IH)))
Lemma2 (LTS6 {a}{E}{E'} lts) | IH | no ¬p with (E *) ∈? map (_· E *) (D E)
... | yes p = lem3 (lem1 {E'} IH)
... | no ¬p₁ = ∷-preserves-⊆ (lem3 (lem1 {E'} IH))

data LTSw : RegExp → String → RegExp → Set where
  LTSw[] : (E : RegExp) → LTSw E ε E
  LTSw:: : ∀{E F G x xs} → LTS E x F → LTSw F xs G → LTSw E (x ∷ xs) G

open Nullable

lemma4 : ∀{a : Char}{w : String}{E : RegExp}
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
    to {a} {w} {E · E₁} (E' , (LTS5 {_}{_}{_}{E''} n l , r)) = in-· (_⇔_.from Brzozowski.theorem1 n) (to (E' , l , r))

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
    ... | fst , snd , trd = fst , LTS5 (_⇔_.to Brzozowski.theorem1 c) snd , trd

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
    to {[]} {E} d = E , LTSw[] E , (_⇔_.to Brzozowski.theorem1 d)
    to {x ∷ w} {E} d with _⇔_.from (lemma4 {x}{w}{E}) d
    ... | _ , snd , trd with to trd
    ... | a , b , c  = a , LTSw:: snd b , c

    from : ∀{w} {E} → ∃[ E' ] (LTSw E w E' × Nullable E') → w ∈ (E)
    from {[]} {.E'} (E' , LTSw[] .E' , nl) = _⇔_.from Brzozowski.theorem1 nl
    from {x ∷ w} {E} (E' , LTSw:: {_}{F} dl dr , nl) = _⇔_.to (lemma4 {x}{w}{E }) (F , dl , (from (E' , dr ,  nl)))

derivatesList : ∀{E E' w} → LTSw E w E' → List (RegExpSet)
derivatesList (LTSw[] E) = []
derivatesList (LTSw:: {E}{F}{_}{c} x d) = (D F) ∷ derivatesList d

open All.All

lem7 : ∀{a b c} → b ⊆ a → All (_⊆ b) c → All (_⊆ a) c
lem7 [] [] = []
lem7 [] ([] ∷ y) = [] ∷ (lem7 [] y)
lem7 (px ∷ x) [] = []
lem7 (px ∷ x) (px₁ ∷ y) = (⊆-trans px₁ (px ∷ x) ) ∷ lem7 (px ∷ x) y

theorem5 : ∀{E F w} → (l : LTSw E w F) → All (_⊆ D E) (derivatesList l)
theorem5 (LTSw[] E) = []
theorem5 (LTSw:: x l) with Lemma2 x
... | DF⊆DE  = DF⊆DE ∷ (lem7 DF⊆DE (theorem5 l))











--

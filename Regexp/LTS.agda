module LTS where
open import Regexp
open import Equivalence
open import Brzozowski using (Nullable; ε-seq; split-seq; split-*)
open import Data.Char as Char
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import String using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ; foldl)

open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

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


















--

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence
module Regexp (Σ : Set) where
open import String Σ using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ)

ε = []

infixl 6 _+_
infixl 7 _·_
infixl 8 _*
data RegExp : Set where
  ⟨⟩ : RegExp
  ⟨ε⟩ : RegExp
  Atom : (c : Σ) → RegExp
  _+_ : RegExp → RegExp → RegExp
  _·_ : RegExp → RegExp → RegExp
  _* : RegExp → RegExp

infix 10 _∈_
data _∈_ : String → RegExp → Set where
  in-ε :
    ε ∈( ⟨ε⟩ )
  in-c :
    (c : Σ)
    → (c ∷ []) ∈( Atom c )
  in-· :
    ∀ {s t} {E F}
    → s ∈ E
    → t ∈ F
    → (s ++ t) ∈( E · F )
  in+l :
      ∀ {s} {E F}
    → s ∈( E )
    → s ∈( E + F )
  in+r :
    ∀ {s} {E F}
    → s ∈( F )
    → s ∈( E + F )
  in-*1 :
     ∀ {E}
     → ε ∈ (E *)
  in-*2 :
     ∀ {s t} {E}
     → s ∈ E
     → t ∈ (E *)
     → (s ++ t) ∈ (E *)

+-idˡ : ∀ {s : String} {E : RegExp}
  → s ∈(E) ≃ s ∈(⟨⟩ + E)
+-idˡ =
  record
    { to      = in+r
    ; from    = λ{ (in+r x) → x}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{ (in+r y) → refl}
    }

+-idʳ : ∀ {s : String} {E : RegExp}
  → s ∈(E) ≃ s ∈(E + ⟨⟩)
+-idʳ =
  record
    { to      = in+l
    ; from    = λ{ (in+l x) → x }
    ; from∘to = λ x → refl
    ; to∘from = λ{ (in+l y) → refl }
    }

seq-nullʳ : ∀ {s : String} {E : RegExp}
  → s ∈(⟨⟩ · E) ≃ s ∈(⟨⟩)
seq-nullʳ =
  record
    { to = λ{ (in-· () _)}
    ; from = λ()
    ; from∘to = λ{ (in-· () _) }
    ; to∘from = λ{ ()}
    }

seq-nullˡ : ∀ {s : String} {E : RegExp}
  → s ∈(E · ⟨⟩) ≃ s ∈(⟨⟩)
seq-nullˡ =
  record
    { to = λ{ (in-· _ ())}
    ; from = λ()
    ; from∘to = λ{ (in-· _ ()) }
    ; to∘from = λ{ ()}
    }


+-comm : ∀ {s : String} {E F : RegExp}
  → s ∈(E + F) ≃ s ∈(F + E)
+-comm {s} {E} {F} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : s ∈(E + F) → s ∈(F + E)
    to (in+l sef) = in+r sef
    to (in+r sef) = in+l sef

    from : s ∈(F + E) → s ∈(E + F)
    from (in+l x) = in+r x
    from (in+r x) = in+l x

    from∘to : (x : s ∈ (E + F)) → from (to x) ≡ x
    from∘to (in+l x) = refl
    from∘to (in+r x) = refl

    to∘from : (x : s ∈ (F + E)) → to (from x) ≡ x
    to∘from (in+l x) = refl
    to∘from (in+r x) = refl



+-assoc : ∀ {s : String} {E F G : RegExp}
  → s ∈(E + (F + G)) ≃ s ∈((E + F) + G)
+-assoc {s} {E} {F} {G} =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ (E + (F + G)) → s ∈ (E + F + G)
    to (in+l x) = in+l (in+l x)
    to (in+r (in+l x)) = in+l (in+r x)
    to (in+r (in+r x)) = in+r x

    from : s ∈ (E + F + G) → s ∈ (E + (F + G))
    from (in+l (in+l x)) = in+l x
    from (in+l (in+r x)) = in+r (in+l x)
    from (in+r x) = in+r (in+r x)

    from∘to : (x : s ∈ (E + (F + G))) → from (to x) ≡ x
    from∘to (in+l x) = refl
    from∘to (in+r (in+l x)) = refl
    from∘to (in+r (in+r x)) = refl

    to∘from : (y : s ∈ (E + F + G)) → to (from y) ≡ y
    to∘from (in+l (in+l y)) = refl
    to∘from (in+l (in+r y)) = refl
    to∘from (in+r y) = refl



seq-assoc : ∀ {s : String} {E F G : RegExp}
  → s ∈(E · (F · G)) ⇔ s ∈((E · F) · G)
seq-assoc {s} {E} {F} {G} =
  record
    { to = to
    ; from = from
    }
  where
    to : ∀ {s} {E} {F} {G} →  s ∈ (E · (F · G)) → s ∈ ((E · F) · G)
    to {_} {E} {F} {G} (in-· {t} x (in-· {u} {v} y z)) =
      subst (_∈((E · F) · G)) (++-assoc t u v) ((in-· (in-· x y) z))

    from : ∀ {s} {E} {F} {G} →  s ∈ ((E · F) · G) → s ∈ (E · (F · G))
    from {_} {E} {F} {G} (in-· {_} {v} (in-· {t} {u} x y) z) =
      subst (_∈(E · (F · G))) (sym (++-assoc t u v)) (in-· x (in-· y z))



seq-distrib-+ˡ : ∀ {s : String} {E F G : RegExp}
  → s ∈(E · (F + G)) ≃ s ∈(E · F + E · G)
seq-distrib-+ˡ {s} {E} {F} {G} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ (E · (F + G)) → s ∈ (E · F + E · G)
    to (in-· x (in+l y)) = in+l (in-· x y)
    to (in-· x (in+r y)) = in+r (in-· x y)

    from : s ∈ (E · F + E · G) → s ∈ (E · (F + G))
    from (in+l (in-· x y)) = in-· x (in+l y)
    from (in+r (in-· x y)) = in-· x (in+r y)

    from∘to : (x : s ∈ (E · (F + G))) → from (to x) ≡ x
    from∘to (in-· x (in+l y)) = refl
    from∘to (in-· x (in+r y)) = refl

    to∘from : (y : s ∈ (E · F + E · G)) → to (from y) ≡ y
    to∘from (in+l (in-· y y₁)) = refl
    to∘from (in+r (in-· y y₁)) = refl


seq-distrib-+ʳ : ∀ {s : String} {E F G : RegExp}
  → s ∈((E + F) · G) ≃ s ∈(E · G + F · G)
seq-distrib-+ʳ {s} {E} {F} {G} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ ((E + F) · G) → s ∈ (E · G + F · G)
    to (in-· (in+l x) y) = in+l (in-· x y)
    to (in-· (in+r x) y) = in+r (in-· x y)

    from : s ∈ (E · G + F · G) → s ∈ ((E + F) · G)
    from (in+l (in-· x x₁)) = in-· (in+l x) x₁
    from (in+r (in-· x x₁)) = in-· (in+r x) x₁

    from∘to : (x : s ∈ ((E + F) · G)) → from (to x) ≡ x
    from∘to (in-· (in+l x) y) = refl
    from∘to (in-· (in+r x) y) = refl

    to∘from : (y : s ∈ (E · G + F · G)) → to (from y) ≡ y
    to∘from (in+l (in-· y y₁)) = refl
    to∘from (in+r (in-· y y₁)) = refl



seq-idˡ : ∀ {s : String} {E : RegExp}
  → s ∈(⟨ε⟩ · E) ≃ s ∈(E)
seq-idˡ {s} {E} =
  record
    { to      = λ { (in-· in-ε x) → x }
    ; from    = λ { x → in-· in-ε x }
    ; from∘to = λ { (in-· in-ε x₁) → refl }
    ; to∘from = λ { y → refl }
    }



seq-idʳ : ∀ {s : String} {E : RegExp}
  → s ∈(E · ⟨ε⟩) ⇔ s ∈(E)
seq-idʳ {s} {E} =
  record
    { to      = to
    ; from    = from
    }
  where
    to : s ∈ (E · ⟨ε⟩) → s ∈ E
    to (in-· {u} x in-ε) rewrite  ++-idʳ u = x

    from : ∀ {E} {v} → v ∈(E) → v ∈(E · ⟨ε⟩)
    from {E} {v} x = subst (_∈(E · ⟨ε⟩)) (++-idʳ v) (in-· x in-ε)


ε-guaranteed-* : ∀ {s : String} {E : RegExp}
  → s ∈(E *) ⇔ s ∈( (E + ⟨ε⟩) * )
ε-guaranteed-* {s} {E} =
  record
    { to = to
    ; from = from
    }
  where
    to : ∀ {E}{v} → v ∈ (E *) → v ∈ ((E + ⟨ε⟩) *)
    to in-*1 = in-*1
    to (in-*2 {s} {[]} x y) = in-*2 (in+l x) (to y)
    to (in-*2 {s} {t ∷ ts} x y) = in-*2 (in+l x) (to y)

    from : ∀ {F}{v} → v ∈ ((F + ⟨ε⟩) *) → v ∈ (F *)
    from in-*1 = in-*1
    from (in-*2 {v} (in+l x) y) = in-*2 x (from y)
    from (in-*2 {[]} (in+r x) y) = from y

+-idempotent : ∀ {s : String} {E : RegExp}
  → s ∈(E + E) ⇔ s ∈(E)
+-idempotent {s}{E} =
  record
    { to = λ{ (in+l x) → x ; (in+r x) → x }
    ; from = in+l
    }

lemma1 : ∀ {s}{t}{E}
  → s ∈(E *)
  → t ∈(E *)
    ---------
  → (s ++ t) ∈(E *)
lemma1 {_} {t} in-*1 y = y
lemma1 {_} {t} {E} (in-*2 {u} {v} x y) z =
  subst (_∈(E *)) (sym (++-assoc u v t)) (in-*2 x (lemma1 y z))


*-idempotent : ∀ {s : String} {E : RegExp}
  → s ∈(E *) ⇔ s ∈( E * * )
*-idempotent {s} {E} =
  record
    { to = to
    ; from = from }
  where
    to : ∀ {E} {v} → v ∈(E *) → v ∈( E * * )
    to {E} {v} in-*1 = in-*1
    to {E} {v} (in-*2 {t} {u} x y) =
        subst (_∈(E * *)) (++-idʳ v) (in-*2 (in-*2 x y) in-*1)

    from : ∀ {E} {v} → v ∈( E * * ) → v ∈(E *)
    from in-*1 = in-*1
    from {E} (in-*2 {ts} {_} x y) with from y
    ... | a = lemma1 x a

zero* : ∀ {s}
  → s ∈(⟨⟩ *) ≃ s ∈(⟨ε⟩)
zero* =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : ∀{s} → s ∈ (⟨⟩ *) → s ∈ ⟨ε⟩
    to in-*1 = in-ε
    from : ∀{s} → s ∈ ⟨ε⟩ → s ∈ (⟨⟩ *)
    from in-ε = in-*1
    from∘to : ∀{s} → (x : s ∈ (⟨⟩ *)) → from (to x) ≡ x
    from∘to in-*1 = refl
    to∘from : ∀{s} → (y : s ∈ ⟨ε⟩) → to (from y) ≡ y
    to∘from in-ε = refl

one* : ∀ {s} → s ∈(⟨ε⟩ *) ⇔ s ∈(⟨ε⟩)
one* {s} =
  record
    { to = to
    ; from = from
    }
  where
    to : s ∈(⟨ε⟩ *) → s ∈(⟨ε⟩)
    to in-*1 = in-ε
    to (in-*2 in-ε x) = to x

    from : s ∈ ⟨ε⟩ → s ∈ (⟨ε⟩ *)
    from in-ε = in-*1

lemma2 : ∀ {s}{E}
  → s ∈(E)
    -------
  → s ∈(E *)
lemma2 {s} {E} x = subst (_∈(E *)) ((++-idʳ s)) (in-*2 x in-*1)

-- Extensions

-- One or more instances
infixl 8 _⁺
_⁺ : RegExp → RegExp
E ⁺ = E · E *

⁺law : ∀ {s}{E}
  → s ∈(E *) ≃ s ∈(E ⁺ + ⟨ε⟩)
⁺law =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : ∀ {s E} → s ∈ (E *) → s ∈ ((E ⁺) + ⟨ε⟩)
    to in-*1 = in+r in-ε
    to (in-*2 x x₁) = in+l (in-· x x₁)

    from : ∀ {s}{E} → s ∈ ((E ⁺) + ⟨ε⟩) → s ∈ (E *)
    from (in+l (in-· x x₁)) = in-*2 x x₁
    from (in+r in-ε) = in-*1

    from∘to : ∀{s E} → (x : s ∈ (E *)) → from (to x) ≡ x
    from∘to in-*1 = refl
    from∘to (in-*2 x x₁) = refl

    to∘from : ∀{s E} → (y : s ∈ (E ⁺ + ⟨ε⟩)) → to (from y) ≡ y
    to∘from (in+l (in-· x x₁)) = refl
    to∘from (in+r in-ε) = refl

-- Zero or one instance
infixl 8 _⁇
_⁇ : RegExp → RegExp
R ⁇ = R + ⟨ε⟩

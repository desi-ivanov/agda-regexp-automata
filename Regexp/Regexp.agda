module Regexp where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst; trans)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary using (¬_)
open import Data.Char as Char
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import String using (_++_; _∷_; ++-assoc; []; String; ++-idʳ; ++-idˡ)

ε = []

infixl 6 _+_
infixl 7 _,_
infixl 8 _*
data RegExp : Set where
  ⟨⟩ : RegExp
  ⟨ε⟩ : RegExp
  Atom : (c : Char) → RegExp
  _+_ : RegExp → RegExp → RegExp
  _,_ : RegExp → RegExp → RegExp
  _* : RegExp → RegExp

infix 10 _∈ℒ_
data _∈ℒ_ : String → RegExp → Set where
  ∈ℒ[] :
    ε ∈ℒ( ⟨ε⟩ )
  ∈ℒc :
    (c : Char)
    →  (c ∷ []) ∈ℒ( Atom c )
  ∈ℒ-, :
    ∀ {s t} {E F}
    → s ∈ℒ( E )
    → t ∈ℒ( F )
    → (s ++ t) ∈ℒ( E , F )
  ∈ℒ+l :
      ∀ {s} {E F}
    → s ∈ℒ( E )
    → s ∈ℒ( E + F )
  ∈ℒ+r :
    ∀ {s} {E F}
    → s ∈ℒ( F )
    → s ∈ℒ( E + F )
  ∈ℒ*-0 :
    ∀ {E}
    → ε ∈ℒ( E * )
  ∈ℒ*-+ :
    ∀ {s t} {E}
    → s ∈ℒ( E )
    → t ∈ℒ( E * )
    → (s ++ t) ∈ℒ( E * )

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

+-idˡ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E) ≃ s ∈ℒ(⟨⟩ + E)
+-idˡ =
  record
    { to      = ∈ℒ+r
    ; from    = λ{ (∈ℒ+r x) → x}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{ (∈ℒ+r y) → refl}
    }

+-idʳ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E) ≃ s ∈ℒ(E + ⟨⟩)
+-idʳ =
  record
    { to      = ∈ℒ+l
    ; from    = λ{ (∈ℒ+l x) → x }
    ; from∘to = λ x → refl
    ; to∘from = λ{ (∈ℒ+l y) → refl }
    }

seq-nullʳ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(⟨⟩ , E) ≃ s ∈ℒ(⟨⟩)
seq-nullʳ =
  record
    { to = λ{ (∈ℒ-, () _)}
    ; from = λ()
    ; from∘to = λ{ (∈ℒ-, () _) }
    ; to∘from = λ{ ()}
    }

seq-nullˡ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E , ⟨⟩) ≃ s ∈ℒ(⟨⟩)
seq-nullˡ =
  record
    { to = λ{ (∈ℒ-, _ ())}
    ; from = λ()
    ; from∘to = λ{ (∈ℒ-, _ ()) }
    ; to∘from = λ{ ()}
    }


+-comm : ∀ {s : String} {E F : RegExp}
  → s ∈ℒ(E + F) ≃ s ∈ℒ(F + E)
+-comm {s} {E} {F} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : s ∈ℒ(E + F) → s ∈ℒ(F + E)
    to (∈ℒ+l sef) = ∈ℒ+r sef
    to (∈ℒ+r sef) = ∈ℒ+l sef

    from : s ∈ℒ(F + E) → s ∈ℒ(E + F)
    from (∈ℒ+l x) = ∈ℒ+r x
    from (∈ℒ+r x) = ∈ℒ+l x

    from∘to : (x : s ∈ℒ (E + F)) → from (to x) ≡ x
    from∘to (∈ℒ+l x) = refl
    from∘to (∈ℒ+r x) = refl

    to∘from : (x : s ∈ℒ (F + E)) → to (from x) ≡ x
    to∘from (∈ℒ+l x) = refl
    to∘from (∈ℒ+r x) = refl



+-assoc : ∀ {s : String} {E F G : RegExp}
  → s ∈ℒ(E + (F + G)) ≃ s ∈ℒ((E + F) + G)
+-assoc {s} {E} {F} {G} =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ℒ (E + (F + G)) → s ∈ℒ (E + F + G)
    to (∈ℒ+l x) = ∈ℒ+l (∈ℒ+l x)
    to (∈ℒ+r (∈ℒ+l x)) = ∈ℒ+l (∈ℒ+r x)
    to (∈ℒ+r (∈ℒ+r x)) = ∈ℒ+r x

    from : s ∈ℒ (E + F + G) → s ∈ℒ (E + (F + G))
    from (∈ℒ+l (∈ℒ+l x)) = ∈ℒ+l x
    from (∈ℒ+l (∈ℒ+r x)) = ∈ℒ+r (∈ℒ+l x)
    from (∈ℒ+r x) = ∈ℒ+r (∈ℒ+r x)

    from∘to : (x : s ∈ℒ (E + (F + G))) → from (to x) ≡ x
    from∘to (∈ℒ+l x) = refl
    from∘to (∈ℒ+r (∈ℒ+l x)) = refl
    from∘to (∈ℒ+r (∈ℒ+r x)) = refl

    to∘from : (y : s ∈ℒ (E + F + G)) → to (from y) ≡ y
    to∘from (∈ℒ+l (∈ℒ+l y)) = refl
    to∘from (∈ℒ+l (∈ℒ+r y)) = refl
    to∘from (∈ℒ+r y) = refl



seq-assoc : ∀ {s : String} {E F G : RegExp}
  → s ∈ℒ(E , (F , G)) ⇔ s ∈ℒ((E , F) , G)
seq-assoc {s} {E} {F} {G} =
  record
    { to = to
    ; from = from
    }
  where
    to : ∀ {s} {E} {F} {G} →  s ∈ℒ (E , (F , G)) → s ∈ℒ ((E , F) , G)
    to {_} {E} {F} {G} (∈ℒ-, {t} x (∈ℒ-, {u} {v} y z)) =
      subst (_∈ℒ((E , F) , G)) (++-assoc t u v) ((∈ℒ-, (∈ℒ-, x y) z))

    from : ∀ {s} {E} {F} {G} →  s ∈ℒ ((E , F) , G) → s ∈ℒ (E , (F , G))
    from {_} {E} {F} {G} (∈ℒ-, {_} {v} (∈ℒ-, {t} {u} x y) z) =
      subst (_∈ℒ(E , (F , G))) (sym (++-assoc t u v)) (∈ℒ-, x (∈ℒ-, y z))



seq-distrib-+ˡ : ∀ {s : String} {E F G : RegExp}
  → s ∈ℒ(E , (F + G)) ≃ s ∈ℒ(E , F + E , G)
seq-distrib-+ˡ {s} {E} {F} {G} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ℒ (E , (F + G)) → s ∈ℒ (E , F + E , G)
    to (∈ℒ-, x (∈ℒ+l y)) = ∈ℒ+l (∈ℒ-, x y)
    to (∈ℒ-, x (∈ℒ+r y)) = ∈ℒ+r (∈ℒ-, x y)

    from : s ∈ℒ (E , F + E , G) → s ∈ℒ (E , (F + G))
    from (∈ℒ+l (∈ℒ-, x y)) = ∈ℒ-, x (∈ℒ+l y)
    from (∈ℒ+r (∈ℒ-, x y)) = ∈ℒ-, x (∈ℒ+r y)

    from∘to : (x : s ∈ℒ (E , (F + G))) → from (to x) ≡ x
    from∘to (∈ℒ-, x (∈ℒ+l y)) = refl
    from∘to (∈ℒ-, x (∈ℒ+r y)) = refl

    to∘from : (y : s ∈ℒ (E , F + E , G)) → to (from y) ≡ y
    to∘from (∈ℒ+l (∈ℒ-, y y₁)) = refl
    to∘from (∈ℒ+r (∈ℒ-, y y₁)) = refl


seq-distrib-+ʳ : ∀ {s : String} {E F G : RegExp}
  → s ∈ℒ((E + F) , G) ≃ s ∈ℒ(E , G + F , G)
seq-distrib-+ʳ {s} {E} {F} {G} =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from }
  where
    to : s ∈ℒ ((E + F) , G) → s ∈ℒ (E , G + F , G)
    to (∈ℒ-, (∈ℒ+l x) y) = ∈ℒ+l (∈ℒ-, x y)
    to (∈ℒ-, (∈ℒ+r x) y) = ∈ℒ+r (∈ℒ-, x y)

    from : s ∈ℒ (E , G + F , G) → s ∈ℒ ((E + F) , G)
    from (∈ℒ+l (∈ℒ-, x x₁)) = ∈ℒ-, (∈ℒ+l x) x₁
    from (∈ℒ+r (∈ℒ-, x x₁)) = ∈ℒ-, (∈ℒ+r x) x₁

    from∘to : (x : s ∈ℒ ((E + F) , G)) → from (to x) ≡ x
    from∘to (∈ℒ-, (∈ℒ+l x) y) = refl
    from∘to (∈ℒ-, (∈ℒ+r x) y) = refl

    to∘from : (y : s ∈ℒ (E , G + F , G)) → to (from y) ≡ y
    to∘from (∈ℒ+l (∈ℒ-, y y₁)) = refl
    to∘from (∈ℒ+r (∈ℒ-, y y₁)) = refl



seq-idˡ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(⟨ε⟩ , E) ≃ s ∈ℒ(E)
seq-idˡ {s} {E} =
  record
    { to      = λ { (∈ℒ-, ∈ℒ[] x) → x }
    ; from    = λ { x → ∈ℒ-, ∈ℒ[] x }
    ; from∘to = λ { (∈ℒ-, ∈ℒ[] x₁) → refl }
    ; to∘from = λ { y → refl }
    }



seq-idʳ : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E , ⟨ε⟩) ⇔ s ∈ℒ(E)
seq-idʳ {s} {E} =
  record
    { to      = to
    ; from    = from
    }
  where
    to : s ∈ℒ (E , ⟨ε⟩) → s ∈ℒ E
    to (∈ℒ-, {u} x ∈ℒ[]) rewrite  ++-idʳ u = x

    from : ∀ {E} {v} → v ∈ℒ(E) → v ∈ℒ(E , ⟨ε⟩)
    from {E} {v} x = subst (_∈ℒ(E , ⟨ε⟩)) (++-idʳ v) (∈ℒ-, x ∈ℒ[])


ε-guaranteed-* : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E *) ⇔ s ∈ℒ( (E + ⟨ε⟩) * )
ε-guaranteed-* {s} {E} =
  record
    { to = to
    ; from = from
    }
  where
    to : ∀ {E}{v} → v ∈ℒ (E *) → v ∈ℒ ((E + ⟨ε⟩) *)
    to ∈ℒ*-0 = ∈ℒ*-0
    to (∈ℒ*-+ {s} {[]} x y) = ∈ℒ*-+ (∈ℒ+l x) (to y)
    to (∈ℒ*-+ {s} {t ∷ ts} x y) = ∈ℒ*-+ (∈ℒ+l x) (to y)

    from : ∀ {F}{v} → v ∈ℒ ((F + ⟨ε⟩) *) → v ∈ℒ (F *)
    from ∈ℒ*-0 = ∈ℒ*-0
    from (∈ℒ*-+ {v} (∈ℒ+l x) y) = ∈ℒ*-+ x (from y)
    from (∈ℒ*-+ {[]} (∈ℒ+r x) y) = from y

+-idempotent : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E + E) ⇔ s ∈ℒ(E)
+-idempotent {s}{E} =
  record
    { to = λ{ (∈ℒ+l x) → x ; (∈ℒ+r x) → x }
    ; from = ∈ℒ+l
    }

lemma1 : ∀ {s}{t}{E}
  → s ∈ℒ(E *)
  → t ∈ℒ(E *)
    ---------
  → (s ++ t) ∈ℒ(E *)
lemma1 {_} {t} ∈ℒ*-0 y = y
lemma1 {_} {t} {E} (∈ℒ*-+ {u} {v} x y) z =
  subst (_∈ℒ(E *)) (sym (++-assoc u v t)) (∈ℒ*-+ x (lemma1 y z))


*-idempotent : ∀ {s : String} {E : RegExp}
  → s ∈ℒ(E *) ⇔ s ∈ℒ( E * * )
*-idempotent {s} {E} =
  record
    { to = to
    ; from = from }
  where
    to : ∀ {E} {v} → v ∈ℒ(E *) → v ∈ℒ( E * * )
    to {E} {v} ∈ℒ*-0 = ∈ℒ*-0
    to {E} {v} (∈ℒ*-+ {t} {u} x y) =
        subst (_∈ℒ(E * *)) (++-idʳ v) (∈ℒ*-+ (∈ℒ*-+ x y) ∈ℒ*-0)

    from : ∀ {E} {v} → v ∈ℒ( E * * ) → v ∈ℒ(E *)
    from ∈ℒ*-0 = ∈ℒ*-0
    from {E} (∈ℒ*-+ {ts} {_} x y) with from y
    ... | a = lemma1 x a

zero* : ∀ {s}
  → s ∈ℒ(⟨⟩ *) ⇔ s ∈ℒ(⟨ε⟩)
zero* =
  record
    { to = λ{ ∈ℒ*-0 → ∈ℒ[] }
    ; from = λ{ ∈ℒ[] → ∈ℒ*-0 }
    }

one* : ∀ {s} → s ∈ℒ(⟨ε⟩ *) ⇔ s ∈ℒ(⟨ε⟩)
one* {s} =
  record
    { to = to
    ; from = λ{ ∈ℒ[] → ∈ℒ*-0 }
    }
  where
    to : s ∈ℒ(⟨ε⟩ *) → s ∈ℒ(⟨ε⟩)
    to ∈ℒ*-0 = ∈ℒ[]
    to (∈ℒ*-+ ∈ℒ[] x) = to x



lemma2 : ∀ {s}{E}
  → s ∈ℒ(E)
    -------
  → s ∈ℒ(E *)
lemma2 {s} {E} x = subst (_∈ℒ(E *)) ((++-idʳ s)) (∈ℒ*-+ x ∈ℒ*-0)

-- Extensions

-- One or more instances
infixl 8 _⁺
_⁺ : RegExp → RegExp
E ⁺ = E , E *

⁺law : ∀ {s}{E}
  → s ∈ℒ(E *) ⇔ s ∈ℒ(E ⁺ + ⟨ε⟩)
⁺law =
  record
    { to = to
    ; from = from }
  where
    to : ∀ {s}{E} → s ∈ℒ (E *) → s ∈ℒ ((E ⁺) + ⟨ε⟩)
    to ∈ℒ*-0 = ∈ℒ+r ∈ℒ[]
    to (∈ℒ*-+ x x₁) = ∈ℒ+l (∈ℒ-, x x₁)

    from : ∀ {s}{E} → s ∈ℒ ((E ⁺) + ⟨ε⟩) → s ∈ℒ (E *)
    from (∈ℒ+l (∈ℒ-, x x₁)) = ∈ℒ*-+ x x₁
    from (∈ℒ+r ∈ℒ[]) = ∈ℒ*-0

-- Zero or one instance
infixl 8 _⁇
_⁇ : RegExp → RegExp
R ⁇ = R + ⟨ε⟩












--

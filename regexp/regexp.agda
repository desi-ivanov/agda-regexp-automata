module regexp where
import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Empty using (⊥; ⊥-elim)
import Data.Unit using (⊤; tt)
open import Data.Char as Char
open import Data.Bool

infixr 5 _∷_
data String : Set where
  [] : String
  _∷_ : Char → String → String

pattern [_] z = z ∷ []
ε = []

infixr 5 _++_
_++_ : String → String → String
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data RegExp : Set where
  ⟨⟩ : RegExp
  ⟨ε⟩ : RegExp
  Atom : (c : Char) → RegExp
  _+_ : RegExp → RegExp → RegExp
  _,_ : RegExp → RegExp → RegExp
  _* : RegExp → RegExp

infixl 0 _∈ℒ_
data _∈ℒ_ : String → RegExp → Set where
  ∈ℒ[] :
    ε ∈ℒ( ⟨ε⟩ )
  ∈ℒc :
    (c : Char)
    → [ c ] ∈ℒ( Atom c )
  ∈ℒ-, :
    ∀ {s t} {E F}
    → s ∈ℒ( E )
    → t ∈ℒ( F )
    → s ++ t ∈ℒ( E , F )
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
    → t ∈ℒ( E *)
    → s ++ t ∈ℒ( E * )

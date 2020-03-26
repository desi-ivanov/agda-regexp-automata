module String where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Char as Char

infixr 5 _∷_
data String : Set where
  [] : String
  _∷_ : Char → String → String


infixr 5 _++_
_++_ : String → String → String
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ (s t g : String) → (s ++ t) ++ g ≡ s ++ (t ++ g)
++-assoc [] t g = refl
++-assoc (x ∷ s) t g rewrite ++-assoc s t g = refl

++-idʳ : ∀ (s : String)  → (s ++ []) ≡ s
++-idʳ [] = refl
++-idʳ (x ∷ s) rewrite ++-idʳ s = refl

++-idˡ : ∀ (s : String)  → ([] ++ s) ≡ s
++-idˡ [] = refl
++-idˡ (x ∷ x₁) = refl

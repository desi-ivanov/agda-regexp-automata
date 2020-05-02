open import Data.Nat using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
module String (Σ : Set) where

infixr 5 _∷_
data String : Set where
  [] : String
  _∷_ : Σ → String → String


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

foldl : ∀ {B : Set} → (Σ → B → B) → B →  String → B
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f x b) xs

length : String → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

take : ℕ → String → String
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → String → String
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

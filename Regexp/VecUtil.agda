module VecUtil where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec

infixl 45 _!_
_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[]     ! ()
(x ∷ xs) ! fzero  = x
(x ∷ xs) ! fsuc i = xs ! i

build : {n : ℕ}{A : Set} -> (Fin n -> A) -> Vec A n
build {zero } f = []
build {suc _} f = f fzero ∷ build (λ x → f (fsuc x))

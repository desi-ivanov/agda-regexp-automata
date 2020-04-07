module VecUtil where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec
open import Data.Fin.Subset using (Subset)
open import Data.Bool using (false; true)

infixl 45 _!_
_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[]     ! ()
(x ∷ xs) ! fzero  = x
(x ∷ xs) ! fsuc i = xs ! i

build : {n : ℕ}{A : Set} -> (Fin n -> A) -> Vec A n
build {zero } f = []
build {suc _} f = f fzero ∷ build (λ x → f (fsuc x))

ifPresentOrElse : ∀{m} {A : Set} → Fin m → Subset m → (B : Fin m → A) → A → A
ifPresentOrElse i s f z with s ! i
... | false = z
... | true = f i

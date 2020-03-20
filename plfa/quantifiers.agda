module quantifiers where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; Σ) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥; ⊥-elim)
open import isomorphism using (_≃_; extensionality)
open import relations using (even; odd; Can; BinStartsOne; natToBinYieldsCan; cantofromb)
open import introduction using (Bin; ⟨⟩; _O; _I; inc; natToBin; binToNat; binLaw2)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- Show that universals distribute over conjunction:
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ x → ⟨ (λ y → proj₁ (x y)) , (λ y → proj₂ (x y)) ⟩
  ; from = λ x y → ⟨ (proj₁ x y) , (proj₂ x y) ⟩
  ; from∘to = λ x → refl
  ; to∘from = λ x → refl
  }

-- Show that a disjunction of universals implies a universal of disjunctions:
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ x) y = _⊎_.inj₁ (x y)
⊎∀-implies-∀⊎ (_⊎_.inj₂ y₁) y = _⊎_.inj₂ (y₁ y)

-- Does the converse hold? If so, prove; if not, explain why.
--                conv : ∀ {A : Set} {B C : A → Set}
--                    →  ∀ (x : A) → B x ⊎ C x
--                    → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- No, given
-- ∀ (x : A) → B x ⊎ C x
-- there can be two xs' x1 and x2 in A for which
-- B x1 holds
-- B x2 doesn't hold
-- C x1 doesn't hold
-- C x2 holds
-- therefore neither
--             ∀ (x : A) → B x
--             or
--             ∀ (x : A) → C x
-- can hold

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- Let B be a type indexed by Tri, that is B : Tri → Set.
-- Show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc.

postulate
  extensionalityDep : ∀ {A : Set} {B : A → Set} (f g : (∀ (x : A) → B x))
    → (∀ (x : A) → f x ≡ g x)
   --------------------------
    → f ≡ g

to : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) → B aa × B bb × B cc
to x = ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩

from : ∀ {B : Tri → Set} → B aa × B bb × B cc → (∀ (x : Tri) → B x)
from ⟨ fst , snd ⟩ aa = fst
from ⟨ fst , snd ⟩ bb = proj₁ snd
from ⟨ fst , snd ⟩ cc = proj₂ snd

es : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
es = record
  { to      = to
  ; from    = from
  ; from∘to = λ x → extensionalityDep (from (to x)) x λ { aa → refl
                                                        ; bb → refl
                                                        ; cc → refl
                                                        }
  ; to∘from = λ y → refl
  }





-- data Σ (A : Set) (B : A → Set) : Set where
--   ⟨_,_⟩ : (x : A) → B x → Σ A B
--
-- Σ-syntax = Σ
-- infix 2 Σ-syntax
-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to      = λ{x → λ{ ⟨ y , z ⟩ → x y z}}
  ; from    = λ x y z → x ⟨ y , z ⟩
  ; from∘to = λ x → refl
  ; to∘from = λ y → extensionality λ{ ⟨ x , y ⟩ → refl}
  }

-- Show that existentials distribute over disjunction:
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to      = λ { ⟨ x , _⊎_.inj₁ x₁ ⟩ → _⊎_.inj₁ ⟨ x , x₁ ⟩
                ; ⟨ x , _⊎_.inj₂ y ⟩ → _⊎_.inj₂ ⟨ x , y ⟩
                }
  ; from    = λ { (_⊎_.inj₁ ⟨ x , x₁ ⟩) → ⟨ x , _⊎_.inj₁ x₁ ⟩
                ; (_⊎_.inj₂ ⟨ x , x₁ ⟩) → ⟨ x , (_⊎_.inj₂ x₁) ⟩
                }
  ; from∘to = λ { ⟨ x , _⊎_.inj₁ x₁ ⟩ → refl
                ; ⟨ x , _⊎_.inj₂ y ⟩ → refl
                }
  ; to∘from = λ { (_⊎_.inj₁ ⟨ x , x₁ ⟩) → refl
                ; (_⊎_.inj₂ ⟨ x , x₁ ⟩) → refl
                }
  }

-- Show that an existential of conjunctions implies a conjunction of existentials:
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , x₁ ⟩ = ⟨ ⟨ x , proj₁ x₁ ⟩ , ⟨ x , proj₂ x₁ ⟩ ⟩
-- Does the converse hold?
-- No

-- Let Tri and B be as in Exercise ∀-×.
-- Show that ∃[ x ] B x is isomorphic to B aa ⊎ B bb ⊎ B cc.
to2 : ∀ {B : Tri → Set} → ∃[ x ] B x → B aa ⊎ B bb ⊎ B cc
to2 ⟨ aa , y ⟩ = _⊎_.inj₁ y
to2 ⟨ bb , y ⟩ = _⊎_.inj₂ (_⊎_.inj₁ y)
to2 ⟨ cc , y ⟩ = _⊎_.inj₂ (_⊎_.inj₂ y)

from2 : ∀ {B : Tri → Set} → B aa ⊎ B bb ⊎ B cc → ∃[ x ] B x
from2 (_⊎_.inj₁ x) = ⟨ aa , x ⟩
from2 (_⊎_.inj₂ (_⊎_.inj₁ x)) = ⟨ bb , x ⟩
from2 (_⊎_.inj₂ (_⊎_.inj₂ x)) = ⟨ cc , x ⟩

es2 : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
es2 = record
  { to      = to2
  ; from    = from2
  ; from∘to = λ { ⟨ aa , y ⟩ → refl
                ; ⟨ bb , y ⟩ → refl
                ; ⟨ cc , y ⟩ → refl
                }
  ; to∘from = λ { (_⊎_.inj₁ x) → refl
                ; (_⊎_.inj₂ (_⊎_.inj₁ x)) → refl
                ; (_⊎_.inj₂ (_⊎_.inj₂ y)) → refl
                }
  }

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even.zero                       =  ⟨ zero , refl ⟩
even-∃ (even.suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd.suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even.zero
∃-even ⟨ suc m , refl ⟩  =  even.suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd.suc (∃-even ⟨ m , refl ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }


-- Show that existential of a negation implies negation of a universal:
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , x₁ ⟩ b = x₁ (b x)


-- Establish that there is an isomorphism between ℕ and ∃[ b ](Can b).
≡One : ∀{b : Bin} (o o' : BinStartsOne b) → o ≡ o'
≡One BinStartsOne.isOne BinStartsOne.isOne = refl
≡One (BinStartsOne.flwByOne b o) (BinStartsOne.flwByOne .b x) = sym (cong (BinStartsOne.flwByOne b) (≡One x o))
≡One (BinStartsOne.flwByZero b o) (BinStartsOne.flwByZero .b x) = sym (cong (BinStartsOne.flwByZero b) (≡One x o))

≡Bso : ∀{b : Bin} (bo bo' : BinStartsOne b) → bo ≡ bo'
≡Bso BinStartsOne.isOne BinStartsOne.isOne = refl
≡Bso (BinStartsOne.flwByOne b b₁) (BinStartsOne.flwByOne .b c) = sym (cong (BinStartsOne.flwByOne b) (≡Bso c b₁))
≡Bso (BinStartsOne.flwByZero b b₁) (BinStartsOne.flwByZero .b c) = sym (cong (BinStartsOne.flwByZero b) (≡Bso c b₁))

≡Can : ∀{b : Bin} (cb cb' : Can b) → cb ≡ cb'
≡Can Can.zeroIsCan Can.zeroIsCan = refl
≡Can (Can.startsWithOne (b O) x) (Can.startsWithOne (b O) x2) rewrite ≡Bso x x2  = refl
≡Can (Can.startsWithOne (b I) x) (Can.startsWithOne .(b I) x2) rewrite ≡Bso x x2 = refl
≡Can Can.zeroIsCan (Can.startsWithOne .(⟨⟩ O) (BinStartsOne.flwByZero .⟨⟩ ()))
≡Can (Can.startsWithOne .(⟨⟩ O) (BinStartsOne.flwByZero .⟨⟩ ())) Can.zeroIsCan

proj₁≡→Can≡ : (cb cb′ : ∃[ b ](Can b)) → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ ⟨ fst , snd ⟩ ⟨ fst , snd2 ⟩ refl =
  begin
    ⟨ fst , snd ⟩
  ≡⟨ cong (λ x → ⟨ fst , x ⟩) (≡Can snd snd2) ⟩
    ⟨ fst , snd2 ⟩
  ∎

es3to : ℕ → ∃[ b ](Can b)
es3to x = ⟨ natToBin x , natToBinYieldsCan x ⟩

es3from : ∃[ b ](Can b) → ℕ
es3from ⟨ x , y ⟩ = binToNat x

es3 : ℕ ≃ ∃[ b ](Can b)
es3 = record
  { to = es3to
  ; from = es3from
  ; from∘to = λ { x → binLaw2 x}
  ; to∘from = λ { ⟨ fst , snd ⟩ → proj₁≡→Can≡ ⟨ natToBin (binToNat fst) , natToBinYieldsCan (binToNat fst) ⟩ ⟨ fst , snd ⟩ (cantofromb fst snd) }
  }




--

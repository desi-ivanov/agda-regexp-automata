module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_; _<?_; _≤?_; s≤s; z≤n)
open import Data.Fin
  using (Fin; inject+; toℕ; raise; fromℕ≤; _ℕ-_; reduce≥)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T)
open import Data.Bool.Properties using (T?)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; []) renaming (_++_ to _++ˢ_)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v) hiding (concat)
open import Data.Vec.Relation.Unary.Any using (index) renaming (any to any?)
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans; cong)

record Nfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    F : Subset n

δ̂ : ∀{n} → Nfa n → (Subset n) → String → (Subset n)
δ̂ {n} nfa qs [] = qs
δ̂ {n} nfa qs (x ∷ s) = δ̂ nfa (onestep qs x) s
  where
    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = U (mapS qs (λ q → Nfa.δ nfa q c) ∅)

infix 10 _↓′_
_↓′_ : ∀{n} → Nfa n → String → Set
nfa ↓′ s  = Nonempty ((Nfa.F nfa) ∩ (δ̂ nfa ⁅ Nfa.S nfa ⁆ s))


any : ∀{n} → (P : Fin n → Bool) → Bool
any {zero}  f = false
any {suc _} f = f fzero ∨ any λ x → f (fsuc x)

accepts : ∀{n} → Nfa n → Fin n → String → Bool
accepts nfa q []       = Nfa.F nfa ! q
accepts nfa q (c ∷ s) = any λ p → Nfa.δ nfa q c ! p ∧ accepts nfa p s

infix 10 _↓_
_↓_ : ∀{n} → Nfa n → String → Set
nfa ↓ s  = T (accepts nfa (Nfa.S nfa) s)


_↓?_ : ∀{n} → (nfa : Nfa n) → (s : String) → Dec (nfa ↓ s)
nfa ↓? s with accepts nfa (Nfa.S nfa) s
... | false = no (λ z → z)
... | true = yes tt

lem≤ : ∀{m n} → ¬ 1 + m ≤ n → m ≥ n
lem≤ {_} {zero} ¬p = z≤n
lem≤ {zero} {suc n} ¬p = ⊥-elim (¬p (s≤s z≤n))
lem≤ {suc m} {suc n} ¬p = s≤s (lem≤ (λ z → ¬p (s≤s z)))

concatNfa : ∀{n m} → Nfa n → Nfa m → Nfa (n + m)
concatNfa {n} {m} nfaL nfaR =
  record
    { S = inject+ m (Nfa.S nfaL)
    ; δ = δ
    ; F = ∅ ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (n + m) → Char → Subset (n + m)
    δ q c with toℕ q <? n
    δ q c | yes q<n with fromℕ≤ (q<n) ∈? Nfa.F nfaL
    δ q c | yes q<n | yes fin = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | yes q<n | no ¬fin = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++             ∅
    δ q c | no ¬q<n           =               ∅             ++ (Nfa.δ nfaR (reduce≥ q (lem≤ ¬q<n)) c)

unionNfa : ∀{n m} → Nfa n → Nfa m → Nfa (n + m)
unionNfa {n} {m} nfaL nfaR =
  record
    { S = inject+ m (Nfa.S nfaL)
    ; δ = δ
    ; F = (Nfa.F nfaL) ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (n + m) → Char → Subset (n + m)
    δ q c with toℕ q <? n
    δ q c | yes q<n with fromℕ≤ (q<n) ≟ Nfa.S nfaL
    δ q c | yes q<n | yes isS = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | yes q<n | no ¬isS = (Nfa.δ nfaL (fromℕ≤ q<n) c) ++             ∅
    δ q c | no ¬q<n           =               ∅             ++ (Nfa.δ nfaR (reduce≥ q (lem≤ ¬q<n)) c)

¬q=0→q≥1 : ∀{n}{q : Fin (suc n)} →  ¬ (q ≡ fzero) → toℕ q ≥ suc zero
¬q=0→q≥1 {n} {Data.Fin.0F} p = ⊥-elim (p refl)
¬q=0→q≥1 {n} {fsuc q} p = s≤s z≤n

starNfa : ∀{n} → Nfa n → Nfa (suc n)
starNfa nfa with any? T? (Nfa.F nfa)
starNfa {n} nfa | yes p =
  record
    { S = fzero
    ; δ = δ
    ; F = ⁅ fzero ⁆ ++ Nfa.F nfa
    }
  where
    δ : Fin (suc n) → Char → Subset (suc n)
    δ q c with q ≟ fzero
    ... | yes q≡0 = ∅ ++ (Nfa.δ nfa (Nfa.S nfa) c)
    ... | no ¬q≡0 with reduce≥ q (¬q=0→q≥1 ¬q≡0)
    ... | q' with q' ∈? Nfa.F nfa
    ... | yes fin = ∅ ++ (⁅ Nfa.S nfa ⁆ ∪ (Nfa.δ nfa q') c)
    ... | no ¬fin = ∅ ++                  (Nfa.δ nfa q') c
starNfa {suc n} nfa | no ¬p =
  record
    { S = fzero
    ; δ = λ _ _ → ⁅ fsuc fzero ⁆
    ; F = ⁅ fzero ⁆
    }


concat-closure : ∀{n m : ℕ} {s t : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → (nfaL ↓ s) × (nfaR ↓ t) ⇔ (concatNfa nfaL nfaR) ↓ (s ++ˢ t)
concat-closure  = record { to = to  ; from = from  }
  where
    to = {!   !}
    from  = {!   !}

union-closure : ∀{n m : ℕ} {s t : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → let union = unionNfa nfaL nfaR in
    (nfaL ↓ s) ⊎ (nfaR ↓ t) ⇔ ( union ↓ s × union ↓ t )
union-closure  = record { to = to  ; from = from  }
  where
    to = {!   !}
    from  = {!   !}
















--

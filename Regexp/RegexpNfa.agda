open import Equivalence
open import Data.Nat as ℕ using (ℕ; zero; suc; _<′_)
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F)
  renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong)
open import VecUtil
open import Induction.Nat
open import Induction.WellFounded

module RegexpNfa (Σ : Set) (_≟_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import String Σ using (String; _∷_; []; length) renaming (_++_ to _++ˢ_)
open import Nfa Σ hiding (Acc)
open import Regexp Σ

nfa-∅ : Nfa 1
nfa-∅ = record { S = 0F ; δ = λ _ _ → FullSet ; F = ∅ }

nfa-ε : Nfa 2
nfa-ε = record { S = 0F ; δ = λ _ _ → ⁅ 1F ⁆ ; F = ⁅ 0F ⁆ }

nfa-c : (c : Σ) → Nfa 3
nfa-c c = record { S = 0F ; δ = δ ; F = ⁅ 1F ⁆ }
  where
    δ : Fin 3 → Σ → Subset 3
    δ 0F k with k ≟ c
    ... | yes p = ⁅ 1F ⁆
    ... | no ¬p = ⁅ 2F ⁆
    δ _ _ = ⁅ 2F ⁆

extractOrL : ∀{a} → T(a Data.Bool.∨ false) → T a
extractOrL {false} z = z
extractOrL {true} _ = tt

nfa-∅-is-empty : (s : String) → ¬ (nfa-∅ ↓ s)
nfa-∅-is-empty (x ∷ s) r = ⊥-elim((nfa-∅-is-empty s) (extractOrL r))

nfa-ε-only-ε2 : (s : String) → ¬ (T (accepts nfa-ε 1F s))
nfa-ε-only-ε2 [] z = z
nfa-ε-only-ε2 (x ∷ s) z = ⊥-elim((nfa-ε-only-ε2 s) (extractOrL z))

nfa-ε-only-ε1 : (s : String) → s ≡ ε ⊎ ¬ (nfa-ε ↓ s)
nfa-ε-only-ε1 [] = inj₁ refl
nfa-ε-only-ε1 (x ∷ s) = inj₂ λ z → ⊥-elim (nfa-ε-only-ε2 s (extractOrL z))

nfa-ε-only-ε3 : (s : String) → ¬ (s ≡ ε) → ¬ (nfa-ε ↓ s)
nfa-ε-only-ε3 s neq with nfa-ε-only-ε1 s
nfa-ε-only-ε3 s neq | inj₁ x = λ _ → neq x
nfa-ε-only-ε3 s neq | inj₂ y = y

nfa-c-correct-to : (c : Σ) → nfa-c c ↓ (c ∷ [])
nfa-c-correct-to c with c ≟ c
nfa-c-correct-to c | yes p = tt
nfa-c-correct-to c | no ¬p = ¬p refl

nfa-c-correct-from2 : ∀{c s} → ¬ (T (accepts (nfa-c c) 2F s ))
nfa-c-correct-from2 {c} {x ∷ s} d = ⊥-elim (nfa-c-correct-from2 {c} {s} (extractOrL d))

nfa-c-correct-from : ∀{c}{s} → nfa-c c ↓ s → s ≡ (c ∷ [])
nfa-c-correct-from {c} {x ∷ []} d with x ≟ c
nfa-c-correct-from {c} {x ∷ []} tt | yes p = cong (_∷ []) p
nfa-c-correct-from {c} {x ∷ x₁ ∷ s} d with x ≟ c
nfa-c-correct-from {c} {x ∷ x₁ ∷ s} d | yes p = ⊥-elim(nfa-c-correct-from2 {c} {x ∷ x₁ ∷ s} d)
nfa-c-correct-from {c} {x ∷ x₁ ∷ s} d | no ¬p = ⊥-elim(nfa-c-correct-from2 {c} {x ∷ x₁ ∷ s} d)

only-ε∈⟨ε⟩ : (s : String) → ¬ (s ≡ ε) → ¬ (s ∈ ⟨ε⟩)
only-ε∈⟨ε⟩ [] neq = λ _ → neq refl
only-ε∈⟨ε⟩ (x ∷ s) neq = λ ()

RegExp->Nfa : (R : RegExp)
    → ∃₂ λ (n : ℕ) (nfa : Nfa n)
      → ∀ (s : String)
      → s ∈ R ⇔ nfa ↓ s
RegExp->Nfa ⟨⟩ = 1 , nfa-∅ , λ s →  (λ x → contradiction x λ ()) IFF (λ x → contradiction x (nfa-∅-is-empty s))
RegExp->Nfa ⟨ε⟩ = 2 , nfa-ε , λ { [] → (λ _ → tt) IFF (λ _ → in-ε)
                          ; (x ∷ s) → (λ x₁ → ⊥-elim ((only-ε∈⟨ε⟩ (x ∷ s) (λ ())) x₁))
                                      IFF
                                      (λ x₁ → ⊥-elim (nfa-ε-only-ε3 (x ∷ s) (λ ()) x₁))
                          }
RegExp->Nfa (Atom c) = 3 , nfa-c c , λ{  [] → (λ ()) IFF (λ ()); (x ∷ s) → left IFF right }
  where
    left : ∀{x}{s} → (x ∷ s) ∈ Atom c → nfa-c c ↓ (x ∷ s)
    left (in-c c) = nfa-c-correct-to c
    right : ∀{x}{s} → nfa-c c ↓ (x ∷ s) → (x ∷ s) ∈ Atom c
    right {x}{s} d rewrite nfa-c-correct-from {c} {x ∷ s} d = in-c c
RegExp->Nfa (R RegExp.+ F) with RegExp->Nfa R | RegExp->Nfa F
... | n , nfaL , acL | m , nfaR , acR =
  1 ℕ.+ n ℕ.+ m , unionNfa nfaL nfaR , λ s → to s IFF (from s)
  where
    to :  (s : String) → s ∈ (R + F) → T (accepts (unionNfa nfaL nfaR) 0F s)
    to s (in+l inl) = union-cl-l {n}{m}{s} (_⇔_.to (acL s) inl)
    to s (in+r inr) = union-cl-r {n}{m}{s} (_⇔_.to (acR s) inr)

    from : (s : String) → unionNfa nfaL nfaR ↓ s → s ∈ (R + F)
    from s d with union-cl-inverse {n} {m} {s} d
    from s d | inj₁ y = in+l (_⇔_.from (acL s) y)
    from s d | inj₂ y = in+r (_⇔_.from (acR s) y)

RegExp->Nfa (R · F) with RegExp->Nfa R | RegExp->Nfa F
... | n , nfaL , acL | m , nfaR , acR =
  1 ℕ.+ n ℕ.+ m , concatNfa nfaL nfaR , λ s → to s IFF (from s)
  where
    to : (s : String) → s ∈ (R · F) → (concatNfa nfaL nfaR) ↓ s
    to _ (in-· {s} {t} inL inR) = concat-closure {n} {m} {s} {t}  (_⇔_.to (acL s) inL , _⇔_.to (acR t) inR  )

    from : (s : String) → (concatNfa nfaL nfaR) ↓ s → s ∈ (R · F)
    from s d with concat-closure-inv {n}{m}{s} d
    from s d | u , v , eq , dL , dR rewrite eq = in-· (_⇔_.from (acL u) dL) (_⇔_.from (acR v) dR)
RegExp->Nfa (R *) with RegExp->Nfa R
... | n , nfa , IH =
  1 ℕ.+ n , starNfa nfa , λ s → (to s) IFF (from s)
  where
    to : (s : String) → s ∈ (R *) → starNfa nfa ↓ s
    to _ in-*1 = tt
    to _ (in-*2 {s} {t} l r) with to t r
    ... | u = star-closure {n}{s}{t} (_⇔_.to (IH s) l , u)

    ∷-++-length-< : ∀{x s u v} → (x ∷ s) ≡ (x ∷ u) ++ˢ v → length v ℕ.<′ length (x ∷ s)
    ∷-++-length-< {x} {.v} {[]} {v} refl = ℕ.≤′-refl
    ∷-++-length-< {x} {x₂ ∷ .(u ++ˢ v)} {.x₂ ∷ u} {v} refl = ℕ.≤′-step (∷-++-length-< {x₂} {_}{u}{v} refl)

    star-from-WF : (s : String)
      → starNfa nfa ↓ s
      → Acc _<′_ (length s)
      → s ∈ (R *)
    star-from-WF [] _ _ = in-*1
    star-from-WF (x ∷ s) ds (acc go) with star-closure-inverse {n} {x} {s} ds
    ... | u , v , eq , fl , nxt rewrite eq = in-*2 (_⇔_.from (IH (x ∷ u)) fl) (star-from-WF v nxt (go (length v) (∷-++-length-< eq)))

    from : (s : String)
      → starNfa nfa ↓ s
      → s ∈ (R *)
    from s ds = star-from-WF s ds (<′-wellFounded (length s))

    -- {-# TERMINATING #-}
    -- star-from : ∀{n} → (nfa : Nfa n) → (R : RegExp) → ((s : String) → s ∈ R ⇔ nfa ↓ s) → (s : String) → starNfa nfa ↓ s → s ∈ (R *)
    -- star-from _ _ _ [] ds = in-*1
    -- star-from {n} nfa R IH (x ∷ s) ds with star-closure-inverse {n} {x} {s} ds
    -- ... | u , v , eq , fl , nxt rewrite eq = in-*2 (_⇔_.from (IH (x ∷ u)) fl) (star-from nfa R IH v nxt)

--

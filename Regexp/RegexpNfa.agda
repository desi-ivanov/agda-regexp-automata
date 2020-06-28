open import Equivalence
open import Data.Nat as ℕ using (ℕ; zero; suc; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F)
  renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Bool using (Bool; false; true; not; T; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong)
open import VecUtil hiding (_∈?_; _∈_)
open import Induction.Nat
open import Induction.WellFounded

module RegexpNfa (Σ : Set) (_≟_ : (a : Σ) → (b : Σ) → Dec (a ≡ b)) where
open import String Σ using (String; _∷_; []; length) renaming (_++_ to _++ˢ_)
open import Nfa Σ hiding (Acc; ε)
open import Regexp Σ

∅-nfa : Nfa 1
∅-nfa = record { S = 0F ; δ = λ _ _ → ⁅ 0F ⁆ ; F = ∅ }

ε-nfa : Nfa 2
ε-nfa = record { S = 0F ; δ = λ _ _ → ⁅ 1F ⁆ ; F = ⁅ 0F ⁆ }

c-nfa : (c : Σ) → Nfa 3
c-nfa c = record { S = 0F ; δ = δ ; F = ⁅ 1F ⁆ }
  where
    δ : Fin 3 → Σ → Subset 3
    δ 0F k with k ≟ c
    ... | yes p = ⁅ 1F ⁆
    ... | no ¬p = ⁅ 2F ⁆
    δ _ _ = ⁅ 2F ⁆

extractOrL : ∀{a} → T(a ∨ false) → T a
extractOrL {false} z = z
extractOrL {true} _ = tt

∅-nfa-is-empty : (s : String) → ¬ (∅-nfa ↓ s)
∅-nfa-is-empty (x ∷ s) r = ⊥-elim (∅-nfa-is-empty s (extractOrL r))

1F-is-error : (s : String) → ¬ (T (accepts ε-nfa 1F s))
1F-is-error [] z = z
1F-is-error (x ∷ s) z = ⊥-elim (1F-is-error s (extractOrL z))

nfaε-correct : (s : String) → ¬ (s ≡ ε) → ¬ (ε-nfa ↓ s)
nfaε-correct [] a b = a refl
nfaε-correct (x ∷ s) a b = 1F-is-error s (extractOrL b)

2F-is-error : ∀{c s} → ¬ (T (accepts (c-nfa c) 2F s ))
2F-is-error {c} {x ∷ s} d =
  contradiction (extractOrL d) (2F-is-error {c} {s})

nfac-correct : ∀{c}{s} → c-nfa c ↓ s → s ≡ (c ∷ [])
nfac-correct {c} {x ∷ []} d with x ≟ c
... | yes p = cong (_∷ []) p
nfac-correct {c} {x ∷ y ∷ s} d with x ≟ c
... | yes p = contradiction d (2F-is-error {c} {x ∷ y ∷ s})
... | no ¬p = contradiction d (2F-is-error {c} {x ∷ y ∷ s})


toNFA : (R : RegExp)
    → ∃₂ λ (n : ℕ) (nfa : Nfa n)
      → ∀ (s : String)
      → s ∈ R ⇔ nfa ↓ s
toNFA ⟨⟩ = 1 , ∅-nfa , λ s → record
    { to = λ ()
    ; from = λ nfa↓s → ⊥-elim (∅-nfa-is-empty s nfa↓s)
    }
toNFA ⟨ε⟩ = 2 , ε-nfa , iff
  where
  iff : (s : String)
    → s ∈ ⟨ε⟩ ⇔ ε-nfa ↓ s
  iff [] = record { to = λ _ → tt ; from = λ _ → in-ε }
  iff (x ∷ s) = record
    { to = λ ()
    ; from = λ nfa↓xs → ⊥-elim (nfaε-correct (x ∷ s) (λ ()) nfa↓xs )
    }
toNFA (Atom c) = 3 , c-nfa c , λ s → record { to = to ; from = from }
  where
  to : ∀{s}
    → s ∈ Atom c
    → c-nfa c ↓ s
  to (in-c c) with c ≟ c
  ... | yes p = tt
  ... | no ¬p = ¬p refl

  from : ∀{s}
    → c-nfa c ↓ s
    → s ∈ Atom c
  from {s} nfa↓s rewrite nfac-correct {c} {s} nfa↓s = in-c c

toNFA (R + F) with toNFA R | toNFA F
... | n , A , w∈R⇔A↓w | m , B , w∈F⇔B↓w =
  suc n ℕ.+ m , union A B , λ s → to s IFF (from s)
  where
  to :  (s : String)
    → s ∈ (R + F)
    → union A B ↓ s
  to s (in+l s∈R) = _⇔_.to (union-correct s) (inj₁ (_⇔_.to (w∈R⇔A↓w s) s∈R))
  to s (in+r s∈F) = _⇔_.to (union-correct s) (inj₂ (_⇔_.to (w∈F⇔B↓w s) s∈F))

  from : (s : String)
    → union A B ↓ s
    → s ∈ (R + F)
  from s A∪B↓s with _⇔_.from (union-correct s) A∪B↓s
  ...| inj₁ A↓s = in+l (_⇔_.from (w∈R⇔A↓w s) A↓s)
  ...| inj₂ B↓s = in+r (_⇔_.from (w∈F⇔B↓w s) B↓s)

toNFA (R · F) with toNFA R | toNFA F
... | n , A , w∈R⇔A↓w | m , B , w∈F⇔B↓w =
  suc n ℕ.+ m , concat A B , λ s → to s IFF (from s)
  where
  to : (s : String)
    → s ∈ (R · F)
    → concat A B ↓ s
  to _ (in-· {u} {v} u∈R v∈F) =
    _⇔_.from (concat-correct (u ++ˢ v))
      (u , v , refl , _⇔_.to (w∈R⇔A↓w u) u∈R , _⇔_.to (w∈F⇔B↓w v) v∈F)

  from : (s : String)
    → concat A B ↓ s
    → s ∈ (R · F)
  from s AB↓s with _⇔_.to (concat-correct s) AB↓s
  ... | u , v , s≡uv , A↓u , B↓v rewrite s≡uv =
    in-· (_⇔_.from (w∈R⇔A↓w u) A↓u) (_⇔_.from (w∈F⇔B↓w v) B↓v)

toNFA (R *) with toNFA R
... | n , A , s∈R⇔A↓s =
  suc n , star A , λ s → (to s) IFF (from s)
  where
  to : (s : String)
    → s ∈ (R *)
    → star A ↓ s
  to _ in-*1 = tt
  to _ (in-*2 {u} {v} u∈R v∈R*) =
    star-correct1 {_} {u} {v} (_⇔_.to (s∈R⇔A↓s u) u∈R , (to v v∈R*))

  lenv<lenau++v : ∀{u v} → (a : Σ) → length v <′ length (a ∷ u ++ˢ v)
  lenv<lenau++v {[]} {v} a = ≤′-refl
  lenv<lenau++v {u ∷ us} {v} a = ≤′-step (lenv<lenau++v u)

  star-from-WF : (s : String)
    → star A ↓ s
    → Acc _<′_ (length s)
    → s ∈ (R *)
  star-from-WF [] _ _ = in-*1
  star-from-WF (a ∷ s) A*↓as (acc go) with star-correct2 a s A*↓as
  ... | u , v , as≡uv , A↓au , A*↓v rewrite as≡uv =
    in-*2 (_⇔_.from (s∈R⇔A↓s (a ∷ u)) A↓au)
        (star-from-WF v A*↓v (go (length v) (lenv<lenau++v a)))

  from : (s : String)
    → star A ↓ s
    → s ∈ (R *)
  from s A*↓s = star-from-WF s A*↓s (<′-wellFounded (length s))

    -- {-# TERMINATING #-}
    -- star-from : ∀{n} → (nfa : Nfa n) → (R : RegExp) → ((s : String) → s ∈ R ⇔ nfa ↓ s) → (s : String) → star nfa ↓ s → s ∈ (R *)
    -- star-from _ _ _ [] ds = in-*1
    -- star-from {n} nfa R iff (x ∷ s) ds with star-correct2 {n} {x} {s} ds
    -- ... | u , v , as≡uv , fl , nxt rewrite as≡uv = in-*2 (_⇔_.from (iff (x ∷ u)) fl) (star-from nfa R IH v nxt)


_∈?_ : (v : String) → (F : RegExp) → Dec (v ∈ F)
v ∈? F with toNFA F
... | _ , A , v∈F⇔A↓v with A ↓? v
... | yes A↓v = yes (_⇔_.from (v∈F⇔A↓v v) A↓v)
... | no ¬A↓v = no λ v∈F → contradiction (_⇔_.to (v∈F⇔A↓v v) v∈F) ¬A↓v

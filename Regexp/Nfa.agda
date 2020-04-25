module Nfa where
open import Data.Char as Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≥_; _<?_; _≤?_; s≤s; z≤n)
open import Data.Fin
  using (Fin; inject+; 0F; raise)
  renaming (zero to fzero; suc to fsuc; _<_ to _<f_; _<?_ to _<f?_)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; _⊆_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Fin.Subset.Properties using (x∈p∪q⁺; x∈p∪q⁻)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T; not)
open import Data.Bool.Properties using (T?)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import String using (String; _∷_; []; ++-idˡ; ++-idʳ; take; drop; ++-assoc; length) renaming (_++_ to _++ˢ_)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v) hiding (concat; splitAt; take; drop)
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any using (index) renaming (any to any?)
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary.Negation using (contradiction)

record Nfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Subset n
    F : Subset n

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

-- Alternative 1: Acceptance by Intersection of final states with extendend delta
δ̂ : ∀{n} → Nfa n → (Subset n) → String → (Subset n)
δ̂ {n} nfa qs [] = qs
δ̂ {n} nfa qs (x ∷ s) = δ̂ nfa (onestep qs x) s
  where
    onestep : (Subset n) → Char → (Subset n)
    onestep qs c = U (mapS qs (λ q → Nfa.δ nfa q c) ∅)
infix 10 _↓′_
_↓′_ : ∀{n} → Nfa n → String → Set
nfa ↓′ s  = Nonempty ((Nfa.F nfa) ∩ (δ̂ nfa ⁅ Nfa.S nfa ⁆ s))

-- Alternative 2: Acceptance by States path
data Acc {n} : Nfa n → Fin n → String → Set where
  Acc[] : ∀{q}{nfa} → q ∈ Nfa.F nfa → Acc nfa q []
  Acc∷ : ∀{p x xs q nfa} → p ∈ Nfa.δ nfa q x → Acc nfa p xs → Acc nfa q (x ∷ xs)
infix 10 _↓′′_
_↓′′_ : ∀{n} → Nfa n → String → Set
nfa ↓′′ s = Acc nfa (Nfa.S nfa) s

--------------------------------------------------------------------------------
-- Union, Concatenation and Star operations on Nfa

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero    i        = inj₂ i
splitAt (suc m) fzero    = inj₁ fzero
splitAt (suc m) (fsuc i) = Data.Sum.map fsuc (λ x → x) (splitAt m i)

concatNfa : ∀{n m} → Nfa n → Nfa m → Nfa (1 + n + m)
concatNfa {n} {m} nfaL nfaR =
  record
    { S = fzero
    ; δ = δ
    ; F = F
    }
  where
    δ : Fin (1 + n + m) → Char → Subset (1 + n + m)
    δ q c with splitAt 1 q
    δ q c | inj₁ z with Nfa.S nfaL ∈? Nfa.F nfaL
    δ q c | inj₁ z | yes isf           = ∅ {1} ++ (Nfa.δ nfaL (Nfa.S nfaL) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₁ z | no ¬isf           = ∅ {1} ++ (Nfa.δ nfaL (Nfa.S nfaL) c) ++             ∅
    δ q c | inj₂ mn with splitAt n mn
    δ q c | inj₂ mn | inj₁ l with l ∈? Nfa.F nfaL
    δ q c | inj₂ mn | inj₁ l | yes isf = ∅ {1} ++ (Nfa.δ nfaL l c)            ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₂ mn | inj₁ l | no ¬isf = ∅ {1} ++ (Nfa.δ nfaL l c)            ++             ∅
    δ q c | inj₂ mn | inj₂ r           = ∅ {1} ++             ∅               ++ (Nfa.δ nfaR r c)

    F : Subset (1 + n + m)
    F with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
    F | yes ε∈l | yes ε∈r = true  ∷v Nfa.F nfaL ++ Nfa.F nfaR
    F | yes ε∈l | no ¬ε∈r = ∅ {1} ++ ∅          ++ Nfa.F nfaR
    F | no ¬ε∈l | yes ε∈r = ∅ {1} ++ Nfa.F nfaL ++ Nfa.F nfaR
    F | no ¬ε∈l | no ¬ε∈r = ∅ {1} ++ ∅          ++ Nfa.F nfaR

unionNfa : ∀{n m} → Nfa n → Nfa m → Nfa (1 + n + m)
unionNfa {n} {m} nfaL nfaR =
  record
    { S = fzero
    ; δ = δ
    ; F = sf ++ (Nfa.F nfaL) ++ (Nfa.F nfaR)
    }
  where
    δ : Fin (1 + n + m) → Char → Subset (1 + n + m)
    δ q c  with splitAt 1 q
    δ q c | inj₁ z          = ∅ {1} ++ (Nfa.δ nfaL (Nfa.S nfaL) c) ++ (Nfa.δ nfaR (Nfa.S nfaR) c)
    δ q c | inj₂ f with splitAt n f
    δ q c | inj₂ f | inj₁ l = ∅ {1} ++ (Nfa.δ nfaL l c)            ++ ∅
    δ q c | inj₂ f | inj₂ r = ∅ {1} ++ ∅                           ++ (Nfa.δ nfaR r c)

    sf : Subset 1
    sf with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
    sf | no ¬ε∈l | no ¬ε∈r = false ∷v []v
    sf | _     | _         = true ∷v []v

starNfa : ∀{n} → Nfa n → Nfa (1 + n)
starNfa {n} nfa =
  record
    { S = fzero
    ; δ = δ
    ; F = ⁅ fzero ⁆ ++ Nfa.F nfa
    }
  where
    δ : Fin (1 + n) → Char → Subset (1 + n)
    δ q c with splitAt 1 q
    δ q c | inj₁ z = ∅ ++ (Nfa.δ nfa (Nfa.S nfa) c)
    δ q c | inj₂ p with p ∈? Nfa.F nfa
    δ q c | inj₂ p | yes isf = ∅ ++ ((Nfa.δ nfa (Nfa.S nfa) c) ∪ (Nfa.δ nfa p) c)
    δ q c | inj₂ p | no ¬isf = ∅ ++                  (Nfa.δ nfa p) c

--------------------------------------------------------------------------------
-- Correctnes of Union, Star and Concatenation constructions

injectOrR : ∀{u b} → T(b) → T(u ∨ b)
injectOrR {false} {true} tt = tt
injectOrR {true} {true} tt = tt

injectOrL : ∀{u b} → T(u) → T(u ∨ b)
injectOrL {true} {true} t = tt
injectOrL {true} {false} t = tt

splitOr : ∀{u b} → T(u ∨ b) → T u ⊎ T b
splitOr {false} {true} t = inj₂ tt
splitOr {true} {false} t = inj₁ tt
splitOr {true} {true} t = inj₁ tt

anyToExists : ∀{n} {f : Fin n → Bool} → T (any f) → ∃[ i ] T(f i)
anyToExists {suc n} {f} t with splitOr {f 0F} {any (λ x → f (fsuc x))} t
anyToExists {suc n} {f} t | inj₁ x = 0F , x
anyToExists {suc n} {f} t | inj₂ y with anyToExists {_} {λ u → f (fsuc u)} y
anyToExists {suc n} {f} t | inj₂ y | fst , snd = fsuc fst , snd

fromExists : ∀{n} {f : Fin n → Bool} → ∃[ i ] T(f i) → T(any f)
fromExists {_} {f} (0F , snd) = injectOrL snd
fromExists {_} {f} (fsuc fst , snd) = injectOrR (fromExists ( fst , snd ))

splitand : ∀{a b} → T (a ∧ b) → T a × T b
splitand {true} {true} tt = tt , tt

biglemma : ∀{n x xs q} {nfa : Nfa n}
  → T (accepts nfa q (x ∷ xs))
  →  ∃[ p ] (T ((Nfa.δ nfa q x) ! p) × T (accepts nfa p xs))
biglemma {n} {x} {xs} {q} {nfa} p with anyToExists {n} {λ z → (Nfa.δ nfa q x) ! z ∧ accepts nfa z xs} p
... | fst , snd = fst , (splitand {(Nfa.δ nfa q x) ! fst} {accepts nfa fst xs} snd)

lem1ˡ : ∀{n m} → (v : Vec Bool n) → (w : Vec Bool m)
  → (p : Fin n)
  → T (v ! p)
  → T ((v ++ w) ! (inject+ m p))
lem1ˡ v w p x = subst (λ v → T v) (sym (lookup-++ˡ v w p)) x

lem1ʳ : ∀{n m} → (v : Vec Bool n) → (w : Vec Bool m)
  → (p : Fin m)
  → T (w ! p)
  → T ((v ++ w) ! (raise n p))
lem1ʳ v w p x = subst (λ v → T v) (sym (lookup-++ʳ v w p)) x

lem3 : ∀{n} {w} {v : Subset n} → v [ w ]= true → T (v ! w)
lem3 t = subst (λ v → T v) (sym (s!i≡s[i] t)) tt

joinand : ∀{a} {b} → T a → T b → T (a ∧ b)
joinand {true} {true} _ _ = tt

splitAt-inject+ : ∀ m n i → splitAt m (inject+ n i) ≡ inj₁ i
splitAt-inject+ (suc m) n fzero = refl
splitAt-inject+ (suc m) n (fsuc i) rewrite splitAt-inject+ m n i = refl

splitAt-raise : ∀ m n i → splitAt m (raise {n} m i) ≡ inj₂ i
splitAt-raise zero    n i = refl
splitAt-raise (suc m) n i rewrite splitAt-raise m n i = refl

lemmaLookupT : ∀{n} {v : Vec Bool n} {w} → T(v ! w) → v [ w ]= true
lemmaLookupT {_} {x ∷v v} {0F} t with (x ∷v v) ! 0F
lemmaLookupT {_} {x ∷v v} {0F} t | true = here
lemmaLookupT {_} {x ∷v v} {fsuc w} t = there (lemmaLookupT t)

injectSetUnionʳ : ∀{n} {q} {set : Subset n} → T(set ! q) → (inj : Subset n) → T((set ∪ inj) ! q)
injectSetUnionʳ {n} {q} {set} t inj with set ! q  | v[i]=v!i set q
... | true | u =  subst (λ y → T y) (sym (s!i≡s[i] (x∈p∪q⁺ {_}{set}{inj} (inj₁ u)))) tt

injectSetUnionˡ : ∀{n} {q} {set : Subset n} → T(set ! q) → (inj : Subset n) → T((inj ∪ set) ! q)
injectSetUnionˡ {n} {q} {set} t inj with set ! q  | v[i]=v!i set q
... | true | u =  subst (λ y → T y) (sym (s!i≡s[i] (x∈p∪q⁺ {_}{inj} (inj₂ u)))) tt

lem0 : ∀{n} → (q : Fin (suc n)) (vec : Subset n) → T ((false ∷v vec) ! q) → 0F Data.Fin.< q
lem0 (fsuc q) vec t = s≤s z≤n

lem2 : ∀{n} → (q : Fin (suc n)) → 0F Data.Fin.< q → ∃[ p ] (q ≡ fsuc p)
lem2 (fsuc q) _ = q , refl

lem5 : ∀{n} {q} (ss : Subset n) → T (ss ! q) → ss ! q ≡ true
lem5 {_} {0F} (true ∷v ss) t = refl
lem5 {_} {fsuc q} (x ∷v ss) t = lem5 ss t

lem11 : ∀{n} {t : Fin n} → ¬(T(∅{n} ! t))
lem11 {suc n} {fsuc t} d = lem11 {n}{t} d

lem7 : ∀{n m} → (q : Fin (suc (n + m))) (ss : Subset n) → T ((false ∷v ss ++ ∅ {m}) ! q) → ∃[ p ](q ≡ fsuc (inject+ m p) × T(ss ! p))
lem7 {.0} (fsuc q) []v acc = ⊥-elim(lem11 {_}{fsuc q} acc)
lem7 {.(suc _)}  Data.Fin.1F (true ∷v ss) tt = 0F , refl , tt
lem7 {.(suc _)} (fsuc (fsuc q)) (z ∷v ss) acc with lem7 {_} (fsuc q) ss acc
lem7 {.(suc _)} (fsuc (fsuc q)) (z ∷v ss) acc | fst , snd , trd = fsuc fst , cong fsuc snd , trd

lem13 : ∀{n} {t : Fin (n + 0F)} → ¬(T((∅{n} ++ []v) ! t))
lem13 {suc n} {fsuc t} ds = lem13{n}{t} ds

lem8 : ∀{n m} → (q : Fin (suc (n + m))) (ss : Subset m) → T ((false ∷v ∅ {n} ++ ss) ! q) → ∃[ p ](q ≡ fsuc (raise n p) × T(ss ! p))
lem8 {suc n} {.0} q []v ac = ⊥-elim(lem13 {_}{q} ac)
lem8 {0F} (fsuc q) (x ∷v ss) ac = q , refl , ac
lem8 {suc n} {m} (fsuc q) (ss) ac with lem8 {n} q (ss) ac
... | fst , snd , trd  = fst , cong fsuc snd , trd

lem10 : ∀{n m} → (q : Fin (suc (n + m))) (ss1 : Subset n ) (ss2 : Subset m) → T ((false ∷v ss1 ++ ss2) ! q)
        → ∃[ p ](q ≡ fsuc (inject+ m p) × T(ss1 ! p))
        ⊎ ∃[ p ](q ≡ fsuc (raise n p)   × T(ss2 ! p))
lem10 {0F} {m} (fsuc q) []v ss2 acc = inj₂ (q , refl , acc)
lem10 {suc n} {m} Data.Fin.1F (true ∷v ss1) ss2 tt = inj₁ (0F , refl , tt)
lem10 {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc with lem10 {n}{m}(fsuc q) ss1 ss2 acc
lem10 {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc | inj₁ (fst , snd , trd) = inj₁ (fsuc fst , cong fsuc snd , trd )
lem10 {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc | inj₂ (fst , snd , trd) = inj₂ (fst , cong fsuc snd , trd )

lem12 : ∀{n}{q : Fin n} {s} → s [ q ]= true → T(s ! q)
lem12 here = tt
lem12 (there ac) = lem12 ac

lem6 : ∀{n} → (a b : Subset n) (q : Fin n) → T((a ∪ b) ! q)  → T (a ! q) ⊎ T (b ! q)
lem6 {n} a b q ac with x∈p∪q⁻ a b (lemmaLookupT {n}{a ∪ b} ac)
lem6 {n} a b q ac | inj₁ x = inj₁ (lem12 x)
lem6 {n} a b q ac | inj₂ x = inj₂ (lem12 x)

lem9 : ∀{n}{v : Subset n} {t : Fin n} → v [ t ]= true → T (v ! t)
lem9 {_} {true ∷v v} {0F} d = tt
lem9 {_} {x ∷v v} {fsuc t} (there d) = lem9 d


union-accepts-left : ∀{n m} {s} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T (accepts nfaL q s)
  → T (accepts (unionNfa nfaL nfaR) (raise 1 (inject+ m q)) s)
union-accepts-left {n} {m} {[]} {q} {nfaL} {nfaR} x with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR | lem1ˡ (Nfa.F nfaL) (Nfa.F nfaR) q x
...| yes _ | yes _ | v = v
...| yes _ | no  _ | v = v
...| no  _ | yes _ | v = v
...| no  _ | no  _ | v = v
union-accepts-left {n} {m} {c ∷ s} {q} {nfaL} {nfaR} x with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR | splitAt n (inject+ m q) | splitAt-inject+ n m q
union-accepts-left {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | yes p | yes p₁ | inj₁ q | refl with biglemma {n}{c}{s} x
... | w , v , t with union-accepts-left {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ˡ {n}{m} (Nfa.δ nfaL q c) ∅ w (lem3 {n}{w}{Nfa.δ nfaL q c} (lemmaLookupT v))
... | u | i = fromExists (inject+ m w , (joinand i u))
union-accepts-left {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | yes p | no ¬p | inj₁ q | refl with biglemma {n}{c}{s} x
... | w , v , t with union-accepts-left {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ˡ {n}{m} (Nfa.δ nfaL q c) ∅ w (lem3 {n}{w}{Nfa.δ nfaL q c} (lemmaLookupT v))
... | u | i = fromExists (inject+ m w , (joinand i u))
union-accepts-left {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | no ¬p | yes p | inj₁ q | refl with biglemma {n}{c}{s} x
... | w , v , t with union-accepts-left {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ˡ {n}{m} (Nfa.δ nfaL q c) ∅ w (lem3 {n}{w}{Nfa.δ nfaL q c} (lemmaLookupT v))
... | u | i = fromExists (inject+ m w , (joinand i u))
union-accepts-left {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | no ¬p | no ¬p₁ | inj₁ q | refl with biglemma {n}{c}{s} x
... | w , v , t with union-accepts-left {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ˡ {n}{m} (Nfa.δ nfaL q c) ∅ w (lem3 {n}{w}{Nfa.δ nfaL q c} (lemmaLookupT v))
... | u | i = fromExists (inject+ m w , (joinand i u))

union-accepts-right : ∀{n m} {s} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T (accepts nfaR q s)
  → T (accepts (unionNfa nfaL nfaR) (raise (1 + n) q) s)
union-accepts-right {n} {m} {[]} {q} {nfaL} {nfaR} p with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR | lem1ʳ (Nfa.F nfaL) (Nfa.F nfaR) q p
... | yes _ | yes _ | v = v
... | yes _ | no  _ | v = v
... | no  _ | yes _ | v = v
... | no  _ | no  _ | v = v
union-accepts-right {n} {m} {c ∷ s} {q} {nfaL} {nfaR} x with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR | splitAt n (raise n q) | splitAt-raise n m q
union-accepts-right {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | yes p | yes p₁ | inj₂ q | refl with biglemma {m}{c}{s} x
... | w , v , t with union-accepts-right {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ʳ {n}{m} ∅ (Nfa.δ nfaR q c) w (lem3 {m}{w}{Nfa.δ nfaR q c} (lemmaLookupT v))
... | u | i = fromExists (raise n w , (joinand i u))
union-accepts-right {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | yes p | no ¬p | inj₂ q | refl with biglemma {m}{c}{s} x
... | w , v , t with union-accepts-right {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ʳ {n}{m} ∅ (Nfa.δ nfaR q c) w (lem3 {m}{w}{Nfa.δ nfaR q c} (lemmaLookupT v))
... | u | i = fromExists (raise n w , (joinand i u))
union-accepts-right {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | no ¬p | yes p | inj₂ q | refl with biglemma {m}{c}{s} x
... | w , v , t with union-accepts-right {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ʳ {n}{m} ∅ (Nfa.δ nfaR q c) w (lem3 {m}{w}{Nfa.δ nfaR q c} (lemmaLookupT v))
... | u | i = fromExists (raise n w , (joinand i u))
union-accepts-right {n} {m} {c ∷ s} {.q} {nfaL} {nfaR} x | no ¬p | no ¬p₁ | inj₂ q | refl with biglemma {m}{c}{s} x
... | w , v , t with union-accepts-right {n}{m}{s}{w}{nfaL}{nfaR} t
                | lem1ʳ {n}{m} ∅ (Nfa.δ nfaR q c) w (lem3 {m}{w}{Nfa.δ nfaR q c} (lemmaLookupT v))
... | u | i = fromExists (raise n w , (joinand i u))

union-cl-l : ∀{n m : ℕ} {s : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → nfaL ↓ s → unionNfa nfaL nfaR ↓ s
union-cl-l {n} {m} {[]} {nfaL} {nfaR} p with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
... | yes _  | yes _ = tt
... | yes _  | no  _ = tt
... | no  _  | yes _ = tt
... | no  ¬p | no  _ = ⊥-elim (¬p (lemmaLookupT p))
union-cl-l {n} {m} {c ∷ s} {nfaL} {nfaR} p with biglemma {n} {c} {s} p
union-cl-l {n} {m} {c ∷ s} {nfaL} {nfaR} p | w , t , f   with union-accepts-left {n}{m}{s}{w}{nfaL}{nfaR} f
... | ur with lem1ˡ (Nfa.δ nfaL (Nfa.S nfaL) c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = fromExists ((inject+ m w) , (joinand pur ur))

union-cl-r : ∀{n m : ℕ} {s : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → nfaR ↓ s → unionNfa nfaL nfaR ↓ s
union-cl-r {n} {m} {[]} {nfaL} {nfaR} p with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
... | yes _ | yes _ = tt
... | yes _ | no  _ = tt
... | no  _ | yes _ = tt
... | no  _ | no ¬p = ⊥-elim (¬p (lemmaLookupT p))
union-cl-r {n} {m} {c ∷ s} {nfaL} {nfaR} p with  biglemma {m} {c} {s} p
... | w , t , f with union-accepts-right {n}{m}{s}{w}{nfaL}{nfaR} f
... | ur with lem1ʳ (Nfa.δ nfaL (Nfa.S nfaL) c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = fromExists ((raise n w) , (joinand pur ur))

concat-right-preserved : ∀{n m : ℕ} {v : String} {p}{nfaL : Nfa n} {nfaR : Nfa m}
  → T(accepts nfaR p v)
  → T(accepts (concatNfa nfaL nfaR) (raise 1 (raise n p)) v)
concat-right-preserved {n} {m} {[]} {p} {nfaL} {nfaR} acc  with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
...| yes _ | yes _ = lem1ʳ (Nfa.F nfaL) (Nfa.F nfaR) p acc
...| no  _ | yes _ = lem1ʳ (Nfa.F nfaL) (Nfa.F nfaR) p acc
...| yes _ | no  _ = lem1ʳ (∅ {n}) (Nfa.F nfaR) p acc
...| no  _ | no  _ = lem1ʳ (∅ {n}) (Nfa.F nfaR) p acc
concat-right-preserved {n} {m} {c ∷ v} {p} {nfaL} {nfaR} acc with  biglemma {m}{c}{v} acc
... | w , t , f with splitAt n (raise n p) | splitAt-raise n m p
concat-right-preserved {n} {m} {c ∷ v} {.y} {nfaL} {nfaR} acc | w , t , f | inj₂ y | refl with  concat-right-preserved {_}{_}{v}{w}{nfaL}{nfaR} f
... | ind  with lem1ʳ (∅ {1 + n}) (Nfa.δ nfaR y c) w t
... | pur = fromExists (raise n w , joinand pur ind)

concat-inductive-left : ∀{n m : ℕ} {s v : String} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T(accepts nfaL q s) × nfaR ↓ v
  → T(accepts (concatNfa nfaL nfaR) (raise 1 (inject+ m q)) (s ++ˢ v))
concat-inductive-left {n} {m} {[]} {[]} {q} {nfaL} {nfaR} (fst , snd) with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
...| yes ε∈l | yes ε∈r = lem1ˡ (Nfa.F nfaL) (Nfa.F nfaR) q fst
...| no ¬ε∈l | yes ε∈r = lem1ˡ (Nfa.F nfaL) (Nfa.F nfaR) q fst
...| yes ε∈l | no ¬ε∈r = ⊥-elim(¬ε∈r (lemmaLookupT snd))
...| no ¬ε∈l | no ¬ε∈r = ⊥-elim(¬ε∈r (lemmaLookupT snd))
concat-inductive-left {n} {m} {[]} {c ∷ v} {q} {nfaL} {nfaR} (fst , snd) with splitAt n (inject+ m q) | splitAt-inject+ n m q
concat-inductive-left {n} {m} {[]} {c ∷ v} {.x} {nfaL} {nfaR} (fst , snd) | inj₁ x | refl with x ∈? Nfa.F nfaL
concat-inductive-left {n} {m} {[]} {c ∷ v} {.x} {nfaL} {nfaR} (fst , snd) | inj₁ x | refl | yes p₁ with biglemma {m}{c}{v} snd
... | w , t , f with lem1ʳ (Nfa.δ nfaL x c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur  = fromExists (raise n w , joinand pur (concat-right-preserved {n}{m}{v}{w}{nfaL}{nfaR} f))
concat-inductive-left {n} {m} {[]} {c ∷ v} {.x} {nfaL} {nfaR} (fst , snd) | inj₁ x | refl | no ¬p = ⊥-elim (¬p (lemmaLookupT fst))
concat-inductive-left {n} {m} {c ∷ s} {v} {q} {nfaL} {nfaR} (fst , snd) with biglemma {n}{c}{s} fst
... | w , t , f with splitAt n (inject+ m q) | splitAt-inject+ n m q
concat-inductive-left {n} {m} {c ∷ s} {v} {.q} {nfaL} {nfaR} (fst , snd) | w , t , f | inj₁ q | refl with q ∈? Nfa.F nfaL
concat-inductive-left {n} {m} {c ∷ s} {v} {.q} {nfaL} {nfaR} (fst , snd) | w , t , f | inj₁ q | refl | yes p₁ with concat-inductive-left {n}{m}{s}{v}{w}{nfaL}{nfaR} (f , snd)
... | ind  with lem1ˡ (Nfa.δ nfaL q c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = fromExists (inject+ m w , joinand pur ind)
concat-inductive-left {n} {m} {c ∷ s} {v} {.q}{nfaL} {nfaR} (fst , snd) | w , t , f | inj₁ q | refl | no ¬p with concat-inductive-left {n}{m}{s}{v}{w}{nfaL}{nfaR} (f , snd)
... | ind  with lem1ˡ (Nfa.δ nfaL q c) ∅ w t
... | pur = fromExists (inject+ m w , joinand pur ind)

concat-closure : ∀{n m : ℕ} {s v : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → (nfaL ↓ s) × (nfaR ↓ v)
    --------------------------------
  → (concatNfa nfaL nfaR) ↓ (s ++ˢ v)
concat-closure {n} {m} {[]} {[]} {nfaL} {nfaR} (fst , snd) with Nfa.S nfaL ∈? Nfa.F nfaL | Nfa.S nfaR ∈? Nfa.F nfaR
...| yes ε∈l | yes ε∈r = tt
...| yes ε∈l | no ¬ε∈r = ⊥-elim(¬ε∈r (lemmaLookupT snd))
...| no ¬ε∈l | yes ε∈r = ⊥-elim(¬ε∈l (lemmaLookupT fst))
...| no ¬ε∈l | no ¬ε∈r = ⊥-elim(¬ε∈l (lemmaLookupT fst))
concat-closure {n} {m} {[]} {c ∷ v} {nfaL} {nfaR} (fst , snd) with Nfa.S nfaL ∈? Nfa.F nfaL | v[i]=v!i (Nfa.F nfaL) (Nfa.S nfaL)
concat-closure {n} {m} {[]} {c ∷ v} {nfaL} {nfaR} (fst , snd) | yes p | _ with (Nfa.F nfaL) ! (Nfa.S nfaL)
concat-closure {n} {m} {[]} {c ∷ v} {nfaL} {nfaR} (fst , snd) | yes p | _ | true with biglemma {m} {c}{v} snd
... | w , t , f with lem1ʳ (Nfa.δ nfaL (Nfa.S nfaL) c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = fromExists (raise n w , joinand pur (concat-right-preserved {n}{m}{v} f))
concat-closure {n} {m} {[]} {c ∷ v} {nfaL} {nfaR} (fst , snd) | no ¬p | _ = ⊥-elim (¬p (lemmaLookupT fst))
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) with biglemma {n}{c}{s} fst
... | w , t , f  with concat-inductive-left {n}{m}{s}{v} (f , snd)
... | ur with Nfa.S nfaL ∈? Nfa.F nfaL | v[i]=v!i (Nfa.F nfaL) (Nfa.S nfaL)
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | yes p | _ with lookup (Nfa.F nfaL) (Nfa.S nfaL)
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | yes p | _ | false with lem1ˡ (Nfa.δ nfaL (Nfa.S nfaL) c) ∅ w t
... | pur = injectOrR (fromExists (inject+ m w , joinand pur ur))
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | yes p | _ | true with lem1ˡ (Nfa.δ nfaL (Nfa.S nfaL) c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = injectOrR (fromExists (inject+ m w , joinand pur ur))
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | no ¬p | _  with lookup (Nfa.F nfaL) (Nfa.S nfaL)
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | no ¬p | _ | false with lem1ˡ (Nfa.δ nfaL (Nfa.S nfaL) c) ∅ w t
... | pur = fromExists (inject+ m w , joinand pur ur)
concat-closure {n} {m} {c ∷ s} {v} {nfaL} {nfaR} (fst , snd) | w , t , f | ur | no ¬p | _ | true with lem1ˡ (Nfa.δ nfaL (Nfa.S nfaL) c) (Nfa.δ nfaR (Nfa.S nfaR) c) w t
... | pur = fromExists (inject+ m w , joinand pur ur)

star-preserved : ∀{n}{s}{q}{nfa : Nfa n}
  → T(accepts nfa q s)
  → T(accepts (starNfa nfa) (raise 1 q) s)
star-preserved {n} {[]} {q} {nfa} p = p
star-preserved {n} {c ∷ s} {q} {nfa} p with biglemma {n}{c}{s} p
... | w , t , f with q ∈? Nfa.F nfa
star-preserved {n} {c ∷ s} {q} {nfa} p | w , t , f | yes p₁ with star-preserved {n}{s}{w}{nfa} f
... | ind = fromExists (w , joinand (injectSetUnionˡ t (Nfa.δ nfa (Nfa.S nfa) c)) ind)
star-preserved {n} {c ∷ s} {q} {nfa} p | w , t , f | no ¬p with  star-preserved {n}{s}{w}{nfa} f
... | ind = fromExists (w , joinand t ind)

star-inductive : ∀{n}{s v}{q} {nfa : Nfa n}
  → T(accepts nfa q s) × (starNfa nfa) ↓ v
  → T(accepts (starNfa nfa) (raise 1 q) (s ++ˢ v))
star-inductive {n} {[]} {[]} {q} {nfa} (fst , snd) = fst
star-inductive {n} {[]} {c ∷ v} {q} {nfa} (fst , snd) with q ∈? Nfa.F nfa
star-inductive {n} {[]} {c ∷ v} {q} {nfa} (fst , snd) | yes p with anyToExists {n} {λ x →
          lookup (Nfa.δ nfa (Nfa.S nfa) c) x ∧
          accepts (starNfa nfa) (fsuc x) v } snd
star-inductive {n} {[]} {c ∷ v} {q} {nfa} (fst , snd) | yes p | w , f with splitand {lookup (Nfa.δ nfa (Nfa.S nfa) c) w} {accepts (starNfa nfa) (fsuc w) v} f
star-inductive {n} {[]} {c ∷ v} {q} {nfa} (fst , snd) | yes p | w , f | f1 , f2 = fromExists (w , (joinand (injectSetUnionʳ {n} {w} {Nfa.δ nfa (Nfa.S nfa) c} f1 (Nfa.δ nfa q c)) f2))
star-inductive {n} {[]} {c ∷ v} {q} {nfa} (fst , snd) | no ¬p = ⊥-elim(¬p (lemmaLookupT fst))
star-inductive {n} {c ∷ s} {v} {q} {nfa} (fst , snd) with biglemma {n}{c}{s} fst
... | w , t , f with q ∈? Nfa.F nfa
star-inductive {n} {c ∷ s} {v} {q} {nfa} (fst , snd) | w , t , f | yes p with star-inductive {n}{s}{v}{w}{nfa} (f , snd)
... | ind = fromExists (w , joinand (injectSetUnionˡ t (Nfa.δ nfa (Nfa.S nfa) c)) ind)
star-inductive {n} {c ∷ s} {v} {q} {nfa} (fst , snd) | w , t , f | no ¬p with star-inductive {n}{s}{v}{w}{nfa} (f , snd)
... | ind = fromExists (w , joinand t ind)

star-closure : ∀{n} {s v : String} {nfa : Nfa n}
  → nfa ↓ s × (starNfa nfa) ↓ v
    ---------------------------
  → (starNfa nfa) ↓ (s ++ˢ v)
star-closure {n} {[]} {[]} {nfa} (fst , snd) = tt
star-closure {n} {c ∷ s} {[]} {nfa} (fst , snd) rewrite ++-idʳ (s) with biglemma {n} {c} {s} fst
... | w , t , f = fromExists (w , (joinand t (star-preserved {n}{s}{w} {nfa} f)))
star-closure {n} {[]} {c ∷ v} {nfa} (fst , snd) rewrite ++-idˡ (c ∷ v) = snd
star-closure {n} {c ∷ s} {v} {nfa} (fst , snd) with biglemma {n} {c} {s} fst
... | w , t , f = fromExists (w , (joinand t (star-inductive {n}{s}{v}{w}{nfa} (f , snd))))

open Nfa

union-cl-inverse-ind-L : ∀{n m : ℕ} {s : String} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T (accepts (unionNfa nfaL nfaR) (fsuc (inject+ m q)) s)
  → T (accepts nfaL q s)
union-cl-inverse-ind-L {n} {m} {[]} {q} {nfaL}{nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ rewrite sym (lookup-++ˡ (F nfaL) (F nfaR) q) = d
... | yes p | no ¬p  rewrite sym (lookup-++ˡ (F nfaL) (F nfaR) q) = d
... | no ¬p | yes p  rewrite sym (lookup-++ˡ (F nfaL) (F nfaR) q) = d
... | no ¬p | no ¬p₁ rewrite sym (lookup-++ˡ (F nfaL) (F nfaR) q) = d
union-cl-inverse-ind-L {n} {m} {x ∷ s}{q}{nfaL}{nfaR} d with biglemma {1 + n + m} {x} {s} {fsuc (inject+ m q)} {unionNfa nfaL nfaR} d
... | w , t , f with splitAt n (inject+ m q) | splitAt-inject+ n m q
... | inj₁ q | refl with lem7 {n}{m} w (δ nfaL q x) t
... | p , eq , ds rewrite eq = fromExists (p , joinand ds (union-cl-inverse-ind-L {n}{m}{s}{p} f))

union-cl-inverse-ind-R : ∀{n m : ℕ} {s : String} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T (accepts (unionNfa nfaL nfaR) (fsuc (raise n q)) s)
  → T (accepts nfaR q s)
union-cl-inverse-ind-R {n} {m} {[]} {q} {nfaL}{nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ rewrite sym (lookup-++ʳ (F nfaL) (F nfaR) q) = d
... | yes p | no ¬p  rewrite sym (lookup-++ʳ (F nfaL) (F nfaR) q) = d
... | no ¬p | yes p  rewrite sym (lookup-++ʳ (F nfaL) (F nfaR) q) = d
... | no ¬p | no ¬p₁ rewrite sym (lookup-++ʳ (F nfaL) (F nfaR) q) = d
union-cl-inverse-ind-R {n} {m} {x ∷ s}{q}{nfaL}{nfaR} d with biglemma {1 + n + m} {x} {s} {fsuc (raise n q)} {unionNfa nfaL nfaR} d
... | w , t , f with splitAt n (raise n q) | splitAt-raise n m q
... | inj₂ q | refl with lem8 {n}{m} w (δ nfaR q x) t
... | p , eq , ds rewrite eq = fromExists (p , joinand ds (union-cl-inverse-ind-R {n}{m}{s}{p} f))


union-cl-inverse :  ∀{n m : ℕ} {s : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → unionNfa nfaL nfaR ↓ s
  → nfaL ↓ s ⊎ nfaR ↓ s
union-cl-inverse {n} {m} {[]} {nfaL} {nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ = inj₁ (lem9 p)
... | yes p | no ¬p  = inj₁ (lem9 p)
... | no ¬p | yes p  = inj₂ (lem9 p)
union-cl-inverse {n} {m} {x ∷ s} {nfaL} {nfaR} d with biglemma {suc n + m}{x}{s}{0F}{unionNfa nfaL nfaR} d
... | w , t , f with lem10 w (δ nfaL (S nfaL) x) (δ nfaR (S nfaR) x) t
... | inj₁ (p , eq , z) rewrite eq = inj₁ (fromExists (p , joinand z (union-cl-inverse-ind-L {n} {m} {s} f) ))
... | inj₂ (p , eq , z) rewrite eq = inj₂ (fromExists (p , joinand z (union-cl-inverse-ind-R {n} {m} {s} f) ))

concat-closure-inv-indR : ∀{n m : ℕ} {s : String} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T(accepts (concatNfa nfaL nfaR) (fsuc (raise n q)) s)
  → T(accepts nfaR q s)
concat-closure-inv-indR {n} {m} {[]} {q} {nfaL} {nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ rewrite lookup-++ʳ (F nfaL) (F nfaR) q = d
... | no ¬p | yes p  rewrite lookup-++ʳ (F nfaL) (F nfaR) q = d
... | yes p | no ¬p  rewrite lookup-++ʳ (∅{n}) (F nfaR) q = d
... | no ¬p | no ¬p₁ rewrite lookup-++ʳ (∅{n}) (F nfaR) q = d
concat-closure-inv-indR {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d with biglemma {suc n + m} {x}{s}{fsuc (raise n q)}{concatNfa nfaL nfaR} d
... | w , t , f with splitAt n (raise n q) | splitAt-raise n m q
... | inj₂ q | refl with lem8 w (δ nfaR q x) t
... | p , eq , ok rewrite eq = fromExists (p , joinand ok (concat-closure-inv-indR {n}{m}{s} f) )

concat-closure-inv-indL : ∀{n m : ℕ} {s : String} {q} {nfaL : Nfa n} {nfaR : Nfa m}
  → T(accepts (concatNfa nfaL nfaR) (fsuc (inject+ m q)) s)
  → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts nfaL q u) × nfaR ↓ v)
concat-closure-inv-indL {n} {m} {[]} {q} {nfaL} {nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ rewrite lookup-++ˡ (F nfaL) (F nfaR) q = [] , [] , refl , d , lem9 p₁
... | no ¬p | yes p  rewrite lookup-++ˡ (F nfaL) (F nfaR) q = [] , [] , refl , d , lem9 p
... | yes p | no ¬p  rewrite lookup-++ˡ (∅{n}) (F nfaR) q = ⊥-elim (lem11 {n} d)
... | no ¬p | no ¬p₁ rewrite lookup-++ˡ (∅{n}) (F nfaR) q = ⊥-elim (lem11 {n} d)
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d with biglemma {suc n + m} {x}{s}{fsuc (inject+ m q)}{concatNfa nfaL nfaR} d
... | w , t , f with splitAt n (inject+ m q) | splitAt-inject+ n m q
... | inj₁ q | refl with q ∈? F nfaL
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | yes p with lem10 w (δ nfaL q x) (δ nfaR (S nfaR) x) t
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | yes p | inj₁ (np , eq , z) rewrite eq with concat-closure-inv-indL {n}{m}{s}{np}{nfaL}{nfaR} f
... | u , v , s≡uv , ac , ind = x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinand z ac) , ind
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | yes p | inj₂ (np , eq , z) rewrite eq with concat-closure-inv-indR {n}{m}{s}{np} f
... | rac = [] , x ∷ s , refl , lem9 p , fromExists (np , joinand z rac )
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | no ¬p with lem10 w (δ nfaL q x) (∅) t
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | no ¬p | inj₁ (np , eq , z) rewrite eq with concat-closure-inv-indL {n}{m}{s}{np}{nfaL}{nfaR} f
... | u , v , s≡uv , ac , ind = x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinand z ac) , ind
concat-closure-inv-indL {n} {m} {x ∷ s} {q} {nfaL} {nfaR} d | w , t , f | inj₁ q | refl | no ¬p | inj₂ (np , eq , z) = ⊥-elim(lem11 {m} z)

concat-closure-inv : ∀{n m : ℕ} {s : String} {nfaL : Nfa n} {nfaR : Nfa m}
  → concatNfa nfaL nfaR ↓ s
  → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × nfaL ↓ u × nfaR ↓ v)
concat-closure-inv {n} {m} {[]} {nfaL} {nfaR} d with S nfaL ∈? F nfaL | S nfaR ∈? F nfaR
... | yes p | yes p₁ rewrite lookup-++ˡ (F nfaL) (F nfaR) (S nfaL) = [] , [] , refl , lem9 p , lem9 p₁
concat-closure-inv () | no ¬p | yes p
concat-closure-inv () | yes p | no ¬p
concat-closure-inv () | no ¬p | no ¬p₁
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d with biglemma {suc n + m} {x} {s} {0F} d
... | w , t , f with S nfaL ∈? F nfaL
... | yes p with lem10 w (δ nfaL (S nfaL) x) (δ nfaR (S nfaR) x) t
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d | w , t , f | yes p | inj₁ (np , eq , z) rewrite eq with concat-closure-inv-indL {n}{m}{s}{np} f
... | u , v , s≡uv , ac , ind = x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinand z ac) , ind
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d | w , t , f | yes p | inj₂ (np , eq , z) rewrite eq = [] , x ∷ s , refl , lem9 p , fromExists (np , joinand z (concat-closure-inv-indR {n}{m}{s}{np} f))
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d | w , t , f | no ¬p with lem10 w (δ nfaL (S nfaL) x) (∅) t
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d | w , t , f | no ¬p | inj₁ (np , eq , z) rewrite eq with concat-closure-inv-indL {n}{m}{s}{np} f
... | u , v , s≡uv , ac , ind = x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinand z ac) , ind
concat-closure-inv {n} {m} {x ∷ s} {nfaL} {nfaR} d | w , t , f | no ¬p | inj₂ (np , eq , z) rewrite eq = ⊥-elim(lem11 {m} z)

--------------------------------------------------------------------------------

star-inv-ind : ∀{n} {s : String} {nfa : Nfa n}
  → (q : Fin n)
  → T(accepts (starNfa nfa) (fsuc q) s)
  → ¬ (q ∈ F nfa)
  → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts nfa q u) × T (any (λ p → F nfa ! p ∧ accepts (starNfa nfa) (fsuc p) v)))
star-inv-ind {n} {[]} {nfa} q ac nf with lem1ʳ (true ∷v []v) (F nfa) q ac | v[i]=v!i (F nfa) q
... | lm | u rewrite lem5 (F nfa) lm = ⊥-elim(nf u)
star-inv-ind {n} {x ∷ s} {nfa} q ac nf with biglemma {_} {x} {s} {fsuc q} {starNfa nfa} ac
... | w , t , f with q ∈? F nfa
... | yes p = ⊥-elim(nf p)
... | no ¬p with lem2 w (lem0 w (δ nfa q x) t)
... | fsw , snd rewrite snd with fsw ∈? F nfa
... | yes p2 = x ∷ [] , s , refl
  , fromExists (fsw , joinand t (subst (λ v → T v) (sym (s!i≡s[i] p2)) tt))
  , fromExists (fsw , joinand (subst (λ v → T v) (sym (s!i≡s[i] p2)) tt) f)
... | no ¬p2 with star-inv-ind {n} {s} {nfa} fsw f ¬p2
... | u , v , eq , acind , decin = x ∷ u , v , cong (x ∷_) eq , fromExists (fsw , joinand t acind) , decin

star-inv-Base : ∀{n} {s : String} {nfa : Nfa n}
  → (starNfa nfa) ↓ s
  → ¬ (s ≡ [])
  → ∃[ u ] ∃[ v ](s ≡ u ++ˢ v × nfa ↓ u × T (any (λ p → F nfa ! p ∧ accepts (starNfa nfa) (fsuc p) v)))
star-inv-Base {n} {[]} {nfa} d1 ne = ⊥-elim (ne refl)
star-inv-Base {n} {c ∷ s} {nfa} d1 ne with anyToExists {n} d1
... | fst , snd with fst ∈? F nfa
star-inv-Base {n} {c ∷ s} {nfa} d1 ne | fst , snd | yes p =
  c ∷ [] , s , refl
    , fromExists (fst , joinand (proj₁ (splitand snd)) (subst (λ v → T v) (sym (s!i≡s[i] p)) tt))
    , fromExists (fst , joinand (subst (λ v → T v) (sym (s!i≡s[i] p)) tt) (proj₂ (splitand snd)))
star-inv-Base {n} {c ∷ s} {nfa} d1 ne | fst , snd | no ¬p with star-inv-ind {n}{s} {nfa} (fst) (proj₂ (splitand snd)) ¬p
... | u , v , eq , l , z =
  c ∷ u , v , cong (c ∷_) eq , fromExists (fst , (joinand (proj₁ (splitand snd)) l) ) , z

star-acc-from-fin : ∀{n} {s : String} {nfa : Nfa n}
  → (q : Fin n)
  → T(accepts (starNfa nfa) (fsuc q) s)
  → (q ∈ F nfa)
  → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × (T(accepts nfa q u) ⊎ nfa ↓ u))
star-acc-from-fin {n} {[]} {nfa} q ac isf = [] , [] , refl , inj₁ ac
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf with biglemma {_}{x}{s}{fsuc q}{starNfa nfa} ac
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | w , t , f with q ∈? F nfa
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | w , t , f | yes p with lem2 w (lem0 w (δ nfa (S nfa) x ∪ δ nfa q x) t)
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl with fst ∈? F nfa
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | yes p₁ with lem6 (δ nfa (S nfa) x) (δ nfa q x) fst t
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | yes p₁ | inj₁ x₁ = x ∷ [] , s , refl , inj₂ (fromExists (fst , joinand x₁ (lem12 p₁)  ))
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | yes p₁ | inj₂ y with star-acc-from-fin {n}{s}{nfa} fst f p₁
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | yes p₁ | inj₂ y | u , v , eq , inj₁ x₁ = x ∷ u , v , cong (_∷_ x) eq , inj₁ (fromExists (fst , joinand y x₁ ) )
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | yes p₁ | inj₂ y | u , v , eq , inj₂ y₁ = x ∷ [] , u ++ˢ v , cong (_∷_ x) eq , inj₁ (fromExists (fst , joinand y (lem12 p₁)))
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | no ¬p with lem6 (δ nfa (S nfa) x) (δ nfa q x) fst t
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | no ¬p | inj₁ y with star-inv-ind  {n}{s} fst f ¬p
... | u , v , eq  , acc , _ = x ∷ u , v , cong (_∷_ x) eq , inj₂ (fromExists (fst , joinand y acc  ))
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | .(fsuc fst) , t , f | yes p | fst , refl | no ¬p | inj₂ y with star-inv-ind  {n}{s} fst f ¬p
... | u , v , eq  , acc , _  = x ∷ u , v , cong (_∷_ x) eq , inj₁ (fromExists (fst , joinand y acc ))
star-acc-from-fin {n} {x ∷ s} {nfa} q ac isf | w , t , f | no ¬p = ⊥-elim(¬p isf)

postulate
  star-inv : ∀{n} {s : String} {nfa : Nfa n}
    → (starNfa nfa) ↓ s
    → ¬ (s ≡ [])
    → ∃[ u ] ∃[ v ](s ≡ u ++ˢ v × ¬ (u ≡ []) × nfa ↓ u ×  starNfa nfa ↓ v)

-- star-inv {n} {[]} {nfa} d1 ne = ⊥-elim (ne refl)
-- star-inv {n} {c ∷ s} {nfa} d1 ne with anyToExists {n} d1
-- ... | fst , snd with fst ∈? F nfa
-- star-inv {n} {c ∷ s} {nfa} d1 ne | fst , snd | yes p = {!   !}
-- star-inv {n} {c ∷ s} {nfa} d1 ne | fst , snd | no ¬p with star-inv-ind {n}{s} {nfa} (fst) (proj₂ (splitand snd)) ¬p
-- ... | u , v , eq , l , z =
--   c ∷ u , v , cong (c ∷_) eq , (λ ()) , fromExists (fst , (joinand (proj₁ (splitand snd)) l) ) , {!   !} -- z

star-closure-inverse : ∀{n} {a} {s : String} {nfa : Nfa n}
  → (starNfa nfa) ↓ (a ∷ s)
  → ∃[ u ] ∃[ v ]((a ∷ s) ≡ (a ∷ u) ++ˢ v × nfa ↓ (a ∷ u) × starNfa nfa ↓ v)
star-closure-inverse {n}{a}{s}{nfa} d with star-inv {n} {a ∷ s} {nfa} d λ ()
star-closure-inverse {n} {a} {s} {nfa} d | [] , v , eq , neq , fl , xt = ⊥-elim(neq refl)
... | x ∷ u , [] , refl , neq , fl , xt = u , [] , refl , fl , tt
... | x ∷ u , x2 ∷ v , refl , neq , fl , xt = u , x2 ∷ v , refl , fl , xt


--

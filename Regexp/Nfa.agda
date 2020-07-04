module Nfa (Σ : Set) where
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≥_; _<?_; _≤?_; s≤s; z≤n; _∸_)
open import Data.Fin
  using (Fin; inject+; 0F; raise)
  renaming (zero to fzero; suc to fsuc; _<_ to _<f_; _<?_ to _<f?_)
open import Data.Fin.Subset as Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _⊆_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Fin.Subset.Properties using (x∈p∪q⁺; x∈p∪q⁻)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true; _∨_; _∧_; T; not)
open import Data.Bool.Properties using (T?)
open import Data.Product using (_×_; ∃; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Sum using (_¬-⊎_)
open import String Σ using (String; _∷_; []; ++-idˡ; ++-idʳ; take; drop; ++-assoc; length) renaming (_++_ to _++ˢ_)
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
    δ : Fin n → Σ → Subset n
    F : Subset n

any : ∀{n} → (P : Fin n → Bool) → Bool
any {zero}  P = false
any {suc _} P = P fzero ∨ any λ x → P (fsuc x)
open Nfa

accepts : ∀{n} → Nfa n → Fin n → String → Bool
accepts A q []       = F A ! q
accepts A q (c ∷ s) = any λ p → (δ A q c) ! p ∧ accepts A p s

infix 10 _↓_
_↓_ : ∀{n} → Nfa n → String → Set
A ↓ s  = T (accepts A (S A) s)

_↓?_ : ∀{n} → (nfa : Nfa n) → (s : String) → Dec (nfa ↓ s)
A ↓? s = T? (accepts A (S A) s)

-- Alternative 1: Acceptance by Intersection of final states with extendend delta
δ^ : ∀{n} → Nfa n → (Subset n) → String → (Subset n)
δ^ {n} A qs [] = qs
δ^ {n} A qs (c ∷ s) = δ^ A (U (mapS qs (λ q → δ A q c) ∅)) s

infix 10 _↓′_
_↓′_ : ∀{n} → Nfa n → String → Set
A ↓′ s  = Nonempty ((F A) ∩ (δ^ A ⁅ S A ⁆ s))

-- Alternative 2: Acceptance by States path
data Acc {n} : Nfa n → Fin n → String → Set where
  Acc[] : ∀{q}{nfa} → q ∈ F nfa → Acc nfa q []
  Acc∷ : ∀{p x xs q nfa} → p ∈ δ nfa q x → Acc nfa p xs → Acc nfa q (x ∷ xs)

infix 10 _↓′′_
_↓′′_ : ∀{n} → Nfa n → String → Set
nfa ↓′′ s = Acc nfa (S nfa) s

ε = []

emptyLanguage : ∀{n} {nfa : Nfa n} → nfa ↓ ε ≡ S nfa ∈ F nfa
emptyLanguage = refl

--------------------------------------------------------------------------------
-- Union, Concatenation and Star operations on Nfa

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero    i        = inj₂ i
splitAt (suc m) fzero    = inj₁ fzero
splitAt (suc m) (fsuc i) = Data.Sum.map fsuc (λ x → x) (splitAt m i)

union : ∀{n m} → Nfa n → Nfa m → Nfa (1 + n + m)
union {n} {m} A B =
  record
    { S = fzero
    ; δ = d
    ; F = sf ++ (F A) ++ (F B)
    }
  where
    d : Fin (1 + n + m) → Σ → Subset (1 + n + m)
    d q c  with splitAt 1 q
    d q c | inj₁ z = ∅ {1} ++ (δ A (S A) c) ++ (δ B (S B) c)
    d q c | inj₂ f with splitAt n f
    ... | inj₁ l = ∅ {1} ++ (δ A l c) ++ ∅
    ... | inj₂ r = ∅ {1} ++ ∅ ++ (δ B r c)

    sf : Subset 1
    sf with A ↓? ε | B ↓? ε
    sf | no ε∉l | no ε∉r = ∅
    sf | _     | _       = FullSet

concat : ∀{n m} → Nfa n → Nfa m → Nfa (1 + n + m)
concat {n} {m} A B =
  record
    { S = fzero
    ; δ = d
    ; F = f
    }
  where
    d : Fin (1 + n + m) → Σ → Subset (1 + n + m)
    d q c with splitAt 1 q
    d _ c | inj₁ z with A ↓? ε
    ... | yes isf = ∅ {1} ++ (δ A (S A) c) ++ (δ B (S B) c)
    ... | no ¬isf = ∅ {1} ++ (δ A (S A) c) ++ ∅
    d _ c | inj₂ mn with splitAt n mn
    d _ c | inj₂ mn | inj₁ l with l ∈? F A
    ... | yes isf = ∅ {1} ++ (δ A l c) ++ (δ B (S B) c)
    ... | no ¬isf = ∅ {1} ++ (δ A l c) ++  ∅
    d _ c | inj₂ mn | inj₂ r = ∅ {1} ++ ∅ ++ (δ B r c)

    f : Subset (1 + n + m)
    f with A ↓? ε | B ↓? ε
    f | yes ε∈l | yes ε∈r = FullSet {1} ++ F A ++ F B
    f | no ε∉l | yes ε∈r = ∅ {1} ++ F A ++ F B
    f | _ | no ε∉r = ∅ {1} ++ ∅ ++ F B

star : ∀{n} → Nfa n → Nfa (1 + n)
star {n} nfa =
  record
    { S = fzero
    ; δ = d
    ; F = ⁅ fzero ⁆ ++ F nfa
    }
  where
    d : Fin (1 + n) → Σ → Subset (1 + n)
    d q c with splitAt 1 q
    d _ c | inj₁ z = ∅ ++ (δ nfa (S nfa) c)
    d _ c | inj₂ p with p ∈? F nfa
    ... | yes isf = ∅ ++ (δ nfa (S nfa) c) ∪ (δ nfa p) c
    ... | no ¬isf = ∅ ++ (δ nfa p) c

--------------------------------------------------------------------------------
-- Correctness of Union, Star and Concatenation constructions

open Nfa

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

splitAnd : ∀{a b} → T (a ∧ b) → T a × T b
splitAnd {true} {true} tt = tt , tt

joinAnd : ∀{a} {b} → T a → T b → T (a ∧ b)
joinAnd {true} {true} _ _ = tt

anyToExists : ∀{n} {f : Fin n → Bool} → T (any f) → ∃[ i ] T(f i)
anyToExists {suc n} {f} t with splitOr {f 0F} {any (λ x → f (fsuc x))} t
anyToExists {suc n} {f} t | inj₁ x = 0F , x
anyToExists {suc n} {f} t | inj₂ y with anyToExists {_} {λ u → f (fsuc u)} y
anyToExists {suc n} {f} t | inj₂ y | fst , snd = fsuc fst , snd

fromExists : ∀{n} {f : Fin n → Bool} → ∃[ i ] T(f i) → T(any f)
fromExists {_} {f} (0F , snd) = injectOrL snd
fromExists {_} {f} (fsuc fst , snd) = injectOrR (fromExists ( fst , snd ))


nextState : ∀{n x xs q} {nfa : Nfa n}
  → T (accepts nfa q (x ∷ xs))
  → ∃[ p ] ( p ∈ (δ nfa q x)  × T (accepts nfa p xs))
nextState {n} acc-x-xs with anyToExists {n} acc-x-xs
... | p , p∈δqx_∧_acc-p-xs = p , (splitAnd p∈δqx_∧_acc-p-xs)

toAccPath : ∀{n} {nfa : Nfa n} {q xs}
  → T (accepts nfa q xs)
  → Acc nfa q xs
toAccPath     {xs = []}     acc = Acc[] acc
toAccPath {n} {xs = x ∷ xs} acc with nextState {n} {x} {xs} acc
... | p , p∈δqx , acc-p-xs = Acc∷ p∈δqx (toAccPath acc-p-xs)

++-inject : ∀{n m} → (v : Vec Bool n) → (w : Vec Bool m)
  → (p : Fin n)
  → p ∈ v
  → inject+ m p ∈ (v ++ w)
++-inject v w p x = subst T (sym (lookup-++ˡ v w p)) x

++-raise : ∀{n m} → (v : Vec Bool n) → (w : Vec Bool m)
  → (p : Fin m)
  → p ∈ w
  → raise n p ∈ (v ++ w)
++-raise v w p x = subst T (sym (lookup-++ʳ v w p)) x

∈-to-T : ∀{n} {w} {v : Subset n} → w Subset.∈ v →  w ∈ v
∈-to-T t = subst T (sym (s!i≡s[i] t)) tt

splitAt-inject+ : ∀ m n i → splitAt m (inject+ n i) ≡ inj₁ i
splitAt-inject+ (suc m) n fzero = refl
splitAt-inject+ (suc m) n (fsuc i) rewrite splitAt-inject+ m n i = refl

splitAt-raise : ∀ m n i → splitAt m (raise {n} m i) ≡ inj₂ i
splitAt-raise zero    n i = refl
splitAt-raise (suc m) n i rewrite splitAt-raise m n i = refl

T-to-∈ : ∀{n} {v : Vec Bool n} {w} →  w ∈ v  → w Subset.∈ v
T-to-∈ {_} {x ∷v v} {0F} t with (x ∷v v) ! 0F
T-to-∈ {_} {x ∷v v} {0F} t | true = here
T-to-∈ {_} {x ∷v v} {fsuc w} t = there (T-to-∈ t)

injectSetUnionʳ : ∀{n} {q} {inj : Subset n} → (set : Subset n) → q ∈ set →  q ∈ (set ∪ inj)
injectSetUnionʳ {n} {q} {inj} set t with set ! q | v[i]=v!i set q
... | true | u =  subst T (sym (s!i≡s[i] (x∈p∪q⁺ {_}{set}{inj} (inj₁ u)))) tt

injectSetUnionˡ : ∀{n} {q} {set : Subset n} →  q ∈ set  → (inj : Subset n) →  q ∈ (inj ∪ set)
injectSetUnionˡ {n} {q} {set} t inj with set ! q  | v[i]=v!i set q
... | true | u =  subst T (sym (s!i≡s[i] (x∈p∪q⁺ {_}{inj} (inj₂ u)))) tt

split-a∪b : ∀{n} → (a b : Subset n) (q : Fin n)
  →  q ∈ (a ∪ b)
  →  q ∈ a  ⊎  q ∈ b
split-a∪b {n} a b q ac with x∈p∪q⁻ a b (T-to-∈ {n}{a ∪ b} ac)
split-a∪b {n} a b q ac | inj₁ x = inj₁ (∈-to-T x)
split-a∪b {n} a b q ac | inj₂ x = inj₂ (∈-to-T x)

skipEmptyFirst : ∀{n} {vec : Subset n} → (q : Fin (suc n)) →  q ∈ (false ∷v vec)  → ∃[ p ] (q ≡ fsuc p)
skipEmptyFirst (fsuc q) t = q , refl

¬x∈∅ : ∀{n} {t : Fin n} → ¬( t ∈ ∅{n} )
¬x∈∅ {suc n} {fsuc t} d = ¬x∈∅ {n}{t} d

¬x∈∅++[] : ∀{n} {t : Fin (n + 0F)} → ¬( t ∈ (∅{n} ++ []v) )
¬x∈∅++[] {suc n} {fsuc t} ds = ¬x∈∅++[]{n}{t} ds

q∈ss++∅ : ∀{n m}
  → (q : Fin (suc (n + m))) (ss : Subset n)
  →  q ∈ (false ∷v ss ++ ∅ {m})
  → ∃[ p ](q ≡ fsuc (inject+ m p) ×  p ∈ ss )
q∈ss++∅ {.0} (fsuc q) []v acc = ⊥-elim(¬x∈∅ {_}{fsuc q} acc)
q∈ss++∅ {.(suc _)}  Data.Fin.1F (true ∷v ss) tt = 0F , refl , tt
q∈ss++∅ {.(suc _)} (fsuc (fsuc q)) (z ∷v ss) acc with q∈ss++∅ {_} (fsuc q) ss acc
q∈ss++∅ {.(suc _)} (fsuc (fsuc q)) (z ∷v ss) acc | fst , snd , trd = fsuc fst , cong fsuc snd , trd

q∈∅++ss : ∀{n m}
  → (q : Fin (suc (n + m)))
  → (ss : Subset m)
  →  q ∈ (false ∷v ∅ {n} ++ ss)
  → ∃[ p ](q ≡ fsuc (raise n p) ×  p ∈ ss )
q∈∅++ss {suc n} {.0} q []v ac = ⊥-elim(¬x∈∅++[] {_}{q} ac)
q∈∅++ss {0F} (fsuc q) (x ∷v ss) ac = q , refl , ac
q∈∅++ss {suc n} {m} (fsuc q) (ss) ac with q∈∅++ss {n} q (ss) ac
... | fst , snd , trd  = fst , cong fsuc snd , trd

split-∈++ : ∀{n m} → (q : Fin (suc (n + m))) (ss1 : Subset n ) (ss2 : Subset m)
  →  q ∈ (false ∷v ss1 ++ ss2)
  → ∃[ p ](q ≡ fsuc (inject+ m p) ×  p ∈ ss1 )
  ⊎ ∃[ p ](q ≡ fsuc (raise n p)   ×  p ∈ ss2 )
split-∈++ {0F} {m} (fsuc q) []v ss2 acc = inj₂ (q , refl , acc)
split-∈++ {suc n} {m} Data.Fin.1F (true ∷v ss1) ss2 tt = inj₁ (0F , refl , tt)
split-∈++ {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc with split-∈++ {n}{m}(fsuc q) ss1 ss2 acc
split-∈++ {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc | inj₁ (fst , snd , trd) = inj₁ (fsuc fst , cong fsuc snd , trd )
split-∈++ {suc n} {m} (fsuc (fsuc q)) (x ∷v ss1) ss2 acc | inj₂ (fst , snd , trd) = inj₂ (fst , cong fsuc snd , trd )

--------------------------------------------------------------------------------
-- Correctness of concat
concat-preservesʳ : ∀{n m : ℕ} {p} {A : Nfa n} {B : Nfa m}
  → (v : String)
  → T(accepts B p v)
    ⇔
    T(accepts (concat A B) (raise 1 (raise n p)) v)
concat-preservesʳ {n}{m}{p}{A}{B} v =
  record { to = to v p ; from = from v p }
  where
  to : (v : String) (p : Fin m)
    → T (accepts B p v)
    → T (accepts (concat A B) (fsuc (raise n p)) v)
  to [] p acc with A ↓? ε | B ↓? ε
  ...| yes _ | yes _ = ++-raise (F A) (F B) p acc
  ...| no  _ | yes _ = ++-raise (F A) (F B) p acc
  ...| yes _ | no  _ = ++-raise (∅ {n}) (F B) p acc
  ...| no  _ | no  _ = ++-raise (∅ {n}) (F B) p acc
  to (c ∷ v) p acc with  nextState {m}{c}{v} acc
  ... | w , t , f rewrite splitAt-raise n m p
    with ++-raise (∅ {1 + n}) (δ B p c) w t
  ... | pur = fromExists (raise n w , joinAnd pur (to v w f))

  from : (s : String) (q : Fin m)
    → T(accepts (concat A B) (fsuc (raise n q)) s)
    → T(accepts B q s)
  from [] q d with A ↓? ε | B ↓? ε
  ... | yes p | yes p₁ rewrite lookup-++ʳ (F A) (F B) q = d
  ... | no ¬p | yes p  rewrite lookup-++ʳ (F A) (F B) q = d
  ... | yes p | no ¬p  rewrite lookup-++ʳ (∅{n}) (F B) q = d
  ... | no ¬p | no ¬p₁ rewrite lookup-++ʳ (∅{n}) (F B) q = d
  from (x ∷ s) q d with nextState {suc (n + m)}{x}{s}{fsuc (raise n q)} d
  ... | w , t , f rewrite splitAt-raise n m q with q∈∅++ss w (δ B q x) t
  ... | p , eq , ok rewrite eq = fromExists (p , joinAnd ok (from s p f))


concat-preservesˡ : ∀{n m : ℕ} {q} {A : Nfa n} {B : Nfa m}
  → (s : String)
  → T(accepts (concat A B) (fsuc (inject+ m q)) s)
    ⇔
    ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts A q u) × B ↓ v)
concat-preservesˡ {n}{m}{q}{A}{B} s =
  record { to = to s q ; from = from s q }
  where
  to : (s : String) (q : Fin n)
    → T(accepts (concat A B) (fsuc (inject+ m q)) s)
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts A q u) × B ↓ v)
  to [] q d with A ↓? ε | B ↓? ε
  ... | yes p | yes p₁ rewrite lookup-++ˡ (F A) (F B) q =
    [] , [] , refl , d , p₁
  ... | no ¬p | yes p  rewrite lookup-++ˡ (F A) (F B) q =
    [] , [] , refl , d , p
  ... | yes p | no ¬p  rewrite lookup-++ˡ (∅{n}) (F B) q =
    ⊥-elim (¬x∈∅ {n} d)
  ... | no ¬p | no ¬p₁ rewrite lookup-++ˡ (∅{n}) (F B) q =
    ⊥-elim (¬x∈∅ {n} d)
  to (x ∷ s) q d with nextState {suc n + m}{x}{s}{fsuc (inject+ m q)} d
  to (x ∷ s) q d | w , t , f rewrite splitAt-inject+ n m q with q ∈? F A
  to (x ∷ s) q d | w , t , f | yes p with split-∈++ w _ (δ B (S B) x) t
  to (x ∷ s) q d | w , t , f | yes p | inj₁ (np , eq , z) rewrite eq
    with to s np f
  ... | u , v , s≡uv , ac , ind =
    x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinAnd z ac) , ind
  to (x ∷ s) q d | w , t , f | yes p | inj₂ (np , eq , z) rewrite eq
    with (_⇔_.from (concat-preservesʳ s) f)
  ... | r =
    [] , x ∷ s , refl , p , fromExists (np , joinAnd z r)
  to (x ∷ s) q d | w , t , f | no ¬p with split-∈++ w (δ A q x) ∅ t
  ... | inj₂ (np , eq , z) = ⊥-elim(¬x∈∅ {m} z)
  ... | inj₁ (np , eq , z) rewrite eq with to s np f
  ... | u , v , s≡uv , ac , ind =
    x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinAnd z ac) , ind

  from : (s : String) (q : Fin n)
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts A q u) × B ↓ v)
    → T(accepts (concat A B) (fsuc (inject+ m q)) s)
  from _ q ([] , [] , eq , ac , rec) rewrite eq with A ↓? ε | B ↓? ε
  ... | yes ε∈l | yes ε∈r = ++-inject (F A) (F B) q ac
  ... | no ε∉l | yes ε∈r = ++-inject (F A) (F B) q ac
  ... | yes ε∈l | no ε∉r = ⊥-elim(ε∉r rec)
  ... | no ε∉l | no ε∉r = ⊥-elim(ε∉r rec)
  from _ q ([] , c ∷ v , eq , ac , req) rewrite eq | splitAt-inject+ n m q
    with q ∈? F A
  ... | no ¬p = ⊥-elim(¬p ac)
  ... | yes k with nextState {m}{c}{v} req
  ... | w , t , f with ++-raise (δ A q c) (δ B (S B) c) w t
                    | (_⇔_.to (concat-preservesʳ v) f)
  ... | pur | r = fromExists (raise n w , joinAnd pur r)
  from _ q (c ∷ u , v , refl , ac , req) with nextState {n}{c}{u} ac
  ... | w , t , f rewrite splitAt-inject+ n m q
    with from (u ++ˢ v) w (u , v , refl , f , req)
  ... | IH with q ∈? F A
  ... | yes _ =
    fromExists (inject+ m w , joinAnd (++-inject (δ A q c) _ w t) IH)
  ... | no  _ =
    fromExists (inject+ m w , joinAnd (++-inject (δ A q c) _ w t) IH)

concat-correct : ∀{n m : ℕ} {A : Nfa n} {B : Nfa m}
  → (s : String)
  → concat A B ↓ s
    ⇔
    ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × A ↓ u × B ↓ v)
concat-correct {n}{m}{A}{B} s =
  record { to = to s ; from = from s }
  where
  to : (s : String)
    → concat A B ↓ s
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × A ↓ u × B ↓ v)
  to [] d with A ↓? ε | B ↓? ε
  ... | yes p | yes p₁ rewrite lookup-++ˡ (F A) (F B) (S A)
    = [] , [] , refl , p , p₁
  to [] () | no ¬p | yes p
  to [] () | yes p | no ¬p
  to [] () | no ¬p | no ¬p₁
  to (x ∷ s) d with nextState {suc n + m} {x} {s} {0F} d
  ... | w , t , f with A ↓? ε
  ... | yes p with split-∈++ w (δ A (S A) x) (δ B (S B) x) t
  to (x ∷ s) d | w , t , f | yes p | inj₁ (np , eq , z) rewrite eq
    with _⇔_.to (concat-preservesˡ s) f
  ... | u , v , s≡uv , ac , ind =
    x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinAnd z ac) , ind
  to (x ∷ s) d | w , t , f | yes p | inj₂ (np , eq , z) rewrite eq
    with _⇔_.from (concat-preservesʳ s) f
  ... | r =
    [] , x ∷ s , refl , p , fromExists (np , joinAnd z r)
  to (x ∷ s) d | w , t , f | no ¬p with split-∈++ w (δ A (S A) x) ∅ t
  ... | inj₂ (np , eq , z) rewrite eq = ⊥-elim(¬x∈∅ {m} z)
  ... | inj₁ (np , eq , z) rewrite eq
    with _⇔_.to (concat-preservesˡ s) f
  ... | u , v , s≡uv , ac , ind =
    x ∷ u , v , cong (x ∷_) s≡uv , fromExists (np , joinAnd z ac) , ind

  from : (s : String)
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × A ↓ u × B ↓ v)
    → concat A B ↓ s
  from _ ([] , [] , refl , fst , snd) with A ↓? ε | B ↓? ε
  ...| yes ε∈l | yes ε∈r = tt
  ...| yes ε∈l | no ε∉r = ⊥-elim(ε∉r snd)
  ...| no ε∉l | yes ε∈r = ⊥-elim(ε∉l fst)
  ...| no ε∉l | no ε∉r = ⊥-elim(ε∉l fst)
  from _ ([] , c ∷ v , refl , fst , snd) with A ↓? ε
  ... | no ¬p = ⊥-elim (¬p (fst))
  ... | yes p with nextState {m} {c}{v} snd
  ... | w , t , f with  ++-raise (δ A (S A) c) _ w t
                      | _⇔_.to (concat-preservesʳ v) f
  ... | l | r = fromExists (raise n w , joinAnd l r)
  from _ (c ∷ s , v , refl , fst , snd) with nextState {n}{c}{s} fst
  ... | w , t , f  with
    _⇔_.from (concat-preservesˡ (s ++ˢ v)) (s , v , refl , f , snd)
  ... | ur with A ↓? ε
  ... | yes p = injectOrR (
    fromExists (inject+ m w , joinAnd (++-inject (δ A (S A) c) _ w t) ur)
    )
  ... | no ¬p =
    fromExists (inject+ m w , joinAnd (++-inject (δ A (S A) c) ∅ w t) ur)

--------------------------------------------------------------------------------
-- Correctness of union
union-preservesˡ : ∀{n m} {A : Nfa n} {B : Nfa m} {q : Fin n}
  → (s : String)
  → T (accepts A q s)
    ⇔
    T (accepts (union A B) (fsuc (inject+ m q)) s)
union-preservesˡ {n}{m} {A} {B} {q} s =
  record { to = to s q ; from = from s q }
  where
  to : (s : String) (q : Fin n)
    → T (accepts A q s)
    → T (accepts (union A B) (fsuc (inject+ m q)) s)
  to [] q acc with A ↓? ε | B ↓? ε | ++-inject (F A) (F B) q acc
  ...| yes _ | yes _ | acc-∪ = acc-∪
  ...| yes _ | no  _ | acc-∪ = acc-∪
  ...| no  _ | yes _ | acc-∪ = acc-∪
  ...| no  _ | no  _ | acc-∪ = acc-∪

  to (c ∷ s) q acc with nextState {_} {c} {s} acc
  ... | w , w∈δqc , t rewrite splitAt-inject+ n m q =
    let IH = to s w t in
    let d = ++-inject {n}{m} (δ A q c) ∅ w w∈δqc
      in fromExists (inject+ m w , (joinAnd d IH))

  from : (s : String) (q : Fin n)
    → T (accepts (union A B) (fsuc (inject+ m q)) s)
    → T (accepts A q s)
  from [] q acc rewrite sym (lookup-++ˡ (F A) (F B) q)
    with A ↓? ε | B ↓? ε
  ... | yes _ | yes _  = acc
  ... | yes _ | no  _  = acc
  ... | no  _ | yes _  = acc
  ... | no  _ | no  _  = acc

  from (x ∷ s) q d with nextState {_} {x} {s} {fsuc (inject+ m q)} d
  ... | w , w∈δqx , accWs rewrite splitAt-inject+ n m q
    with q∈ss++∅ w (δ A q x) w∈δqx
  ... | p , eq , ds rewrite eq =
    fromExists (p , joinAnd ds (from s p accWs))

union-preservesʳ : ∀{n m} {A : Nfa n} {B : Nfa m} {q : Fin m}
  → (s : String)
  → T (accepts B q s)
    ⇔
    T (accepts (union A B) (fsuc (raise n q)) s)
union-preservesʳ {n}{m}{A}{B} {q} s  =
  record { to = to s q ; from = from s q }
  where
  to : (s : String) (q : Fin m)
    → T (accepts B q s)
    → T (accepts (union A B) (raise (1 + n) q) s)
  to [] q p with
      A ↓? ε
    | B ↓? ε
    | ++-raise (F A) (F B) q p
  ... | yes _ | yes _ | v = v
  ... | yes _ | no  _ | v = v
  ... | no  _ | yes _ | v = v
  ... | no  _ | no  _ | v = v
  to (c ∷ s) q x with nextState {m}{c}{s} x
  ... | w , v , t rewrite splitAt-raise n m q
                  with to s w t
                      | ++-raise {n}{m} ∅ (δ B q c) w v
  ... | u | i = fromExists (raise n w , (joinAnd i u))

  from : (s : String) (q : Fin m)
    → T (accepts (union A B) (fsuc (raise n q)) s)
    → T (accepts B q s)
  from [] q ac rewrite
        sym (lookup-++ʳ (F A) (F B) q)
    with A ↓? ε | B ↓? ε
  ... | yes _ | yes _ = ac
  ... | yes _ | no  _ = ac
  ... | no  _ | yes _ = ac
  ... | no  _ | no  _ = ac
  from (x ∷ s) q d with nextState {_} {x} {s} {fsuc (raise n q)} d
  ... | w , t , f rewrite splitAt-raise n m q
    with q∈∅++ss {n}{m} w (δ B q x) t
  ... | p , eq , ds rewrite eq =
    fromExists (p , joinAnd ds (from s p f))


union-correct : ∀{n m : ℕ} {A : Nfa n} {B : Nfa m}
  → (s : String)
  → A ↓ s ⊎ B ↓ s ⇔ union A B ↓ s
union-correct {n}{m}{A}{B} s =
  record { to = to s ; from = from s }
  where
  to : (s : String) → A ↓ s ⊎ B ↓ s → union A B ↓ s
  to [] ac with A ↓? ε | B ↓? ε
  ... | yes _  | yes _ = tt
  ... | yes _  | no  _ = tt
  ... | no  _  | yes _ = tt
  ... | no ¬p  | no ¬q = ⊥-elim ((¬p ¬-⊎ ¬q) ac)

  to (c ∷ s) (inj₁ A↓cs) with nextState {_} {c} {s} A↓cs
  ... | w , w∈δA , accepts-s-w-A
                with ++-inject (δ A (S A) c) (δ B (S B) c) w w∈δA
                   | _⇔_.to (union-preservesˡ s) accepts-s-w-A
  ... | w∈δA∪B | accepts-s-w-A∪B
    = fromExists (inject+ m w , joinAnd w∈δA∪B accepts-s-w-A∪B)

  to (c ∷ s) (inj₂ B↓cs) with nextState {_} {c} {s} B↓cs
  ... | w , w∈δB , accepts-w-B
                with ++-raise (δ A (S A) c) (δ B (S B) c) w w∈δB
                   | _⇔_.to (union-preservesʳ s) accepts-w-B
  ... | w∈δA∪B | accepts-s-w-A∪B
    = fromExists (raise n w , joinAnd w∈δA∪B accepts-s-w-A∪B)


  from : (s : String) → union A B ↓ s → A ↓ s ⊎ B ↓ s
  from [] d with A ↓? ε | B ↓? ε
  ... | yes p | yes p₁ = inj₁ p
  ... | yes p | no ¬p  = inj₁ p
  ... | no ¬p | yes p  = inj₂ p

  from (x ∷ s) d with nextState {suc n + m} {x} {s} {0F} d
  ... | w , w∈δSc , accepts-w-s with split-∈++ w (δ A (S A) x) (δ B (S B) x) w∈δSc
  ... | inj₁ (p , eq , z) rewrite eq =
    inj₁ (fromExists (p , joinAnd z (_⇔_.from (union-preservesˡ s) accepts-w-s)))
  ... | inj₂ (p , eq , z) rewrite eq =
    inj₂ (fromExists (p , joinAnd z (_⇔_.from (union-preservesʳ s) accepts-w-s)))

--------------------------------------------------------------------------------
-- Correctness of star

star-preserves : ∀{n} {nfa} {q : Fin n} {s}
  → T(accepts (star nfa) (fsuc q) s)
    ⇔
    ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts nfa q u) × star nfa ↓ v)
star-preserves {n} {nfa} {q} {s} =
  record { to = to s q ; from = from s q }
  where
  to : (s : String) (q : Fin n)
    → T(accepts (star nfa) (fsuc q) s)
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts nfa q u) × star nfa ↓ v)
  to [] q ac = [] , [] , refl , ac , tt
  to (x ∷ s) q ac with nextState {_}{x}{s}{fsuc q}{star nfa} ac
  to (x ∷ s) q ac | w , t , f with q ∈? F nfa
  to (x ∷ s) q ac | w , t , f | yes p with skipEmptyFirst w t
  ... | fst , refl with split-a∪b (δ nfa (S nfa) x) (δ nfa q x) fst t
  ... | inj₁ y = [] , x ∷ s , refl , p , fromExists (fst , joinAnd y f)
  ... | inj₂ y with to s fst f
  ... | u , v , eq , acind , decind =
    x ∷ u , v , cong (_∷_ x) eq , fromExists (fst , joinAnd y acind) , decind
  to (x ∷ s) q ac | w , t , f | no ¬p with skipEmptyFirst w t
  ... | fst , refl with to s fst f
  ... | u , v , eq , acind , decind =
    x ∷ u , v , cong (_∷_ x) eq , fromExists (fst , joinAnd t acind) , decind

  from : (s : String) (q : Fin n)
    → ∃[ u ] ∃[ v ] (s ≡ u ++ˢ v × T(accepts nfa q u) × star nfa ↓ v)
    → T(accepts (star nfa) (fsuc q) s)
  from _ q ([] , [] , refl , fst , snd) = fst
  from _ q ([] , c ∷ v , refl , fst , snd) with q ∈? F nfa
  ... | no ¬p = ⊥-elim(¬p (fst))
  ... | yes p with nextState {_} {c} {v} {0F} {star nfa} snd
  ... | fsuc w , t , f =
    fromExists (w , joinAnd (injectSetUnionʳ (δ nfa (S nfa) c) t) f)
  from _ q (c ∷ s , v , refl , fst , snd) with nextState {n}{c}{s} fst
  ... | w , t , f with q ∈? F nfa | from (s ++ˢ v) w (s , v , refl , f , snd)
  ... | yes p | IH =
    fromExists (w , joinAnd (injectSetUnionˡ t (δ nfa (S nfa) c)) IH)
  ... | no ¬p | IH =
    fromExists (w , joinAnd t IH)

star-correct1 : ∀{n} {s v : String} {nfa : Nfa n}
  → nfa ↓ s × (star nfa) ↓ v
  → (star nfa) ↓ (s ++ˢ v)
star-correct1 {n} {[]} {v} (fst , snd) = snd
star-correct1 {n} {c ∷ s} {v} (fst , snd) with nextState {n}{c}{s} fst
... | w , t , f with (_⇔_.from star-preserves (s , v , refl , f , snd))
... | ac = fromExists (w , joinAnd t ac)

star-correct2 : ∀{n} {nfa : Nfa n}
  → (a : Σ) (s : String)
  → (star nfa) ↓ (a ∷ s)
  → ∃[ u ] ∃[ v ](s ≡ u ++ˢ v × nfa ↓ (a ∷ u) × star nfa ↓ v)
star-correct2 {n} a s ds with nextState {suc n}{a}{s}{0F} ds
... | w , t , f with skipEmptyFirst w t
... | fst , refl with _⇔_.to star-preserves f
... | u , v , eq , acind , decind =
  u , v , eq , fromExists (fst , joinAnd t acind) , decind

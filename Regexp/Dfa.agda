open import Data.Nat as ℕ using (ℕ; zero; suc; _≥_; _≤_; _<_; s≤s; z≤n; _+_; _*_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; toℕ; inject+; raise; 0F; 1F; 2F; 3F; 4F; 5F; 6F) renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-inject+)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product using (_×_; Σ; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v; _++_ to _++v_) hiding (take; drop)
open import Data.Vec.Properties using (lookup-++ˡ)
open import Data.Fin.Subset as Subset using (Subset; ∁)
open import VecUtil

module Dfa (Σ : Set) where
open import String Σ

ε = []

record Dfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Σ → Fin n
    F : Subset n
open Dfa

δ^ : ∀{n} → (dfa : Dfa n) → (q : Fin n) → String → Fin n
δ^ dfa q [] = q
δ^ dfa q (x ∷ s) = δ^ dfa (δ dfa q x) s

infix 10 _↓_
_↓_ : ∀{n} → Dfa n → String → Set
dfa ↓ s  = δ^ dfa (S dfa) s ∈ F dfa

_↓?_ : ∀{n} → (dfa : Dfa n) → (s : String) → Dec (dfa ↓ s)
dfa ↓? s = δ^ dfa (S dfa) s ∈? F dfa

--------------------------------------------------------------------------------
-- Complement of a DFA

∁dfa : ∀{n} → Dfa n → Dfa n
∁dfa dfa =
  record
    { S = S dfa
    ; δ = δ dfa
    ; F = ∁ (F dfa)
    }

∁dfa-same-δ^ : ∀{n} → (dfa : Dfa n) (q : Fin n) (s : String)
  → δ^ (∁dfa dfa) q s ≡ δ^ dfa q s
∁dfa-same-δ^ dfa q [] = refl
∁dfa-same-δ^ dfa q (x ∷ s) = ∁dfa-same-δ^ dfa (δ dfa q x) s

x∈p⇒x∉∁p : ∀ {n x} → (p : Subset n) → x ∈ p → x ∉ ∁ p
x∈p⇒x∉∁p {_} {0F} (false ∷v p) a b = a
x∈p⇒x∉∁p {_} {0F} (true ∷v p) a b = b
x∈p⇒x∉∁p {_} {fsuc x} (_ ∷v p) a b = x∈p⇒x∉∁p {_}{x} p a b

x∉∁p⇒x∈p : ∀ {n x} → (p : Subset n) → x ∉ ∁ p → x ∈ p
x∉∁p⇒x∈p {_} {0F} (false ∷v p) ne = ne tt
x∉∁p⇒x∈p {_} {0F} (true ∷v p) ne = tt
x∉∁p⇒x∈p {_} {fsuc x} (_ ∷v p) ne = x∉∁p⇒x∈p {_}{x} p ne


∁dfa-correct : ∀{s n} {dfa : Dfa n}
  → (dfa ↓ s ⇔ ¬ (∁dfa dfa ↓ s))
∁dfa-correct {s}{n}{dfa} rewrite ∁dfa-same-δ^ dfa (S dfa) s =
  (x∈p⇒x∉∁p (F dfa)) IFF (x∉∁p⇒x∈p (F dfa))

--------------------------------------------------------------------------------
-- Pumping Lemma

infixl 6 _^_
_^_ : String → ℕ → String
s ^ zero = []
s ^ (suc n) = s ++ s ^ n

path : ∀{m} → Dfa m → Fin m → (s : String) → Vec (Fin m) (length s)
path dfa q [] = []v
path dfa q (c ∷ s) = q ∷v (path dfa (δ dfa q c) s)

lemmaPath : ∀{m}
  → (dfa : Dfa m)
  → (s : String)
  → (i : Fin (length s))
  → (q : Fin m)
  → path dfa q s ! i ≡ δ^ dfa q (take (toℕ i) s)
lemmaPath dfa (c ∷ s) fzero q = refl
lemmaPath dfa (c ∷ s) (fsuc i) q = lemmaPath dfa s i (δ dfa q c)

lemma-δ^ : ∀{n}
  (dfa : Dfa n)
  → (s : String)
  → (t : String)
  → (q : Fin n)
  → δ^ dfa q (s ++ t) ≡ δ^ dfa (δ^ dfa q s) t
lemma-δ^ dfa [] t q = refl
lemma-δ^ dfa (c ∷ s) t q = lemma-δ^ dfa s t (δ dfa q c)

returns-back : ∀{n}
  → (dfa : Dfa n)
  → (s : String)
  → (q : Fin n)
  → q ≡ δ^ dfa q s
  → ∀(m : ℕ) → q ≡ δ^ dfa q (s ^ m)
returns-back dfa s q eq zero = refl
returns-back dfa s q eq (suc m) with
  returns-back dfa s q eq m | lemma-δ^ dfa s (s ^ m) q
... | ind | lm2 rewrite sym eq = trans ind (sym lm2)

pumping-same-state : ∀{n} {dfa : Dfa n}
  → (s : String)
  → (t : String)
  → (u : String)
  → let p = δ^ dfa (S dfa) s in
     p ≡ δ^ dfa p t
  → dfa ↓ (s ++ t ++ u)
  → ∀ (m : ℕ) → dfa ↓ (s ++ t ^ m ++ u)
pumping-same-state {n} {dfa} s t u p≡δ^_pt dfa↓stu m with
  returns-back dfa t (δ^ dfa (S dfa) s) p≡δ^_pt m
... | pump with   lemma-δ^ dfa (s ++ t)       u       (S dfa)
                | lemma-δ^ dfa s              (t ^ m) (S dfa)
                | lemma-δ^ dfa s              t       (S dfa)
                | lemma-δ^ dfa (s ++ (t ^ m)) u       (S dfa)
... | d1 | d2 | d3 | d4 rewrite
                      trans pump (sym d2)
                    | sym (trans p≡δ^_pt (sym d3))
                    | ++-assoc s t u
                    | ++-assoc s (t ^ m) u
                    | trans d1 (sym d4) = dfa↓stu

take++drop : (n : ℕ) → (s : String) → s ≡ take n s ++ drop n s
take++drop zero s = refl
take++drop (suc n) [] = refl
take++drop (suc n) (c ∷ s) = cong (c ∷_) (take++drop n s)

lemminoTakeDrop1 : ∀{s : String} → {i j : Fin (length s)}
  → i <ᶠ j
  → s ≡ take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ++ drop (toℕ j) s
lemminoTakeDrop1 {c ∷ s} {fzero} {fsuc j} (s≤s z≤n) = cong (c ∷_) (take++drop (toℕ j) s)
lemminoTakeDrop1 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop1 {s} i<j)

lemminoTakeDrop2 : ∀{s : String} → {i j : Fin (length s)}
  → i <ᶠ j
  → drop (toℕ i) (take (toℕ j) s) ≢ []
lemminoTakeDrop2 {c ∷ s} {fzero} {fsuc j} i<j = λ ()
lemminoTakeDrop2 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) eq = ⊥-elim (lemminoTakeDrop2 {s} i<j eq)

lemminoTakeDrop3 : ∀{s : String} → {i j : Fin (length s)}
  → i <ᶠ j
  → take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ≡ take (toℕ j) s
lemminoTakeDrop3 {c ∷ s} {fzero} {fsuc j} i<j = refl
lemminoTakeDrop3 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop3 {s} i<j)

lemminoTakeDrop5 : (s : String)
  → (i : Fin (length s))
  → length (take (toℕ i) s) ≡ toℕ i
lemminoTakeDrop5 (x ∷ s) Data.Fin.0F = refl
lemminoTakeDrop5 (x ∷ s) (fsuc i) = cong suc (lemminoTakeDrop5 s i)

lemminoTakeDrop4 : ∀{s : String}
  → {i j : Fin (length s)}
  → i <ᶠ j
  → length (take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s)) ≡ toℕ j
lemminoTakeDrop4 {x ∷ s} {fzero} {fsuc j} i<j rewrite sym (lemminoTakeDrop3 {x ∷ s} i<j) = cong suc (lemminoTakeDrop5 s j)
lemminoTakeDrop4 {x ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong suc (lemminoTakeDrop4 {s} i<j)

tripartition : (s : String)
  → (i j : Fin (length s))
  → i <ᶠ j
  → ∃[ x ] ∃[ y ] ∃[ z ] (
      s ≡ x ++ y ++ z
      × y ≢ []
      × x ≡ take (toℕ i) s
      × (x ++ y) ≡ take (toℕ j) s
      × length (x ++ y) ≡ toℕ j
    )
tripartition s i j i<j = take (toℕ i) s , drop (toℕ i) (take (toℕ j) s) , drop (toℕ j) s
  , lemminoTakeDrop1 i<j
  , lemminoTakeDrop2 i<j
  , refl
  , lemminoTakeDrop3 i<j
  , lemminoTakeDrop4 i<j

lemmino≢ : ∀{p}{m n : Fin p} → fsuc m ≢ fsuc n → m ≢ n
lemmino≢ {_} {fzero} {fzero} neq =  λ _ → neq refl
lemmino≢ {_} {fsuc m} {fsuc n} neq eq = ⊥-elim (neq (cong fsuc eq))

<-total : ∀{p}{m n : Fin p} → m ≢ n → (m <ᶠ n) ⊎ (n <ᶠ m)
<-total {_} {fzero} {fzero} neq = ⊥-elim (neq refl)
<-total {_} {fzero} {fsuc n} neq = inj₁ (s≤s z≤n)
<-total {_} {fsuc m} {fzero} neq = inj₂ (s≤s z≤n)
<-total {_} {fsuc m} {fsuc n} neq with <-total (lemmino≢ neq)
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ y = inj₂ (s≤s y)

n<1+n : (n : ℕ) → n < suc n
n<1+n zero = s≤s z≤n
n<1+n (suc n) = s≤s (n<1+n n)

lemmamtoℕ : ∀{n} → (j : Fin (suc n)) → toℕ j ≤ n
lemmamtoℕ {n} fzero = z≤n
lemmamtoℕ {suc n} (fsuc j) = s≤s (lemmamtoℕ j)

lemman<m : ∀{n m} → n < m → ∃[ p ] ((suc n) + p ≡ m)
lemman<m {zero} {suc m} n<m = m , refl
lemman<m {suc n} {suc m} (s≤s n<m) with lemman<m {n} {m} n<m
...| p , snd = p , cong suc snd

pigeonHoleLimit : ∀{n}
  → (vec : Vec (Fin n) (suc n))
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × (vec ! i ≡ vec ! j))
pigeonHoleLimit {n} vec with pigeonhole (n<1+n n) (λ i → vec ! i)
... | i , j , neq , eq with <-total neq
... | inj₁ x = i , j , x , lemmamtoℕ j , eq
... | inj₂ y = j , i , y , lemmamtoℕ i , (sym eq)


pigeonholeVec : ∀{n m}
  → (vec : Vec (Fin n) m)
  → n < m
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × vec ! i ≡ vec ! j)
pigeonholeVec {n} {m} vec n<m with lemman<m n<m
... | p , eq rewrite sym eq with splitAt (suc n) vec
... | l , r , e with pigeonHoleLimit l
... | i , j , i<j , j≤n , eq2 with trans (subst (_≡ l ! j) (sym (lookup-++ˡ l r i)) eq2) (sym (lookup-++ˡ l r j))
... | injEq rewrite sym e with toℕ-inject+ p i | toℕ-inject+ p j
... | toinjI | toinjJ with subst (_≤ n) toinjJ j≤n
... | j≤m with subst (suc (toℕ (inject+ p i)) ≤_) toinjJ (subst (λ x → suc x ≤ toℕ j) toinjI i<j)
... | inji<j = inject+ p i , inject+ p j , inji<j , j≤m , injEq

pumpingLemma : {m : ℕ}
  → (dfa : Dfa m)
  → ∃[ n ] (
    ∀(w : String)
    → dfa ↓ w
    → n < length w
    → ∃[ x ] ∃[ y ] ∃[ z ] (
        w ≡ x ++ y ++ z
        × y ≢ ε
        × length (x ++ y) ≤ n
        × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
      )
  )
pumpingLemma {m} dfa = m , base
  where
  base : ∀(w : String)
    → dfa ↓ w
    → m < length w
    → ∃[ x ] ∃[ y ] ∃[ z ] (
        w ≡ x ++ y ++ z
        × y ≢ []
        × length (x ++ y) ≤ m
        × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
      )
  base w dfa↓w m<len_w with
        pigeonholeVec (path dfa (S dfa) w) m<len_w
  ... | i , j , i<j , j≤n , eq  with
        tripartition w i j i<j
  ... | x , y , z , w≡xyz , y≢ε , x≡takeI , xy≡takeJ , len_xy≡J with
        lemmaPath dfa w i (S dfa) | lemmaPath dfa w j (S dfa)
  ... | lp1 | lp2 rewrite
        sym x≡takeI | sym xy≡takeJ | sym eq | sym len_xy≡J | w≡xyz =
    x , y , z , ( refl , y≢ε , j≤n
        , pumping-same-state x y z
            (trans (sym lp1) (trans lp2 (lemma-δ^ dfa x y (S dfa))))
            dfa↓w
      )

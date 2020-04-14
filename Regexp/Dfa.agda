module Dfa where
open import Data.Char using (Char)
open import Data.Nat using (ℕ; zero; suc; _≥_; _≤_; _<_; s≤s; z≤n; _+_)
open import Data.Fin using (Fin; toℕ; inject+; raise) renaming (_<_ to _<ᶠ_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; toℕ-inject+)
open import Data.Bool using (Bool; false; true; not; T)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; []; _++_; length; take; drop)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; Σ; ∃; ∃₂; Σ-syntax; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_; subst; sym; trans; cong; cong₂)
open import Data.Vec renaming (_∷_ to _∷v_; [] to []v; _++_ to _++v_) hiding (take; drop)
open import Data.Vec.Properties using (lookup-++ˡ)
open import VecUtil

String : Set
String = List Char

record Dfa (n : ℕ) : Set where
  field
    S : Fin n
    δ : Fin n → Char → Fin n
    isF : Fin n → Bool

δ̂ : ∀{n} → (Fin n → Char → Fin n) → (q : Fin n) → String → Fin n
δ̂ δ q [] = q
δ̂ δ q (x ∷ s) = δ̂ δ (δ q x) s

infix 10 _↓_
_↓_ : ∀{n} → Dfa n → String → Set
dfa ↓ s  = T (Dfa.isF dfa (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s))

_↓?_ : ∀{n} → (dfa : Dfa n) → (s : String) → Dec (dfa ↓ s)
dfa ↓? s with Dfa.isF dfa (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s)
... | false = no (λ z → z)
... | true = yes tt

complement : ∀{n} → Dfa n → Dfa n
complement dfa =
  record
    { S = Dfa.S dfa
    ; δ = Dfa.δ dfa
    ; isF = λ x → not (Dfa.isF dfa x)
    }

not-elim : ∀{b} → T b → T (not b) → ⊥
not-elim {false} x y = x
not-elim {true} x y = y

¬not-elim : ∀{b} → ¬ T b → ¬ T (not b) → ⊥
¬not-elim {false} x y = y tt
¬not-elim {true} x y = y (x tt)

complement-closure : ∀{s n} {dfa : Dfa n}
  → dfa ↓ s ⇔ ¬ (complement dfa ↓ s)
complement-closure {s}{n}{dfa} = record { to = to {s}{n}{dfa} ; from = from {s}{n}{dfa} }
  where
    to : ∀{s n} {dfa : Dfa n} → dfa ↓ s → ¬ (complement dfa ↓ s)
    to {s} {n} {dfa} p with dfa ↓? s
    ... | yes q = λ x → not-elim p x
    ... | no ¬p = λ _ → ¬p p
    from : ∀{s n} {dfa : Dfa n} → ¬ (complement dfa ↓ s) → dfa ↓ s
    from {s} {n} {dfa} np with (complement dfa) ↓? s | dfa ↓? s
    ... | yes p | yes q = q
    ... | yes p | no ¬q = ⊥-elim (np p)
    ... | no ¬p | yes q = q
    ... | no ¬p | no ¬q = ⊥-elim (¬not-elim ¬q np)

_^_ : String → ℕ → String
s ^ zero = []
s ^ (suc n) = s ++ s ^ n

lemma-δ̂ : ∀{n}
  (dfa : Dfa n)
  → (s : String)
  → (t : String)
  → (q : Fin n)
  → δ̂ (Dfa.δ dfa) q (s ++ t) ≡ δ̂ (Dfa.δ dfa) (δ̂ (Dfa.δ dfa) q s) t
lemma-δ̂ dfa [] t q = refl
lemma-δ̂ dfa (c ∷ s) t q = lemma-δ̂ dfa s t (Dfa.δ dfa q c)

smallPumping : ∀{n}
  → (dfa : Dfa n)
  → (s : String)
  → (q : Fin n)
  → q ≡ δ̂ (Dfa.δ dfa) q s
  → ∀(m : ℕ) → q ≡ δ̂ (Dfa.δ dfa) q (s ^ m)
smallPumping dfa s q eq zero = refl
smallPumping dfa s q eq (suc m) with smallPumping dfa s q eq m | lemma-δ̂ dfa s (s ^ m) q
... | ind | lm2 with subst (λ x → δ̂ (Dfa.δ dfa) q (s ++ (s ^ m)) ≡ δ̂ (Dfa.δ dfa) x (s ^ m)) (sym eq) lm2
... | conc = trans ind (sym conc)

bigPumping : ∀{n} {dfa : Dfa n}
  → (s : String)
  → (t : String)
  → (u : String)
  → let p = δ̂ (Dfa.δ dfa) (Dfa.S dfa) s in
     p ≡ δ̂ (Dfa.δ dfa) p t
  → dfa ↓ (s ++ t ++ u)
  → (m : ℕ)
  → dfa ↓ (s ++ t ^ m ++ u)
bigPumping {n} {dfa} s t u eq2 dec m with smallPumping dfa t (δ̂ (Dfa.δ dfa) (Dfa.S dfa) s) eq2 m
... | nlbl with lemma-δ̂ dfa (s ++ t) u (Dfa.S dfa)
... | lm with lemma-δ̂ dfa s (t ^ m) (Dfa.S dfa)
... | lm2 with lemma-δ̂ dfa s t (Dfa.S dfa)
... | lm3 with trans nlbl (sym lm2)
... | ok with trans eq2 (sym lm3)
... | calm with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ t) ++ u) ≡ δ̂ (Dfa.δ dfa) x u) (sym calm) lm
... | almost with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ t) ++ u) ≡ δ̂ (Dfa.δ dfa) x u) ok almost
... | gotit with lemma-δ̂ dfa (s ++ (t ^ m)) u (Dfa.S dfa)
... | doable with trans gotit (sym doable)
... | notrly with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) x ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) ((s ++ (t ^ m)) ++ u)) (++-assoc s t u) notrly
... | gg with subst (λ x → δ̂ (Dfa.δ dfa) (Dfa.S dfa) (s ++ t ++ u) ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) x) (++-assoc s (t ^ m) u) gg
... | easy = subst (λ x → T (Dfa.isF dfa x)) easy dec

path : ∀{m} → Dfa m → Fin m → (s : String) → Vec (Fin m) (length s)
path dfa q [] = []v
path dfa q (c ∷ s) = q ∷v (path dfa (Dfa.δ dfa q c) s)

take++drop : (n : ℕ) → (s : String) → s ≡ take n s ++ drop n s
take++drop zero s = refl
take++drop (suc n) [] = refl
take++drop (suc n) (c ∷ s) = cong (c ∷_) (take++drop n s)

lemminoTakeDrop1 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → s ≡ take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ++ drop (toℕ j) s
lemminoTakeDrop1 {c ∷ s} {fzero} {fsuc j} (s≤s z≤n) = cong (c ∷_) (take++drop (toℕ j) s)
lemminoTakeDrop1 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop1 {s} i<j)

lemminoTakeDrop2 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → drop (toℕ i) (take (toℕ j) s) ≢ []
lemminoTakeDrop2 {c ∷ s} {fzero} {fsuc j} i<j = λ ()
lemminoTakeDrop2 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) eq = ⊥-elim (lemminoTakeDrop2 {s} i<j eq)

lemminoTakeDrop3 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s) ≡ take (toℕ j) s
lemminoTakeDrop3 {c ∷ s} {fzero} {fsuc j} i<j = refl
lemminoTakeDrop3 {c ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong (c ∷_) (lemminoTakeDrop3 {s} i<j)

lemminoTakeDrop5 : (s : String) → (i : Fin (length s)) → length (take (toℕ i) s) ≡ toℕ i
lemminoTakeDrop5 (x ∷ s) Data.Fin.0F = refl
lemminoTakeDrop5 (x ∷ s) (fsuc i) = cong suc (lemminoTakeDrop5 s i)

lemminoTakeDrop4 : ∀{s : String} → {i j : Fin (length s)} → i <ᶠ j → length (take (toℕ i) s ++ drop (toℕ i) (take (toℕ j) s)) ≡ toℕ j
lemminoTakeDrop4 {x ∷ s} {fzero} {fsuc j} i<j rewrite sym (lemminoTakeDrop3 {x ∷ s} i<j) = cong suc (lemminoTakeDrop5 s j)
lemminoTakeDrop4 {x ∷ s} {fsuc i} {fsuc j} (s≤s i<j) = cong suc (lemminoTakeDrop4 {s} i<j)

tripartition : (s : String)
  → (i j : Fin (length s))
  → i <ᶠ j
  → (∃₂ λ (x : String) (y : String) → ∃ λ (z : String) →
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

piccionaiaLimit : ∀{n}
  → (vec : Vec (Fin n) (suc n))
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × (vec ! i ≡ vec ! j))
piccionaiaLimit {n} vec with pigeonhole (n<1+n n) (λ i → vec ! i)
... | i , j , neq , eq with <-total neq
... | inj₁ x = i , j , x , lemmamtoℕ j , eq
... | inj₂ y = j , i , y , lemmamtoℕ i , (sym eq)

piccionaia : ∀{n m}
  → (vec : Vec (Fin n) m)
  → n < m
  → ∃[ i ] ∃[ j ] (i <ᶠ j × toℕ j ≤ n × (vec ! i ≡ vec ! j))
piccionaia {n} {m} vec n<m with lemman<m n<m
... | p , eq rewrite sym eq with splitAt (suc n) vec
... | l , r , e with piccionaiaLimit l
... | i , j , i<j , j≤n , eq2 with trans (subst (_≡ l ! j) (sym (lookup-++ˡ l r i)) eq2) (sym (lookup-++ˡ l r j))
... | injEq rewrite sym e with toℕ-inject+ p i | toℕ-inject+ p j
... | toinjI | toinjJ with subst (_≤ n) toinjJ j≤n
... | j≤m with subst (suc (toℕ (inject+ p i)) ≤_) toinjJ (subst (λ x → suc x ≤ toℕ j) toinjI i<j)
... | inji<j = inject+ p i , inject+ p j , inji<j , j≤m , injEq

lemmaPath : ∀{m}
  → (dfa : Dfa m)
  → (s : String)
  → (i : Fin (length s))
  → (q : Fin m)
  → (path dfa q s ! i) ≡ δ̂ (Dfa.δ dfa) q (take (toℕ i) s)
lemmaPath dfa (c ∷ s) fzero q = refl
lemmaPath dfa (c ∷ s) (fsuc i) q = lemmaPath dfa s i (Dfa.δ dfa q c)

pumingLemmaBase : ∀{n : ℕ}
  → (dfa : Dfa n)
  → ∀(w : String)
  → dfa ↓ w
  → n < length w
  → ∃[ x ] ∃[ y ] ∃[ z ] (
      w ≡ x ++ y ++ z
      × ¬(y ≡ [])
      × length (x ++ y) ≤ n
      × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
    )
pumingLemmaBase {n} dfa w dec gt with piccionaia (path dfa (Dfa.S dfa) w) gt
... | i , j , i<j , lt , eq  with tripartition w i j i<j
... | x , y , z , eq2 , y≢[] , bydef1 , bydef2 , lenp with lemmaPath dfa w i (Dfa.S dfa) | lemmaPath dfa w j (Dfa.S dfa)
... | lp1 | lp2 with subst (λ v → (path dfa (Dfa.S dfa) w) ! i ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) v) (sym bydef1) lp1
... | u1 with subst (λ v → (path dfa (Dfa.S dfa) w) ! j ≡ δ̂ (Dfa.δ dfa) (Dfa.S dfa) v) (sym bydef2) lp2
... | u2 with trans u2 (lemma-δ̂ dfa x y (Dfa.S dfa))
... | u3 with subst (_≡ δ̂ (Dfa.δ dfa) (δ̂ (Dfa.δ dfa) (Dfa.S dfa) x) y) (sym eq) u3
... | u4 = x , y , z , ( eq2 , y≢[] , subst (_≤ n) (sym lenp) lt , bigPumping {n}{dfa} x y z (trans (sym u1) u4) (subst (dfa ↓_) eq2 dec) )

pumpingLemma : {m : ℕ}
  → (dfa : Dfa m)
  → ∃[ n ] (
    ∀(w : String)
    → dfa ↓ w
    → n < length w
    → ∃[ x ] ∃[ y ] ∃[ z ] (
        w ≡ x ++ y ++ z
        × ¬(y ≡ [])
        × length (x ++ y) ≤ n
        × ∀(k : ℕ) → dfa ↓ (x ++ y ^ k ++ z)
      )
  )
pumpingLemma {m} dfa = m , pumingLemmaBase dfa



















--

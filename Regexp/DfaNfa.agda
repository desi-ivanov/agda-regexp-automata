module DfaNfa where
open import Dfa renaming (δ̂ to δ̂ᵈ; _↓_ to _↓ᵈ_; _↓?_ to _↓ᵈ?_)
open import Nfa renaming (δ̂ to δ̂ⁿ; _↓_ to _↓ⁿ_; _↓?_ to _↓ⁿ?_)
open import Data.Bool using (Bool; false; true; not; T; _∨_; _∧_)
open import Data.Char using (Char)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc; _^_; _*_; _<_; _+_; _≤_; s≤s; z≤n; pred)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; toℕ; fromℕ≤; fromℕ; inject≤; 0F; 1F; 2F)
  renaming (suc to fsuc; zero to fzero)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Fin.Subset
  using (Subset; ⁅_⁆; _∪_; _∩_; _∈_; Nonempty)
  renaming (⊥ to ∅; ⊤ to FullSet)
open import Data.Vec
  using (zipWith; _[_]=_; here; there; toList; tabulate; replicate; sum; _[_]%=_; _[_]≔_; reverse)
  renaming (_∷_ to _∷v_; [] to []v)
open import String
open import VecUtil
open import Equivalence
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; sym; trans; cong)
open Eq.≡-Reasoning

-- Dfa ⊆ Nfa

DfaToNfa : ∀{n} → Dfa n → Nfa n
DfaToNfa dfa =
  record
    { S = Dfa.S dfa
    ; δ = λ q c → ⁅ Dfa.δ dfa q c ⁆
    ; F = tabulate (Dfa.isF dfa)
    }

lemma-tabulate-! : ∀{n}{A : Set}
  → (i : Fin n)
  → (f : Fin n → A)
    -----------------
  → tabulate f ! i ≡ f i
lemma-tabulate-! Data.Fin.0F f = refl
lemma-tabulate-! (fsuc i) f = lemma-tabulate-! i (λ z → f (fsuc z))

replicate-false : ∀{n}
  → (f : Fin n → Bool)
    ---------------------------------------------
  → any (λ x → replicate false ! x ∧ f x) ≡ false
replicate-false {zero} f = refl
replicate-false {suc n} f = replicate-false (λ z → f (fsuc z))

any-singleton : ∀{n}
  → (f : Fin n → Bool)
  → (q : Fin n)
    ---------------------------------
  → any (λ p → ⁅ q ⁆ ! p ∧ f p) ≡ f q
any-singleton {n} f fzero with f fzero
... | false = replicate-false f
... | true = refl
any-singleton f (fsuc q) = any-singleton (λ z → f (fsuc z)) q

isF≡accepts : ∀{n}
  → (dfa : Dfa n)
  → (s : String)
  → (q : Fin n)
    -------------------------------------------------------------
  → Dfa.isF dfa (δ̂ᵈ dfa q s) ≡ accepts (DfaToNfa dfa) q s
isF≡accepts {n} dfa [] q = sym (lemma-tabulate-! q (Dfa.isF dfa))
isF≡accepts {n} dfa (c ∷ s) q with Dfa.δ dfa q c
... | p = trans (isF≡accepts dfa s p) (sym (any-singleton (λ r → accepts (DfaToNfa dfa) r s) p))

dfa⊆nfa : ∀{s n} {dfa : Dfa n}
  → dfa ↓ᵈ s ⇔ (DfaToNfa dfa) ↓ⁿ s
dfa⊆nfa {s}{n}{dfa} = record { to = to {s}{n}{dfa} ; from = from {s}{n}{dfa} }
  where
    to : ∀{s n} {dfa : Dfa n} → dfa ↓ᵈ s → DfaToNfa dfa ↓ⁿ s
    to {s} {n} {dfa} x = subst (λ y → T y) (isF≡accepts dfa s (Dfa.S dfa)) x

    from : ∀{s n} {dfa : Dfa n} → DfaToNfa dfa ↓ⁿ s → dfa ↓ᵈ s
    from {s} {n} {dfa} x = subst (λ y → T y) (sym (isF≡accepts dfa s (Dfa.S dfa))) x

postulate
  ISO : {n : ℕ} → Subset n ≃ Fin (2 ℕ.^ n)

NfaToDfa : ∀{n} → Nfa n → Dfa (2 ℕ.^ n)
NfaToDfa {n} nfa =
  record
    { S = _≃_.to ISO ⁅ Nfa.S nfa ⁆
    ; δ = λ q c → _≃_.to ISO (Uδ (_≃_.from ISO q) c)
    ; isF = λ p → any {n} λ q → (_≃_.from ISO p ! q) ∧ (Nfa.F nfa ! q)
    }
  where
    Uδ : Subset n → Char → Subset n
    Uδ Qset c = U (mapS Qset (λ q → Nfa.δ nfa q c) ∅)

open Nfa.Nfa

lem1 : ∀{n q} → T((⁅_⁆ {n} q) ! q)
lem1 {suc n} {Data.Fin.0F} = tt
lem1 {suc n} {fsuc q} = lem1 {n} {q}

lemz3 : ∀{n q p} → T((⁅_⁆ {n} q) ! p) → q ≡ p
lemz3 {suc n} {0F} {0F} d = refl
lemz3 {suc n} {0F} {fsuc p} d = contradiction (d) (¬x∈∅ {n})
lemz3 {suc n} {fsuc q} {fsuc p} d = cong fsuc (lemz3 d)

postulate
  lemz7 : ∀{n}{q}{x}{s}{i : Fin n}{nfa : Nfa n}
    → T(_≃_.from ISO (δ̂ᵈ (NfaToDfa nfa) (_≃_.to ISO (δ nfa q x)) s) ! i)
    → ∃[ w ] (T((δ nfa q x) ! w) ×  T(_≃_.from ISO (δ̂ᵈ (NfaToDfa nfa) (_≃_.to ISO ⁅ w ⁆) s) ! i))


lemz9 : ∀{n}
  → (ss : Subset n)
  → U (ss ∷v []v) ≡ ss
lemz9 []v = refl
lemz9 (false ∷v ss) = cong (_∷v_ false) (lemz9 ss)
lemz9 (true ∷v ss) = cong (_∷v_ true) (lemz9 ss)


lemz11 : ∀{n}{m}{ss}{i}
  → (f : Fin n → Subset m)
  → T(ss ! i)
  → ifPresentOrElse i ss f ∅ ≡ f i
lemz11 {_}{_}{ss}{i} f b with ss ! i
lemz11 {_}{_}{ss}{i} f b | true = refl

lemz10 : ∀{n}{w : Fin n}{c}{qs}{nfa}
  → T(qs ! w)
  → ifPresentOrElse w qs (λ p → δ nfa p c) ∅ ≡ (δ nfa w c)
lemz10 {n}{w}{c}{qs}{nfa} a  rewrite lemz11 {n}{n}{qs}{w} (λ z → δ nfa z c) a = refl
postulate
  lemz5 : ∀{n}{q}{f} → U {n}{n} (tabulate (λ i → ifPresentOrElse i ⁅ q ⁆ f ∅)) ≡ f q

kkk : ∀{A : Set}{n}{a : A}{l : Data.Vec.Vec A n}{r}
  → a ∷v l ≡ a ∷v r
  → (k : A)
  → a ∷v k ∷v l ≡ a ∷v k ∷v r
kkk refl k = refl

wot2 : ∀{n}{m}{f : Fin (suc n) → Subset m}{ss : Subset n}
  → tabulate (λ i → ifPresentOrElse (fsuc i) (false ∷v ss) f ∅)
  ≡ tabulate (λ i → ifPresentOrElse i ss (λ x → f (Data.Fin.inject₁ x)) ∅)
wot2 {0F} {m} {f} {ss} = refl
wot2 {suc n} {m} {f} {false ∷v ss} with wot2 {n}{m}{λ x → f (Data.Fin.inject₁ x)}{ss}
... | o = {!   !}
wot2 {suc n} {m} {f} {true ∷v ss} = {!   !}

wot : ∀{n}{m}
  → (q : Fin n)
  → (f : Fin n → Subset m)
  → tabulate (λ i → ifPresentOrElse i ⁅ q ⁆ f ∅) ≡ replicate ∅ [ q ]≔ f q
wot {1F} 0F f = refl
wot {suc (suc n)} 0F f with wot {suc n} 0F λ x → f (Data.Fin.inject₁ x)
... | i  with kkk {_}{n}{f 0F} i ∅
... | o rewrite sym o = {!   !}
wot {suc (suc n)} {m} (fsuc q) f with wot {suc n}{m} q λ x → f (fsuc x)
... | i  = {!   !}

lemz5p : (n m : ℕ) → (q : Fin n) → (f : Fin n → Subset m)
  → U (tabulate (λ i → ifPresentOrElse i ⁅ q ⁆ f ∅)) ≡ f q
lemz5p 1F m 0F f = lemz9 (f 0F)
lemz5p (suc (suc n)) 0F 0F f = {!   !}
lemz5p (suc (suc n)) 0F (fsuc q) f = {!   !}
lemz5p (suc (suc n)) (suc m) 0F f = {!   !}
lemz5p (suc (suc n)) (suc m) (fsuc q) f  with lemz5p (suc n) (suc m) q λ x → f (Data.Fin.inject₁  x)
... | IH rewrite IH = {!   !}

lemz8 : ∀{n}{w : Fin n}{c}{i}{qs}{nfa}
  → T(qs ! w)
  → T((δ nfa w c) ! i)
  → T((U (tabulate (λ j → ifPresentOrElse j qs (λ p → δ nfa p c) ∅))) ! i)
lemz8 {n}{w}{c}{i}{qs}{nfa} a b = {!   !}

lemz6p : ∀{n}{q}{x}{c}{w}{i : Fin n}{nfa : Nfa n}
    → T(δ nfa q x ! w)
    → T(_≃_.from ISO ((Dfa.δ (NfaToDfa nfa)) (_≃_.to ISO ⁅ w ⁆) c) ! i)
    → T(_≃_.from ISO ((Dfa.δ (NfaToDfa nfa)) (_≃_.to ISO (δ nfa q x)) c) ! i)
lemz6p {n}{q}{x}{c}{w}{i}{nfa} ac ds rewrite
                _≃_.from∘to ISO ⁅ w ⁆
                | _≃_.from∘to ISO (δ nfa q x)
                | lemz5 {n}{w}{λ z → δ nfa z c }
                | _≃_.from∘to ISO (δ nfa w c)
                | _≃_.from∘to ISO ((Data.Vec.foldr (λ _ → Data.Vec.Vec Bool n)
          (λ {n = n₁} → zipWith _∨_) (replicate false)
          (tabulate
           (λ i₁ →
              ifPresentOrElse i₁ (δ nfa q x) (λ q₁ → δ nfa q₁ c)
              (replicate false))))) = lemz8 {n}{w}{c}{i}{δ nfa q x}{nfa} ac ds
lemz6 : ∀{n}{q}{x}{s}{w}{i : Fin n}{nfa : Nfa n}
  → T(δ nfa q x ! w)
  → T(_≃_.from ISO (δ̂ᵈ (NfaToDfa nfa) (_≃_.to ISO ⁅ w ⁆) s) ! i)
  → T(_≃_.from ISO (δ̂ᵈ (NfaToDfa nfa) (_≃_.to ISO (δ nfa q x)) s) ! i)
lemz6 {n} {q} {x} {[]} {w} {i} {nfa} a b rewrite
      _≃_.from∘to ISO ⁅ w ⁆
    | _≃_.from∘to ISO (δ nfa q x)
    | lemz3 {n}{w}{i} b = a
lemz6 {n} {q} {x} {c ∷ s} {w} {i} {nfa} a b rewrite
      _≃_.from∘to ISO ⁅ w ⁆
    | _≃_.from∘to ISO (δ nfa q x)
    | lemz5 {n}{w}{λ z → δ nfa z c} with lemz6p {n}{q}{x}{c}{w}{i}{nfa} a {!   !}
... | pwr = {!   !}

lemz4 : ∀{n}{c}{q}{w} {nfa : Nfa n}
  → T(δ nfa q c ! w)
  → T((_≃_.from ISO (Dfa.δ (NfaToDfa nfa) (_≃_.to ISO ⁅ q ⁆) c)) ! w)
lemz4 {n}{c}{q}{w}{nfa} ac
  rewrite _≃_.from∘to ISO ⁅ q ⁆ | _≃_.from∘to ISO (Data.Vec.foldr (λ _ → Data.Vec.Vec Bool n)
          (λ {n = n₁} → zipWith _∨_) (replicate false)
          (tabulate
           (λ i →
              ifPresentOrElse i ⁅ q ⁆ (λ q₁ → δ nfa q₁ c) (replicate false))))
            | lemz5 {n}{q}{λ z → δ nfa z c } = ac

lemz : ∀{n} {s} {q} {nfa : Nfa n}
  → T(accepts nfa q s)
  → let dfa = NfaToDfa nfa in
    T (Dfa.isF dfa (Dfa.δ̂ dfa (_≃_.to ISO (⁅ q ⁆)) s))
lemz {n} {[]} {q} {nfa} ac rewrite _≃_.from∘to ISO (⁅ q ⁆) = fromExists (q , joinAnd (lem1 {_}{q}) ac )
lemz {n} {x ∷ s} {q} {nfa} ac with nextState {_}{x}{s}{q}{nfa} ac
... | w , t , f with lemz {n}{s}{w} f
... | ih with anyToExists {n} ih
... | i , ok with splitAnd {_}{(F nfa) ! i} ok
... | fst , snd with lemz4 {n}{x}{q}{w}{nfa} t
... | oo rewrite _≃_.from∘to ISO (⁅ q ⁆)
    | lemz5 {n}{q}{λ z → δ nfa z x } = fromExists (i , joinAnd (lemz6 {n}{q}{x}{s}{w}{i}{nfa} t (proj₁ (splitAnd ok))) snd )

lemz2 : ∀{n} {s} {q} {nfa : Nfa n}
  → let dfa = NfaToDfa nfa in
    T (Dfa.isF dfa (Dfa.δ̂ dfa (_≃_.to ISO ⁅ q ⁆) s))
  → T (accepts nfa q s)
lemz2 {n} {[]} {q} {nfa} ac rewrite _≃_.from∘to ISO (⁅ q ⁆) with anyToExists {n} ac
... | a , b  rewrite lemz3 {n}{q}{a} (proj₁ (splitAnd b)) = proj₂ (splitAnd b)
lemz2 {n} {x ∷ s} {q} {nfa} ac with anyToExists {n} ac
... | a , b rewrite _≃_.from∘to ISO (⁅ q ⁆) | lemz5 {n}{q}{λ z → δ nfa z x} with lemz7 {n}{q}{x}{s}{_}{nfa} (proj₁ (splitAnd b))
... | w , mm , dz with lemz2 {n}{s}{_}{nfa} (fromExists (a , joinAnd dz (proj₂ (splitAnd b))))
... | k = fromExists (w , joinAnd mm k)

nfa⊆dfa : ∀{s n} {nfa : Nfa n}
  → nfa ↓ⁿ s ⇔ (NfaToDfa nfa) ↓ᵈ s
nfa⊆dfa {s}{n}{nfa} = record { to = to {s} ; from = from {s} }
  where
    to : ∀{s} → nfa ↓ⁿ s → NfaToDfa nfa ↓ᵈ s
    to {s} ds = lemz {n}{s} ds

    from : ∀{s} → NfaToDfa nfa ↓ᵈ s → nfa ↓ⁿ s
    from {s} ds = lemz2 {n}{s} ds

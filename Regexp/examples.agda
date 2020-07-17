open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T; Bool; true; false; if_then_else_; _∧_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Equivalence
open import Data.Nat using (ℕ; _≟_; zero; suc)

module examples where

a = zero
b = suc zero
c = suc (suc zero)

Σ = ℕ
open import String Σ hiding (foldl)
open import Regexp Σ
open import Brzozowski Σ _≟_
open import RegexpNfa Σ _≟_ as RegNFA hiding (_∈?_)

a* = Atom a *
b* = Atom b *

⟨aa⟩* = (Atom a · Atom a) *
a*b?a* = Atom a * · (Atom b + ⟨ε⟩) · Atom a *
a*b* = Atom a * · Atom b *
[a[c+b]]* = (Atom a · (Atom c + Atom b)) *

⟨a+b⟩*a = (Atom a + Atom b) * · Atom a

module membership-examples where
  x : (a ∷ a ∷ a ∷ a ∷ []) ∈ ⟨aa⟩*
  x = in-*2 (in-· (in-c a) (in-c a))
          (in-*2 (in-· (in-c a) (in-c a)) in-*1)
  y : (a ∷ b ∷ a ∷ []) ∈ a*b?a*
  y = in-· (in-· (in-*2 (in-c a) in-*1)
                 (in+l (in-c b)))
           (in-*2 (in-c a) in-*1)

  z : (a ∷ a ∷ b ∷ b ∷ b ∷ []) ∈ a*b*
  z = in-· (in-*2 (in-c a)
              (in-*2 (in-c a) in-*1))
           (in-*2 (in-c b)
              (in-*2 (in-c b)
                (in-*2 (in-c b) in-*1)))

  v : (a ∷ b ∷ a ∷ c ∷ []) ∈ [a[c+b]]*
  v =  in-*2 (in-· (in-c a) (in+r (in-c b)))
            (in-*2
              (in-· (in-c a) (in+l (in-c c))) in-*1)

  _ : (a ∷ b ∷ a ∷ []) ∈ ⟨a+b⟩*a
  _ = in-· (in-*2 (in+l (in-c a)) (in-*2 (in+r (in-c b)) in-*1)) (in-c a)

  open Nullable

  _ = {!  (b ∷ []) ∈? ⟨a+b⟩*a  !}


module nullable-examples where
  x : Nullable ⟨aa⟩*
  x = null*

  y : Nullable a*b?a*
  y = null· (null· null* (null+r null⟨ε⟩)) null*

  z : Nullable a*b*
  z = null· null* null*

  u : Nullable [a[c+b]]*
  u = null*

  v : ¬ Nullable (Atom a)
  v = λ ()

module derivative-examples where
  x : ⟨aa⟩* [ a ] ≡ ⟨ε⟩ · Atom a · ⟨aa⟩*
  x = refl

  y : ⟨aa⟩* [ b ] ≡ ⟨⟩ · Atom a · ⟨aa⟩*
  y = refl

  yp : ∀{s} → ¬ s ∈ ⟨aa⟩* [ b ]
  yp (in-· (in-· () _) _)

  x1 : (a ∷ a ∷ a ∷ a ∷ []) ∈ ⟨aa⟩*
  x1 = in-*2 (in-· (in-c a) (in-c a))
             (in-*2 (in-· (in-c a) (in-c a)) in-*1)

  x2 : (a ∷ a ∷ a ∷ []) ∈ (⟨aa⟩* [ a ])
  x2 = in-· (in-· in-ε (in-c a))
             (in-*2 (in-· (in-c a) (in-c a)) in-*1)

  x3 : (a ∷ a ∷ []) ∈ (⟨aa⟩* [ a ] [ a ])
  x3 = in-· (in+r in-ε)
            (in-*2 (in-· (in-c a) (in-c a)) in-*1)

module decidable-Brzozowski-examples where
  v = (a ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ [])

  e1 = v ∈? a*b?a*

  _ = {! (a ∷ []) ∈? ⟨aa⟩*  !}
  
  e2 = (b ∷ b ∷ []) ∈? a*b?a*

  x : v ∈ a*b?a*
  x = (in-· (in-· (in-*2 (in-c a) in-*1) (in+l (in-c b)))
   (in-*2 (in-c a)
    (in-*2 (in-c a)
     (in-*2 (in-c a)
      (in-*2 (in-c a)
       (in-*2 (in-c a)
        (in-*2 (in-c a) (in-*2 (in-c a) (in-*2 (in-c a) in-*1)))))))))

module dfa-examples where
  open import Dfa Σ
  open import Data.Fin renaming (_≟_ to _≟ᶠ_)
  open import Data.Fin.Subset
  open import Data.Vec hiding (foldl; map; _++_)
  open import Data.List hiding(_++_)

  TransitionsList = λ n → List (Fin n × Σ × Fin n)

  make-δ : ∀{n}
    → Fin n
    → TransitionsList n
    → (Fin n → Σ → Fin n)
  make-δ err [] = λ _ _ → err
  make-δ err ((q , x , p) ∷ xs)
    = λ h y → if ⌊ q ≟ᶠ h ⌋ ∧ ⌊ x ≟ y ⌋
              then p
              else make-δ err xs h y

  make-dfa : (n : ℕ)
    → Fin n
    → Fin n
    → List (Fin n)
    → TransitionsList n
    → Dfa n
  make-dfa n start error finals transitions
    = record
      { S = start
      ; δ = make-δ error transitions
      ; F = ⋃ (map ⁅_⁆ finals)
      }

  dfa-⟨aa⟩* = make-dfa 3 0F 2F (0F ∷ []) (
        (0F , a , 1F)
      ∷ (1F , a , 0F)
      ∷ []
    )

  p0 : dfa-⟨aa⟩* ↓ (a ∷ a ∷ [])
  p0 = tt

  p1 : ¬ dfa-⟨aa⟩* ↓ (a ∷ a ∷ a ∷ [])
  p1 ()

  dfa-a*b?a* = make-dfa 3 0F 2F (0F ∷ 1F ∷ []) (
        (0F , a , 0F)
      ∷ (0F , b , 1F)
      ∷ (1F , a , 1F)
      ∷ []
    )

  p2 : dfa-a*b?a* ↓ (a ∷ b ∷ a ∷ [])
  p2 = tt

  p3 : ¬ dfa-a*b?a* ↓ (b ∷ b ∷ a ∷ [])
  p3 ()

  p4 : dfa-a*b?a* ↓ (a ∷ a ∷ a ∷ [])
  p4 = tt

  dfa-a*b* = make-dfa 3 0F 2F (0F ∷ 1F ∷ []) (
        (0F , a , 0F)
      ∷ (0F , b , 1F)
      ∷ (1F , b , 1F)
      ∷ []
    )

  p5 : dfa-a*b* ↓ (a ∷ a ∷ b ∷ [])
  p5 = tt

  p6 : dfa-a*b* ↓ (b ∷ b ∷ b ∷ [])
  p6 = tt

  p7 : ¬ dfa-a*b* ↓ (c ∷ [])
  p7 ()

  dfa-[a[c+b]]* = make-dfa 3 0F 2F (0F ∷ []) (
        (0F , a , 1F)
      ∷ (1F , b , 0F)
      ∷ (1F , c , 0F)
      ∷ []
    )

  p8 : dfa-[a[c+b]]* ↓ []
  p8 = tt

  p9 : dfa-[a[c+b]]* ↓ (a ∷ c ∷ a ∷ b ∷ [])
  p9 = tt

  p10 : ¬ dfa-[a[c+b]]* ↓ (a ∷ a ∷ [])
  p10 ()

  open Data.Nat._≤_



  dfa-binary-multiples-5 = make-dfa 6 0F 5F (0F ∷ []) (
        (0F , 0 , 0F)
      ∷ (0F , 1 , 1F)
      ∷ (1F , 0 , 2F)
      ∷ (1F , 1 , 3F)
      ∷ (2F , 1 , 0F)
      ∷ (2F , 0 , 4F)
      ∷ (3F , 1 , 2F)
      ∷ (3F , 0 , 1F)
      ∷ (4F , 1 , 4F)
      ∷ (4F , 0 , 3F)
      ∷ []
    )

  -- [115] dec = [1110011] bin

  pumpLem = proj₂
              (pumpingLemma dfa-binary-multiples-5)
              (1 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ [])
              tt
              (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

  x : String
  x = 1 ∷ 1 ∷ []

  y : String
  y = 1 ∷ 0 ∷ 0 ∷ []

  z : String
  z = 1 ∷ 1 ∷ []

  acc1 : dfa-binary-multiples-5 ↓ (x ++ y ^ 0 ++ z)
  acc1 = tt

  acc2 : dfa-binary-multiples-5 ↓ (x ++ y ^ 3 ++ z)
  acc2 = tt

module nfa-examples where
  open import Nfa Σ
  open import Data.Fin renaming (_≟_ to _≟ᶠ_)
  open import Data.Fin.Subset
  open import Data.Vec hiding (foldl; map; _++_; concat)
  open import Data.List hiding (_++_; concat)

  NfaTransitionsList = λ n → List (Fin n × Σ × List (Fin n))

  make-nfa-δ : ∀{n}
    → Fin n
    → NfaTransitionsList n
    → (Fin n → Σ → Subset n)
  make-nfa-δ err [] = λ _ _ → ⁅ err ⁆
  make-nfa-δ err ((q , x , ps) ∷ xs)
    = λ h y → if ⌊ q ≟ᶠ h ⌋ ∧ ⌊ x ≟ y ⌋
              then ⋃ (map ⁅_⁆ ps)
              else make-nfa-δ err xs h y

  make-nfa : (n : ℕ)
    → Fin n
    → Fin n
    → List (Fin n)
    → NfaTransitionsList n
    → Nfa n
  make-nfa n start error finals transitions
    = record
      { S = start
      ; δ = make-nfa-δ error transitions
      ; F = ⋃ (map ⁅_⁆ finals)
      }


  nfa-babb-substring = make-nfa 6 0F 5F (4F ∷ []) (
        (0F , a , 0F ∷ [])
      ∷ (0F , b , 0F ∷ 1F ∷ [])
      ∷ (1F , a , 2F ∷ [])
      ∷ (2F , b , 3F ∷ [])
      ∷ (3F , b , 4F ∷ [])
      ∷ (4F , a , 4F ∷ [])
      ∷ (4F , b , 4F ∷ [])
      ∷ []
    )

  babb : String
  babb = b ∷ a ∷ b ∷ b ∷ []

  x : nfa-babb-substring ↓ babb
  x = tt

  evaluatePath : ∀{n}{A : Nfa n} → (q : Fin n) → ∀(xs) → T(accepts A q xs) → List (Fin n)
  evaluatePath q [] ac = []
  evaluatePath {n}{A} q (x ∷ xs) ac with nextState {n} {x} {xs} {q} {A} ac
  ... | p , inz , ok = p ∷ (evaluatePath {n}{A} p xs ok)

  y : nfa-babb-substring ↓ (a ∷ babb ++ b ∷ b ∷ [])
  y = tt

  z : ¬ nfa-babb-substring ↓ (a ∷ b ∷ a ∷ [])
  z ()

  nfa-term-by-abc = make-nfa 5 0F 4F (3F ∷ []) (
        (0F , a , 0F ∷ 1F ∷ [])
      ∷ (1F , b , 2F ∷ [])
      ∷ (2F , c , 3F ∷ [])
      ∷ []
    )

  abc : String
  abc = a ∷ b ∷ c ∷ []

  t : nfa-term-by-abc ↓ (abc)
  t = tt

  u : nfa-term-by-abc ↓ (a ∷ a ∷ a ∷ abc)
  u = tt

  v : ¬ nfa-term-by-abc ↓ (b ∷ a ∷ c ∷ [])
  v ()

  nfa-union-babb-abc = union nfa-babb-substring nfa-term-by-abc

  q : nfa-union-babb-abc ↓ (abc)
  q = tt

  r : nfa-union-babb-abc ↓ (b ∷ a ∷ b ∷ b ∷ [])
  r = tt

  s : ¬ nfa-union-babb-abc ↓ (b ∷ a ∷ c ∷ [])
  s ()

  nfa-concat-babb-abc = concat nfa-babb-substring nfa-term-by-abc

  o : nfa-concat-babb-abc ↓ (babb ++ abc)
  o = tt

  p : ¬ nfa-concat-babb-abc ↓ babb
  p ()

  nfa-star-term-abc = star nfa-term-by-abc

  k : nfa-star-term-abc ↓ (abc ++ abc)
  k = tt

  l : nfa-star-term-abc ↓ (abc ++ a ∷ a ∷ abc)
  l = tt

  m : ¬ nfa-star-term-abc ↓ (a ∷ abc ++ c ∷ c ∷ [])
  m ()

module regexp-nfa-examples where
  open import Nfa Σ
  open Nfa

  tnf = toNFA a*b?a*


  nfa = proj₁ (proj₂ tnf)
  iff = proj₂ (proj₂ tnf)

  -- x = (a ∷ a ∷ b ∷ a ∷ a ∷ a ∷ []) RegNFA.∈? a*b?a*

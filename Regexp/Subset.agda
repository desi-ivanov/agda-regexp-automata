open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Fin using (Fin; zero; suc; inject+; raise)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Nat using (ℕ; suc; zero; _^_; _*_; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Properties using ()
open import Data.Vec using ([]; _∷_)
open import Function using (_∘_; id)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; map)

open import Equivalence

[,]-∘-distr : ∀ {l} {A B C D : Set l} (f : A → B)
              {g : C → A} {h : D → A} →
              f ∘ [ g , h ] ≗ [ f ∘ g , f ∘ h ]
[,]-∘-distr _ (inj₁ _) = refl
[,]-∘-distr _ (inj₂ _) = refl

[,]-map-commute : ∀ {l} {A B C D E : Set l} {f : A → B}  {g : C → D}
                  {f′ : B → E} {g′ : D → E} →
                  [ f′ , g′ ] ∘ map f g ≗ [ f′ ∘ f , g′ ∘ g ]
[,]-map-commute (inj₁ _) = refl
[,]-map-commute (inj₂ _) = refl

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero    i       = inj₂ i
splitAt (suc m) zero    = inj₁ zero
splitAt (suc m) (suc i) = map suc id (splitAt m i)

splitAt-inject+ : ∀ m n i → splitAt m (inject+ n i) ≡ inj₁ i
splitAt-inject+ (suc m) n zero = refl
splitAt-inject+ (suc m) n (suc i) rewrite splitAt-inject+ m n i = refl

splitAt-raise : ∀ m n i → splitAt m (raise {n} m i) ≡ inj₂ i
splitAt-raise zero    n i = refl
splitAt-raise (suc m) n i rewrite splitAt-raise m n i = refl

inject+-raise-splitAt : ∀ m n i → [ inject+ n , raise {n} m ] (splitAt m i) ≡ i
inject+-raise-splitAt zero    n i       = refl
inject+-raise-splitAt (suc m) n zero    = refl
inject+-raise-splitAt (suc m) n (suc i) = begin
  [ inject+ n , raise {n} (suc m) ] (splitAt (suc m) (suc i))  ≡⟨ [,]-map-commute (splitAt m i) ⟩
  [ suc ∘ (inject+ n) , suc ∘ (raise {n} m) ] (splitAt m i)    ≡˘⟨ [,]-∘-distr suc (splitAt m i) ⟩
  suc ([ inject+ n , raise {n} m ] (splitAt m i))              ≡⟨ cong suc (inject+-raise-splitAt m n i) ⟩
  suc i                                                        ∎

sum-split : ∀ {m n} →
      Fin m ⊎ Fin n ≃ Fin (m + n)
sum-split {m}{n} = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
   where
      to : Fin m ⊎ Fin n → Fin (m + n)
      to = [ inject+ n , raise {n} m ]

      from : Fin (m + n)→ Fin m ⊎ Fin n
      from = splitAt m

      from∘to : ∀ (x : Fin m ⊎ Fin n) → from (to x) ≡ x
      from∘to (inj₁ x) = splitAt-inject+ m n x
      from∘to (inj₂ y) = splitAt-raise m n y

      to∘from : ∀ (x : Fin (m + n)) → to (from x) ≡ x
      to∘from = inject+-raise-splitAt m n

subset-suc : ∀ {n m} →
     Subset n       ≃ Fin m
   → Subset (suc n) ≃ Fin m ⊎ Fin m
subset-suc {n}{m} ev = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
   where
      to : Subset (suc n) → Fin m ⊎ Fin m
      to (outside ∷ r) = inj₁ (_≃_.to ev r)
      to (inside ∷ r) = inj₂ (_≃_.to ev r)

      from : Fin m ⊎ Fin m → Subset (suc n)
      from (inj₁ x) = outside ∷ (_≃_.from ev x)
      from (inj₂ y) = inside ∷ (_≃_.from ev y)

      from∘to : ∀ (x : Subset (suc n)) → from (to x) ≡ x
      from∘to (outside ∷ x) rewrite _≃_.from∘to ev x = refl
      from∘to (inside ∷ x) rewrite _≃_.from∘to ev x = refl

      to∘from : ∀ (x : Fin m ⊎ Fin m) → to (from x) ≡ x
      to∘from (inj₁ x) rewrite _≃_.to∘from ev x = refl
      to∘from (inj₂ y) rewrite _≃_.to∘from ev y = refl

subset-fin-iso : ∀ {n} → Subset n ≃ Fin (2 ^ n)
subset-fin-iso {zero} = record { to = λ _ → zero ; from = λ _ → [] ; from∘to = (λ { [] → refl }) ; to∘from = (λ { zero → refl }) }
subset-fin-iso {suc n} with subset-fin-iso {n}
... | IH@record { to = to⁺ ; from = from⁺ ; from∘to = from∘to⁺ ; to∘from = to∘from⁺ } rewrite +-identityʳ (2 ^ n) =
      record { to = to  ; from = from ; from∘to = from∘to ; to∘from = to∘from  }
   where
      to : Subset (suc n) → Fin (2 ^ n + 2 ^ n)
      to s = _≃_.to sum-split (_≃_.to (subset-suc IH) s)

      from : Fin (2 ^ n + 2 ^ n) → Subset (suc n)
      from f = _≃_.from (subset-suc IH) (_≃_.from sum-split f)

      from∘to : ∀ (x : Subset (suc n)) → from (to x) ≡ x
      from∘to s rewrite _≃_.from∘to (sum-split {2 ^ n}{2 ^ n}) (_≃_.to (subset-suc IH) s)
                      | _≃_.from∘to (subset-suc IH) s
                      = refl

      to∘from : ∀ (x : Fin (2 ^ n + 2 ^ n)) → to (from x) ≡ x
      to∘from f rewrite _≃_.to∘from (subset-suc IH) (_≃_.from (sum-split{2 ^ n}{2 ^ n}) f)
                      | _≃_.to∘from (sum-split {2 ^ n}{2 ^ n}) f
                      = refl

module lists where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ;  +-comm; *-comm; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; proj₁; proj₂;  ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Level using (Level)
open import quantifiers using (extensionalityDep)
open import isomorphism using (_≃_; _⇔_; extensionality)
open import introduction using (*-distrib-+; +-swap)
open import connectives using (_⊎_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

{-# BUILTIN LIST List #-}


infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = refl

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =  refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)

length : ∀ {A : Set} (xs : List A) → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length xs + length ys ≡ length (xs ++ ys)
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀ {A : Set} (xs : List A) → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

-- Show that the reverse of one list appended to another is
-- the reverse of the second appended to the reverse of the first:
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityˡ ys
                | ++-identityʳ (reverse ys) = refl
reverse-++-distrib xs [] rewrite ++-identityʳ xs  = refl
reverse-++-distrib (x ∷ xs) (y ∷ ys) rewrite
                reverse-++-distrib xs (y ∷ ys)
                | ++-assoc (reverse ys ++ [ y ]) (reverse xs) [ x ]  = refl

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ]
                            | reverse-involutive xs = refl

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

rpeqr :  ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
rpeqr xs =
  begin
      shunt xs []
    ≡⟨ shunt-reverse xs [] ⟩
      reverse xs ++ []
    ≡⟨ ++-identityʳ (reverse xs) ⟩
      reverse xs
    ∎
map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs



-- Prove that the map of a composition is equal to the composition of two maps:
-- map (g ∘ f) ≡ map g ∘ map f
map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} f g = extensionality map-compose-l
  where
    map-compose-l : (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    map-compose-l [] = refl
    map-compose-l (x ∷ xs) = cong (_∷_ (g (f x))) (map-compose-l xs)


-- Prove the following relationship between map and append:
-- map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl


data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  branch : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (branch l x r) = branch (map-Tree f g l) (g x) (map-Tree f g r)

foldl : ∀ {A B : Set} → (A → B → B) → B →  List A → B
foldl f b [] = b
foldl f b (x ∷ xs) = f x (foldl f b xs)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr f e []        =  e
foldr f e (x ∷ xs)  =  f x (foldr f e xs)

product : List ℕ → ℕ
product xs = foldl _*_ 1 xs

-- Show that fold and append are related as follows:
-- foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ : ∀ {A B : Set} (f : A → B → B) (e : B) (xs ys : List A)
  → foldr f e (xs ++ ys) ≡ foldr f (foldr f e ys) xs
foldr-++ f e [] ys = refl
foldr-++ f e (x ∷ xs) ys = cong (f x) (foldr-++ f e xs ys)

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = cong (_∷_ x) (foldr-∷ xs)

-- Show as a consequence of foldr-++ above that
-- xs ++ ys ≡ foldr _∷_ ys xs
es : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
es xs ys = begin
    xs ++ ys
  ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
    foldr _∷_ [] (xs ++ ys)
  ≡⟨ foldr-++ _∷_ [] xs ys ⟩
    foldr _∷_ (foldr _∷_ [] ys) xs
  ≡⟨  cong (λ z → foldr _∷_ z xs) (foldr-∷ ys) ⟩
    foldr _∷_ ys xs
  ∎


-- Show that map can be defined using fold:
map-is-foldr : ∀ {A B : Set} (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} f = extensionality map-is-foldrbase
  where
    map-is-foldrbase : (xs : List A)
      → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    map-is-foldrbase [] = refl
    map-is-foldrbase (x ∷ xs) = cong (_∷_ (f x)) (map-is-foldrbase xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (branch l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

-- Demonstrate an analogue of map-is-foldr for the type of trees.
map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → map-Tree f g ≡ fold-Tree (λ lf → leaf (f lf)) (λ l x r → branch l (g x) r)
map-is-fold-Tree {A} {B} f g = extensionality map-is-fold-TreeBase
  where
    map-is-fold-TreeBase : (t : Tree A B)
      → map-Tree f g  t ≡ fold-Tree (λ lf → leaf (f lf)) (λ l x r → branch l (g x) r) t
    map-is-fold-TreeBase (leaf x) = refl
    map-is-fold-TreeBase (branch l x r)  rewrite
                                          map-is-fold-TreeBase l
                                        | map-is-fold-TreeBase r = refl

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
sum : List ℕ → ℕ
sum = foldr _+_ 0

-- Prove that the sum of the numbers (n - 1) + ⋯ + 0 is equal to n * (n ∸ 1) / 2:

lemma2 : ∀ (n : ℕ) → n + n * n ≡ n * suc n
lemma2 n rewrite *-comm n (suc n) = refl

lemma1 : ∀ (n : ℕ) → 2 * n  + n * (n ∸ 1) ≡ suc n * (suc n ∸ 1)
lemma1 zero = refl
lemma1 (suc n) rewrite
              *-distrib-+ 2 1 n
              | +-identityʳ n
              | lemma2 n
              | +-assoc  n (suc n) (n * suc n)
              = refl

es2 : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
es2 zero = refl
es2 (suc n) =
  begin
      (n + sum (downFrom n)) * 2
    ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
      n * 2 + sum (downFrom n) * 2
    ≡⟨ cong (n * 2 +_) (es2 n) ⟩
      n * 2 + n * (n ∸ 1)
    ≡⟨ cong (_+ n * (n ∸ 1)) (*-comm n 2) ⟩
      2 * n + n * (n ∸ 1)
    ≡⟨ lemma1 n ⟩
      suc n * (suc n ∸ 1)
    ∎



-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }


foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎


foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ foldl _⊗_ e xs ⊗ y
foldl-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldl _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldl _⊗_ e [] ⊗ y
  ∎
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldl _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldl-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldl _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldl _⊗_ e xs) y) ⟩
    (x ⊗ foldl _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs) ⊗ y
  ∎



data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)


All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P} xs ys = record
    { to   = to xs ys
    ; from = from xs ys
    }
    where
      ++-maintains-anyl : ∀ (xs ys : List A)
        → Any P xs → Any P (xs ++ ys)
      ++-maintains-anyl xs [] (here x) = here x
      ++-maintains-anyl xs [] (there p) rewrite ++-identityʳ xs = there p
      ++-maintains-anyl (x ∷ xs) ys (here p) = here p
      ++-maintains-anyl (x ∷ xs) ys (there p) with ++-maintains-anyl xs ys p
      ... | a = there a
      ++-maintains-anyr : ∀ (ys xs : List A)
        → Any P ys → Any P (xs ++ ys)
      ++-maintains-anyr ys [] (here y) = here y
      ++-maintains-anyr ys [] (there p) rewrite ++-identityʳ ys = there p
      ++-maintains-anyr ys (x ∷ xs) (here p) with ++-maintains-anyr ys xs (here p)
      ... | a = there a
      ++-maintains-anyr (y ∷ ys) (x ∷ xs) (there p) with ++-maintains-anyr ys xs p
      ... | a = there (++-maintains-anyr (y ∷ ys) xs (there p))

      to : (xs ys : List A) →  Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
      to [] (x ∷ ys) p = _⊎_.inj₂ p
      to (x ∷ xs) [] p rewrite ++-identityʳ xs = _⊎_.inj₁ p
      to (x ∷ xs) ys (here x₁) = _⊎_.inj₁ (here x₁)
      to (x ∷ xs) ys (there p) with to xs ys p
      ...                     | _⊎_.inj₁ x₁ = _⊎_.inj₁ (there x₁)
      ...                     | _⊎_.inj₂ x₁ = _⊎_.inj₂ x₁

      from : (xs ys : List A) →  (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
      from [] (x ∷ ys) (_⊎_.inj₂ p) = p
      from xs [] (_⊎_.inj₁ p) rewrite ++-identityʳ xs = p
      from xs (y ∷ ys) (_⊎_.inj₁ p) = ++-maintains-anyl xs (y ∷ ys) p
      from (x ∷ xs) ys (_⊎_.inj₂ p) = ++-maintains-anyr ys (x ∷ xs)  p

-- Show that the equivalence All-++-⇔ can be extended to an isomorphism.
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys = record
  { to      = _⇔_.to (All-++-⇔ xs ys)
  ; from    = _⇔_.from (All-++-⇔ xs ys)
  ; from∘to = from∘to xs ys
  ; to∘from = to∘from xs ys
  }
    where
      from∘to : (xs ys : List A) (x : All P (xs ++ ys))
          → _⇔_.from (All-++-⇔ xs ys) (_⇔_.to (All-++-⇔ xs ys) x) ≡ x
      from∘to [] ys p = refl
      from∘to (x ∷ xs) ys (p ∷ ps) = cong (λ qs → p ∷ qs) (from∘to xs ys ps)

      to∘from : (xs ys : List A) (x : All P xs × All P ys)
          → _⇔_.to (All-++-⇔ xs ys) (_⇔_.from (All-++-⇔ xs ys) x) ≡ x
      to∘from [] ys ⟨ [] , pys ⟩ = refl
      to∘from (x ∷ xs) ys ⟨ px ∷ pxs , pys ⟩ =
        cong (λ qs → ⟨ px ∷ (proj₁ qs) , proj₂ qs ⟩) (to∘from xs ys ⟨ pxs , pys ⟩)

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ {A} {P} xs = record
  { to      = to xs
  ; from    = from xs
  }
  where
    to : (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to [] nany = []
    to (x ∷ xs) nany = (λ x → nany (here x)) ∷ to xs (λ z → nany (there z))

    from : (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from [] nall = λ ()
    from (x ∷ xs) (nx ∷ nxs) = λ{ (here x) → nx x ; (there p) → from xs nxs p}


All-∀explicit :  ∀ {A : Set} {P : A → Set} (xs : List A)
  → All P xs ≃ ∀ (x) → x ∈ xs → P x
All-∀explicit {A} {P} xs = record
  { to      = to xs
  ; from    = from xs
  ; from∘to = from∘to xs
  ; to∘from = λ f →  extensionalityDep (to xs (from xs f)) f (λ r → extensionalityDep (to xs (from xs f) r) (f r) (lemma xs f r))
  }
  where
    to : (xs : List A) → All P xs → (∀ (x) → x ∈ xs → P x)
    to [] [] _ ()
    to (x ∷ xs) (x₁ ∷ x₂) _ (here x₃) rewrite x₃ = x₁
    to (x₁ ∷ xs) (x₂ ∷ x₃) x (there x₄) = to xs x₃ x x₄

    from : (xs : List A) → (∀ (x) → x ∈ xs → P x) → All P xs
    from [] p = []
    from (x ∷ xs) p = p x (here refl) ∷ from xs (λ x z → p x (there z))

    from∘to : (xs : List A) (p : All P xs) → from xs (to xs p) ≡ p
    from∘to [] [] = refl
    from∘to (x ∷ xs) (p ∷ ps) = cong (p ∷_) (from∘to xs ps)

    lemma : (xs : List A) (f : (x : A) → x ∈ xs → P x) (r : A) (z : Any (_≡_ r) xs) → to xs (from xs f) r z ≡ f r z
    lemma (x ∷ xs) f r (here h) rewrite h = refl
    lemma (x ∷ xs) f r (there t) = lemma xs (λ x t → f x (there t)) r t

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes px | _       = yes (here px)
...                 | _      | yes pxs = yes (there pxs)
...                 | no npx | no npxs = no λ { (here x) → npx x
                                              ; (there f) → npxs f }



data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)

-- Define the following variant of the traditional filter function on lists,
-- which given a decidable predicate and a list returns a list of elements that
-- satisfy the predicate and a list of elements that don’t, with their
-- corresponding proofs.
split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) with P? z | split P? zs
split P? (z ∷ zs) | yes p | ⟨ xs , ⟨ ys , ⟨ mrg , ⟨ pxs , pys ⟩ ⟩ ⟩ ⟩ = ⟨ z ∷ xs , ⟨ ys     , ⟨ left-∷ mrg  , ⟨ p ∷ pxs , pys      ⟩ ⟩ ⟩ ⟩
split P? (z ∷ zs) | no ¬p | ⟨ xs , ⟨ ys , ⟨ mrg , ⟨ pxs , pys ⟩ ⟩ ⟩ ⟩ = ⟨ xs     , ⟨ z ∷ ys , ⟨ right-∷ mrg , ⟨ pxs     , ¬p ∷ pys ⟩ ⟩ ⟩ ⟩

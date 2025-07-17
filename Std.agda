open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  → y ≡ x
sym refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  → P y → P x
subst P refl px = px

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl = refl


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data _∈_ {A : Set} : A → List A → Set where
  here  : {l : List A} {a : A}   → a ∈ (a ∷ l)
  there : {l : List A} {a b : A} → a ∈ l → a ∈ (b ∷ l)

{-# OPTIONS --rewriting #-}
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


{- Directions and polarity -}
data Dir : Set where
  +  : Dir
  -  : Dir

−_ : Dir → Dir
− + = -
− - = +

−− : (d : Dir) → − (− d) ≡ d
−− + = refl
−− - = refl
{-#REWRITE −− #-}

_×_ : Dir → Dir → Dir
+ × d' = d'
- × d' = − d'

×assoc : (d d' d'' : Dir) → d × (d' × d'') ≡ (d × d') × d''
×assoc + d' d'' = refl
×assoc - + d'' = refl
×assoc - - d'' = refl

×idem : (d : Dir) → d × d ≡ +
×idem + = refl
×idem - = refl

{-#REWRITE ×assoc ×idem #-}

×+ : (d : Dir) → d × + ≡ d
×+ + = refl
×+ - = refl
{-#REWRITE ×+ #-}

×- : (d : Dir) → d × - ≡ − d
×- + = refl
×- - = refl
{-#REWRITE ×- #-}

×-cancel₁ : (d d' : Dir) → (d × d') × d ≡ d'
×-cancel₁ + d' = refl
×-cancel₁ - + = refl
×-cancel₁ - - = refl

×-cancel₂ : (d d' : Dir) → (d' × d) × d ≡ d'
×-cancel₂ + d' = refl
×-cancel₂ - + = refl
×-cancel₂ - - = refl
{-#REWRITE ×-cancel₁ ×-cancel₂ #-}

-d-d : (d d' : Dir) → (− d) × (− d') ≡ d × d'
-d-d + d' = refl
-d-d - d' = refl
{-#REWRITE -d-d #-}

eqn : (d d' d'' : Dir) → ((d' × d'') × d) × d'' ≡ d' × d
eqn d d' + = refl
eqn d + - = refl
eqn d - - = refl
{-#REWRITE eqn #-}

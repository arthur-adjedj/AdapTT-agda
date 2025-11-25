{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir


{- Appendix C.1 : All sorts of AdapTT2 -}
postulate
  Ctx   :  Set
  Sub   : Ctx → Ctx → Set
  Trans   : (Γ Δ : Ctx) → Sub Γ Δ → Sub Γ Δ → Set
  Ty    : Ctx → Set
  Ad    : (Γ : Ctx) (A A' : Ty Γ) → Set
  Tm    : {Γ : Ctx} → Ty Γ → Set
  Tel   : Ctx → Set
  TelAd  : (Γ : Ctx) (Θ Θ' : Tel Γ) → Set
  Inst  : (Γ : Ctx) → Tel Γ → Set

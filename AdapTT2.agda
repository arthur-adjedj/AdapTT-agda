{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std   public
open import Dir   public
open import AppC1 public
open import AppC2 public
open import AppC3 public
open import AppC4 public
open import AppC5 public
open import AppC6 public

-- -- These rules are not necessary for this file. Are they necessary for the other files?
-- {-#REWRITE *ₘassoc *ₘid id*ₘ #-}
-- {-#REWRITE idwhiskerLeft whiskerLeftid *ₘwhiskerLeft whiskerLeft∘ idwhiskerRight whiskerRightid ∘whiskerRight whiskerRight*ₘ #-}
-- {-#REWRITE ∘ₐassoc ∘ₐid id∘ₐ #-}
-- {-#REWRITE ⟦∘ₐ⟧ ⟦whiskerRight⟧ ⟦whiskerLeft⟧ #-}
-- {-#REWRITE AdaptTrans TmTrans #-}
-- {-#REWRITE ⋄ₛ⁻ #-}
-- {-#REWRITE id^ₘ- *ₘ^ₘ- #-}
-- {-#REWRITE μ⁻ᵈ #-}
-- {-#REWRITE ▹ₘ₊^- #-}
-- {-#REWRITE ▹ₘ₋^- #-}

-- I think these are not useful anymore
-- -- Specialisation to correct for  μ⁻⁻ not firing
-- μ⁻⁻-spe : {d : Dir} {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d)} → (μ ^ₘ -) ^ₘ - ≡ μ
-- μ⁻⁻-spe {d} {Γ} {Δ} {σ} {τ} {μ} = μ⁻⁻ (σ ^ₛ d) (τ ^ₛ d) μ

-- -- Provable lemma needed for computation:
-- SubHdTy+ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel Δ) (A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))) (ι : Inst Γ (Θ [ σ ]₃)) →
--             (tyvz + {Δ} Θ) [ (σ ▸ₛ[ + ]⟦ Θ , A ⟧) ▹ₛᵢ[ + ]⟦ Θ [ WkTy + {Δ} Θ + ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ^ₛ + ]₃ , ι ⟧ ]₁
-- SubHdTy+ σ = SubHdTy {+} σ
-- {-#REWRITE SubHdTy+ #-}

-- σ⁻⁻-spe : {Γ Δ : Ctx} (σ : Sub Γ (Δ ^ -)) → (σ ^ₛ -) ^ₛ - ≡ σ
-- σ⁻⁻-spe = σ⁻⁻
-- {-#REWRITE σ⁻⁻-spe #-}

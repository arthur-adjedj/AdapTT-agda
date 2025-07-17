{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Dir
open import Std
open import AdapTT2
open import Pi
open import IndSig

postulate
  IndAdEqPaR :
    {Γₚ Δ : Ctx} (I : IndDesc Γₚ ⋄ₜ)
    (C : ConDesc Γₚ ⋄ₜ) (∈ᵢ : C ∈ I)
    {σ τ : Sub Δ Γₚ} (μ : Trans Δ Γₚ σ τ)
    (arg : Inst Δ (conData C [ σ ▸ₛ[ + ]⟦ ⋄ₜ , (ind I) [ σ ]₁ ⟧ ]₃) )
    -- Should typecheck, doesn't
    -- Agda fails to rewrite (id ▸ₛ[ + ]⟦ ⋄ₜ , ind I ⟧ ∘ σ) to (σ ▸ₛ[ + ]⟦ ⋄ₜ , (ind I) [ σ ]₁ ⟧)
     → adapt ((ind I) ⟦ μ ⟧) {! (constr I C ∈ᵢ) [ σ ▹ₛᵢ[ + ]⟦ conData C [ id ▸ₛ[ + ]⟦ ⋄ₜ , ind I ⟧ ]₃ , arg ⟧ ]₂ !} ≡ {!  (constr I C ∈ᵢ) [ τ ▹ₛᵢ[ + ]⟦ conData C [ id ▸ₛ[ + ]⟦ ⋄ₜ , ind I ⟧ ]₃ , teladapt (conData C [ id ▸ₛ[ + ]⟦ ⋄ₜ , ind I ⟧ ]₃ ⟦ μ ⟧₃) arg ⟧ ]₂ !}

  IndAdEq :
    {Γₚ Δ : Ctx} {Θᵢ : Tel Γₚ} (I : IndDesc Γₚ Θᵢ)
    (C : ConDesc Γₚ Θᵢ) (∈ᵢ : C ∈ I)
    {σ τ : Sub Δ Γₚ} (μ : Trans Δ Γₚ σ τ)
    (argn : Inst Δ ((ConDesc.Θargs C) [ σ ]₃))
    (argr : Inst Δ (recDatas (ConDesc.Θrec C) [ (σ ▸ₛ[ + ]⟦ Θᵢ , (ind I) [ σ ▹ₛ₃[ + ] Θᵢ ]₁ ⟧) ▹ₛᵢ[ + ]⟦ C .ConDesc.Θargs [ WkTy + Θᵢ + ]₃ , argn ⟧ ]₃) )
    → adapt
      ((ind I) ⟦ μ ▹ₜᵢ₊⟦ Θᵢ , (ConDesc.ιᵢ C) [ σ ▹ₛᵢ[ + ]⟦ ConDesc.Θargs C  , argn ⟧ ]₄ ⟧ ⟧)
      {! (constr I C ∈ᵢ) [ σ ▹ₛᵢ[ + ]⟦ conData C [ id ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧ ]₃ , argn ++ᵢ argr ⟧ ]₂ !} ≡ {! (constr I C ∈ᵢ) [ τ ▹ₛᵢ[ + ]⟦ conData C [ id ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧ ]₃ , teladapt (conData C [ id ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧ ]₃ ⟦ μ ⟧₃) (argn ++ᵢ argr) ⟧ ]₂  !}

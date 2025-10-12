{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir
open import AppC1
open import AppC2

{- Appendix C.3 : Empty context and context dualisation -}

-- To express the rules for Appendix C.3, we first need a helper function
Trans-swap : Dir → (Γ Δ : Ctx) →  Sub Γ Δ → Sub Γ Δ → Set
Trans-swap + Γ Δ σ τ = Trans Γ Δ σ τ
Trans-swap - Γ Δ σ τ = Trans Γ Δ τ σ

-- This function satisfies an obvious lemma, that is needed as a rewrite for the rules to type-check
Trans-swap- : (d : Dir) → (Γ Δ : Ctx) → (σ τ : Sub Γ Δ) → Trans-swap (− d) Γ Δ σ τ ≡ Trans-swap d Γ Δ τ σ
Trans-swap- + Γ Δ σ τ = refl
Trans-swap- - Γ Δ σ τ = refl
{-#REWRITE Trans-swap- #-}

postulate
-- CtxEmp
  ⋄   : Ctx

-- SubEmp
  ⋄ₛ  : {Γ : Ctx} → Sub Γ ⋄

-- SubEmpExt
  ⋄terminal : {Γ : Ctx} (σ : Sub Γ ⋄) → σ ≡ ⋄ₛ

-- CtxDual
  _^_  : Ctx → Dir →  Ctx

-- SubDual
  _^ₛ_ : {Γ Δ : Ctx} → Sub Γ Δ → (d : Dir) → Sub (Γ ^ d) (Δ ^ d)

-- TransDual
  _^ₘ_ : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} → Trans Γ Δ σ τ → (d : Dir) → Trans-swap d (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d)

-- CtxEmpDual
  ⋄⁻ : ⋄ ^ - ≡ ⋄
  {-#REWRITE ⋄⁻ #-}

-- SubIdDual
  id^- : (Γ : Ctx) → id Γ ^ₛ - ≡ id (Γ ^ -)

-- SubCompDual
  ∘^- : {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Ξ Γ} → (σ ∘ τ) ^ₛ - ≡ (σ ^ₛ -) ∘ (τ ^ₛ -)
  {-#REWRITE ∘^- #-}

-- TransWhiskerLeftDual
  whiskerLeft^-  : {Γ Δ Ξ : Ctx} {σ σ' : Sub Γ Δ} (τ : Sub Δ Ξ) (μ : Trans Γ Δ σ σ') →
    (whiskerLeft τ μ) ^ₘ - ≡ whiskerLeft (τ ^ₛ -) (μ ^ₘ -)

-- TransWhiskerRightDual
  whiskerRight^- : {Γ Δ Ξ : Ctx} {τ τ' : Sub Δ Ξ} (ν : Trans Δ Ξ τ τ') (σ : Sub Γ Δ) →
    (whiskerRight ν σ) ^ₘ - ≡ whiskerRight (ν ^ₘ -) (σ ^ₛ -)

-- TransIdDual
  id^ₘ- : {Γ Δ : Ctx} {σ : Sub Γ Δ} → idₘ {σ = σ} ^ₘ - ≡ idₘ

-- TransCompDual
  *ₘ^ₘ- : {Γ Δ : Ctx} {σ τ ξ : Sub Γ Δ} {μ : Trans Γ Δ σ τ} {ν : Trans Γ Δ τ ξ} → (ν *ₘ μ) ^ₘ - ≡ (μ ^ₘ -) *ₘ (ν ^ₘ -)

-- CtxPlus
  Γ⁺ : {Γ : Ctx} → Γ ^ + ≡ Γ
  {-#REWRITE Γ⁺ #-}

-- SubPlus
  σ⁺ : {Γ Δ : Ctx} {σ : Sub Γ Δ} → σ ^ₛ + ≡ σ
  {-#REWRITE σ⁺ #-}

-- TransPlus
  μ⁺ : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {μ : Trans Γ Δ σ τ} → μ ^ₘ + ≡ μ
  {-#REWRITE μ⁺ #-}

-- CtxDoubleDual
  Γ⁻⁻ : {Γ : Ctx} → (Γ ^ -) ^ - ≡ Γ
  {-#REWRITE Γ⁻⁻ #-}

-- SubDoubleDual
  σ⁻⁻ : {Γ Δ : Ctx} (σ : Sub Γ Δ) → (σ ^ₛ -) ^ₛ - ≡ σ
  {-#REWRITE σ⁻⁻ #-}

-- TransDoubleDual
  μ⁻⁻ : {Γ Δ : Ctx} (σ τ : Sub Γ Δ) (μ : Trans Γ Δ σ τ) → (μ ^ₘ -) ^ₘ - ≡ μ
  {-#REWRITE μ⁻⁻ #-}

{- Provable lemmas: We need to rewrite these these results, which are consequences of the axioms -}

⋄ₛ⁻ : {Γ : Ctx} → (⋄ₛ {Γ = Γ}) ^ₛ - ≡ ⋄ₛ
⋄ₛ⁻ { Γ } = ⋄terminal ((⋄ₛ {Γ = Γ}) ^ₛ -)

Γᵈᵈ : (d d' : Dir) (Γ : Ctx) → (Γ ^ d) ^ d' ≡ Γ ^ (d × d')
Γᵈᵈ + d' Γ = refl
Γᵈᵈ - + Γ = refl
Γᵈᵈ - - Γ = refl
{-#REWRITE Γᵈᵈ #-}

σᵈᵈ : (d d' : Dir) {Γ Δ : Ctx} (σ : Sub Γ Δ) → (σ ^ₛ d) ^ₛ d' ≡ σ ^ₛ (d × d')
σᵈᵈ + d' σ = refl
σᵈᵈ - + σ = refl
σᵈᵈ - - σ = refl
{-#REWRITE σᵈᵈ #-}

μ⁻ᵈ : {d : Dir} {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {μ : Trans Γ Δ σ τ} → ((μ ^ₘ -) ^ₘ d) ≡ (μ ^ₘ (- × d))
μ⁻ᵈ {+} {Γ} {Δ} {σ} {τ} {μ} = refl
μ⁻ᵈ { - } {Γ} {Δ} {σ} {τ} {μ} = refl

id^d : {Γ : Ctx} → id Γ ^ₛ d ≡ id (Γ ^ d)
id^d {+} {Γ} = refl
id^d { - } {Γ}= id^- Γ

∘^d : (d : Dir) {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Ξ Γ} → (σ ∘ τ) ^ₛ d ≡ (σ ^ₛ d) ∘ (τ ^ₛ d)
∘^d + = refl
∘^d - {σ = σ} {τ = τ} = ∘^- {σ = σ} {τ = τ}

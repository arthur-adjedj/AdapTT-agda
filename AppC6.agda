{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir
open import AppC1
open import AppC2
open import AppC3
open import AppC4
open import AppC5

{- Appendix C.6 : Type variables -}
postulate
-- CtxTy
  _▸[_]⟦_,_⟧ :  (Γ : Ctx) (d : Dir) → Tel (Γ ^ d) → Dir → Ctx

-- SubTy
  _▸ₛ[_]⟦_,_⟧ : {d' : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) → Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d') → Sub Γ (Δ ▸[ d ]⟦ Θ , d' ⟧)


-- TransAd+
  _▸ₘ₊⟦_⟧_ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ + ] (Θ [ σ ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ + ] (Θ [ τ ]₃)) ^ d)}
          → Ad _ A (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ^ₛ d ]₁)
          → Trans Γ (Δ ▸[ + ]⟦ Θ , d ⟧) (σ ▸ₛ[ + ]⟦ Θ , A ⟧) ((τ ▸ₛ[ + ]⟦ Θ , B ⟧))


-- TransAd-
  _▸ₘ₋⟦_⟧_ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel (Δ ^ -)}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃)) ^ d)}
          → Ad _ A (B [ (id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧) ^ₛ d ]₁)
          → Trans Γ (Δ ▸[ - ]⟦ Θ , d ⟧) ((σ ▸ₛ[ - ]⟦ Θ , B ⟧)) (τ ▸ₛ[ - ]⟦ Θ , A ⟧)

-- WkTy
  WkTy  : (d : Dir) {Γ : Ctx}  (Θ : Tel (Γ ^ d)) (d' : Dir) → Sub (Γ ▸[ d ]⟦ Θ , d' ⟧) Γ

-- VarZTy
  tyvz  : (d : Dir) {Γ : Ctx} (Θ : Tel (Γ ^ d)) → Ty ((Γ ▸[ d ]⟦ Θ , + ⟧) ▹₃[ d ]  ( Θ [ (WkTy d {Γ} Θ +) ^ₛ d ]₃))

-- CtxTyDual
  ▸⟦⟧^- : {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (Γ ▸[ d ]⟦ Θ , d' ⟧) ^ - ≡ (Γ ^ -) ▸[ − d ]⟦ Θ , − d' ⟧
  {-#REWRITE ▸⟦⟧^- #-}

-- WkTyDual
  WkTy^- : {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (WkTy d {Γ} Θ d') ^ₛ - ≡ WkTy (− d) {Γ ^ - } Θ (− d')
  {-#REWRITE WkTy^- #-}

-- SubTyDual
  ▸ₛ^- : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) →
    (_▸ₛ[_]⟦_,_⟧ {d'} σ d Θ A) ^ₛ - ≡ ((σ ^ₛ -) ▸ₛ[ − d ]⟦ Θ , A ⟧)
  {-#REWRITE ▸ₛ^- #-}

d×-d : (d d' : Dir) → d × (− d') ≡ (− d) × d'
d×-d = {!!}
{-#REWRITE d×-d #-}

WkTel^-d : {d d' : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} →
  (WkTel {Γ} d Θ) ^ₛ (− d') ≡ ((WkTel {Γ ^ - } (− d) Θ) ^ₛ d')
WkTel^-d = {!!}
{-#REWRITE WkTel^-d #-}

postulate
-- -- TransAd+Dual
--   {-#REWRITE μ⁻⁻-spe #-}
  ▸ₘ₊^- : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ + ] (Θ [ σ ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ + ] (Θ [ τ ]₃)) ^ d)}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ^ₛ d ]₁)) →
          (_▸ₘ₊⟦_⟧_ {Γ} {Δ} {σ} {τ} μ {Θ} d {A} {B} a) ^ₘ - ≡ _▸ₘ₋⟦_⟧_ {Γ ^ - } {Δ ^ - } {τ ^ₛ - } {σ ^ₛ - } (μ ^ₘ -) {Θ} (− d) {A} {B} a

-- TransAd-Dual
  ▸ₘ₋^- : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel (Δ ^ -)}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃)) ^ d)}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧) ^ₛ d ]₁))
          → (_▸ₘ₋⟦_⟧_ {Γ} {Δ} {σ} {τ} μ {Θ} d {A} {B} a) ^ₘ - ≡ _▸ₘ₊⟦_⟧_ {Γ ^ - } {Δ ^ - } {τ ^ₛ - } {σ ^ₛ - } (μ ^ₘ -) {Θ} (− d) {A} {B} a

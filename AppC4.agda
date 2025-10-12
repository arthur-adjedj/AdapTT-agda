{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir
open import AppC1
open import AppC2
open import AppC3

{- Appendix C.4 : Term variables in AdapTT2 -}
postulate
--CtxExtTm
  _▹[_]_      : (Γ : Ctx) (d : Dir) → Ty (Γ ^ d) → Ctx

-- SubExtTm
  _▹ₛ[_,_]_     : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (A : Ty (Δ ^ d)) → Tm (A [ σ ^ₛ d ]₁) → Sub Γ (Δ ▹[ d ] A)

-- WkTm
  WkTm        : (Γ : Ctx) (d : Dir) (A : Ty (Γ ^ d)) →  Sub (Γ ▹[ d ] A) Γ

-- VarZTm
  vztm        : {Γ : Ctx} {A : Ty Γ} → Tm {Γ = Γ ▹[ + ] A} (A [ WkTm Γ + A ]₁)

-- SubTL
  SubTl        : {Γ Δ : Ctx} {σ : Sub Γ Δ} {A : Ty (Δ ^ d)} (t : Tm(A [ σ ^ₛ d ]₁)) → (WkTm Δ d A) ∘ (σ ▹ₛ[ d , A ] t) ≡ σ

-- SubEta
  SubEta        : {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ (Δ ▹[ + ] A)) → ((WkTm Δ + A) ∘ σ) ▹ₛ[ + , A ] (vztm [ σ ]₂) ≡ σ

-- AdTmVarZ
  adapt-vztm   : {Γ Δ : Ctx} {A : Ty Δ} {σ τ : Sub Γ (Δ ▹[ + ] A)} (μ : Trans Γ (Δ ▹[ + ] A) σ τ) →  adapt (A ⟦ whiskerLeft (WkTm Δ + A) μ ⟧) (vztm [ σ ]₂) ≡ vztm [ τ ]₂

  {-#REWRITE SubTl #-}
-- SubTmExtVarZ
  SubHd : {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ) (t : Tm (A [ σ ]₁)) → vztm {A = A} [ σ ▹ₛ[ + , A ] t ]₂ ≡ t

-- TransTm+
  _▹ₘ₊_       : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Ty Δ} (μ : Trans Γ Δ σ τ) (t : Tm (A [ σ ]₁))
        → Trans Γ (Δ ▹[ + ] A) (σ ▹ₛ[ + , A ] t ) (τ ▹ₛ[ + , A ] (adapt (A ⟦ μ ⟧) t))

-- TransTm-
  _▹ₘ₋_       : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Ty (Δ ^ -)} (μ : Trans Γ Δ σ τ) (t : Tm (A [ τ ^ₛ - ]₁))
         → Trans Γ (Δ ▹[ - ] A) (σ ▹ₛ[ - , A ] adapt (A ⟦ μ ^ₘ - ⟧) t) (τ ▹ₛ[ - , A ] t)

  {-#REWRITE SubEta #-}
-- TransTl+
  TransTl₊     : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) {A : Ty Δ} (t : Tm (A [ σ ]₁)) → whiskerLeft (WkTm Δ + A) (μ ▹ₘ₊ t) ≡ μ

-- TransTl-
  TransTl₋     : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) {A : Ty (Δ ^ -)} (t : Tm (A [ τ ^ₛ - ]₁)) →  whiskerLeft (WkTm Δ - A) (μ ▹ₘ₋ t) ≡ μ

  {-#REWRITE adapt-vztm #-}
-- TransEta
  TransEta     : {Γ Δ : Ctx} {A : Ty Δ} {σ τ : Sub Γ (Δ ▹[ + ] A)} (μ : Trans Γ (Δ ▹[ + ] A) σ τ) → (whiskerLeft (WkTm Δ + A) μ) ▹ₘ₊ (vztm [ σ ]₂) ≡ μ

-- CtxExtTmDual
  ▹^- : {Γ : Ctx} (A : Ty (Γ ^ d)) → (Γ ▹[ d ] A) ^ - ≡ (Γ ^ -) ▹[ − d ] A
  {-#REWRITE ▹^- #-}

-- WkTmDual
  WkTm^- : {Γ : Ctx} {d : Dir} (A : Ty (Γ ^ d)) →  (WkTm Γ d A) ^ₛ - ≡ WkTm (Γ ^ -) (− d) A
  {-#REWRITE WkTm^- #-}

-- SubExtTmDual
  ▹ₛ^- : {Γ Δ : Ctx} {σ : Sub Γ Δ} (A : Ty (Δ ^ d)) (t : Tm (A [ σ ^ₛ d ]₁)) → (σ ▹ₛ[ d , A ] t) ^ₛ - ≡ (σ ^ₛ -) ▹ₛ[ − d , A ] t
  {-#REWRITE ▹ₛ^- #-}

-- TransTm+Dual
  ▹ₘ₊^- : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Ty Δ} (μ : Trans Γ Δ σ τ) (t : Tm (A [ σ ]₁)) → (_▹ₘ₊_ {A = A} μ t) ^ₘ - ≡ (μ ^ₘ -) ▹ₘ₋ t

-- TransTm-Dual
  ▹ₘ₋^- : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Ty (Δ ^ -)} (μ : Trans Γ Δ σ τ) (t : Tm (A [ τ ^ₛ - ]₁)) → (_▹ₘ₋_ {A = A} μ t) ^ₘ - ≡ (μ ^ₘ -) ▹ₘ₊ t

-- TyTransSub
  ⟦⟧[]₁ : (Γ Δ Ξ : Ctx) (τ ξ : Sub Γ Δ) (μ : Trans Γ Δ τ ξ) (σ : Sub Ξ Γ)
         (A : Ty Δ) → A ⟦ μ ⟧ [ σ ]ₐ ≡ A ⟦ whiskerRight μ σ ⟧

-- TySubTrans
  []⟦⟧₁ : (Γ Δ Ξ : Ctx) (σ : Sub Γ Δ) (τ ξ : Sub Ξ Γ) (μ : Trans Ξ Γ τ ξ)
         (A : Ty Δ) → A [ σ ]₁ ⟦ μ ⟧ ≡ A ⟦ whiskerLeft σ μ ⟧

-- provable lemmas to help agda with computations:
⋄ₛ∘ : {Γ Δ : Ctx} {σ : Sub Γ Δ} → ⋄ₛ ∘ σ ≡ ⋄ₛ
⋄ₛ∘ {σ = σ} = ⋄terminal (⋄ₛ ∘ σ)

SubTlComp : {Γ Δ Ξ : Ctx} {A : Ty Δ} {τ : Sub Ξ Γ } {σ : Sub Γ Δ} {t : Tm (A [ σ ]₁) } → WkTm Δ + A ∘ (σ ▹ₛ[ + , A ] t) ∘ τ ≡ σ ∘ τ
SubTlComp {Γ} {Δ} {Ξ} {A} {τ} {σ} {t} = sym (∘assoc (WkTm Δ + A) (σ ▹ₛ[ + , A ] t) τ)
{-#REWRITE SubTlComp #-}

{-#REWRITE SubHd #-}
SubHdComp : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Ξ Γ) (A : Ty Δ) (t : Tm (A [ σ ]₁)) → vztm [ (σ ▹ₛ[ + , A ] t) ∘ τ ]₂ ≡ (t [ τ ]₂)
SubHdComp σ τ A t = sym ([∘]₂ {σ = σ ▹ₛ[ + , A ] t} {δ = τ} {x = vztm})
{-#REWRITE SubHdComp #-}

SubEta- : {Γ Δ : Ctx} {A : Ty (Δ ^ -)} (σ : Sub Γ (Δ ▹[ - ] A)) → (((WkTm (Δ ^ -) + A) ∘ (σ ^ₛ -)) ▹ₛ[ + , A ] (vztm [ σ ^ₛ - ]₂)) ^ₛ - ≡ σ
SubEta- σ = σ⁻⁻ σ
{-#REWRITE SubEta- #-}

{-#REWRITE id^d ∘^d #-}
∘▹ₛ : {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Ξ Γ} {A : Ty (Δ ^ d)} {t : Tm (A [ σ ^ₛ d ]₁)} → (σ ▹ₛ[ d , A ] t) ∘ τ ≡ ((σ ∘ τ) ▹ₛ[ d , A ] (t [ τ ^ₛ d ]₂))
∘▹ₛ {+} {Γ} {Δ} {Ξ} {σ} {τ} {A} {t} = sym (SubEta ((σ ▹ₛ[ + , A ] t) ∘ τ))
∘▹ₛ { - } {Γ} {Δ} {Ξ} {σ} {τ} {A} {t} = sym (SubEta- ((σ ▹ₛ[ - , A ] t) ∘ τ))
{-#REWRITE  ∘▹ₛ #-}

{-#REWRITE TransTl₊ TransTl₋ TransEta #-}
TransEta- : {Γ Δ : Ctx} {A : Ty (Δ ^ -)} {σ τ : Sub Γ (Δ ▹[ - ] A)} (μ : Trans Γ (Δ ▹[ - ] A) σ τ) → (_▹ₘ₊_ {A = A} (whiskerLeft (WkTm (Δ ^ -) + A) (μ ^ₘ -) ) (vztm {Γ = Δ ^ - } {A = A} [ τ ^ₛ - ]₂)) ^ₘ - ≡ μ
TransEta- μ = μ⁻ᵈ {d = - } {μ = μ}
{-#REWRITE TransEta- #-}

▹^d : (d' : Dir) {Γ : Ctx} (A : Ty (Γ ^ d)) → (Γ ▹[ d ] A) ^ d' ≡ (Γ ^ d') ▹[ d × d' ] A
▹^d + A = refl
▹^d - A = refl
{-#REWRITE ▹^d #-}

▹ₛ^d : (d' : Dir) {Γ Δ : Ctx} {σ : Sub Γ Δ} (A : Ty (Δ ^ d)) (t : Tm (A [ σ ^ₛ d ]₁)) → (σ ▹ₛ[ d , A ] t) ^ₛ d' ≡ (σ ^ₛ d') ▹ₛ[ d × d' , A ] t
▹ₛ^d + A t = refl
▹ₛ^d - A t = refl
{-#REWRITE ▹ₛ^d #-}

{-#REWRITE [∘]₂ [id]₂ #-}
WkTm▹ₛvztm  : {Γ : Ctx} {A : Ty Γ} →  WkTm Γ + A ▹ₛ[ + , A ] vztm ≡ id (Γ ▹[ + ] A)
WkTm▹ₛvztm {Γ} {A} = SubEta (id (Γ ▹[ + ] A))
WkTm▹ₛvztm₋ : {Γ : Ctx} {A : Ty (Γ ^ -)} →  WkTm Γ - A ▹ₛ[ - , A ] vztm ≡ id (Γ ▹[ - ] A)
WkTm▹ₛvztm₋ {Γ} {A} = SubEta- (id (Γ ▹[ - ] A))
{-#REWRITE WkTm▹ₛvztm WkTm▹ₛvztm₋ #-}

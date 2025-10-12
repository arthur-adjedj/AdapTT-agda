{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir
open import AppC1

infixr 7 _∘_
variable
  d d' : Dir

{- Appendix C.2 : Basic structure of AdapTT2 -}
postulate
-- SubstId
  id           : (Γ : Ctx) → Sub Γ Γ

-- SubstComp
  _∘_          : {Γ Δ Ξ : Ctx} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ

-- SubstRightUnitality
  ∘id : {Γ Δ : Ctx} {σ : Sub Γ Δ} → σ ∘ id Γ ≡ σ

-- SubstLeftUnitality
  id∘ : {Γ Δ : Ctx} {σ : Sub Γ Δ} → id Δ ∘ σ ≡ σ

-- SubstAssoc
  ∘assoc : {Γ Δ Ξ Φ : Ctx} (σ : Sub Φ Δ) (δ : Sub Γ Φ) (τ : Sub Ξ Γ) →  (σ ∘ δ) ∘ τ ≡ σ ∘ δ ∘ τ

-- AdId
  idₐ          : {Γ : Ctx} {A : Ty Γ} → Ad Γ A A

-- AdComp
  _∘ₐ_         : {Γ : Ctx} {A B C : Ty Γ} → Ad Γ B C → Ad Γ A B →  Ad Γ A C

-- TransId
  idₘ          : {Γ Δ : Ctx} {σ : Sub Γ Δ} → Trans Γ Δ σ σ

-- TransComp
  _*ₘ_         : {Γ Δ : Ctx} {σ ρ τ : Sub Γ Δ} → Trans Γ Δ σ τ → Trans Γ Δ ρ σ →  Trans Γ Δ ρ τ

-- TransWhiskerLeft
  whiskerLeft  : {Γ Δ Ξ : Ctx} {σ σ' : Sub Γ Δ} (τ : Sub Δ Ξ) (μ : Trans Γ Δ σ σ') → Trans Γ Ξ (τ ∘ σ) (τ ∘ σ')

-- TransWhiskerRight
  whiskerRight : {Γ Δ Ξ : Ctx} {τ τ' : Sub Δ Ξ} (ν : Trans Δ Ξ τ τ') (σ : Sub Γ Δ) → Trans Γ Ξ (τ ∘ σ) (τ' ∘ σ)

-- TransLeftUnitality
  *ₘid : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) → μ *ₘ idₘ ≡ μ

-- TransRightUnitality
  id*ₘ : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) → idₘ *ₘ μ ≡ μ

 -- TransAssoc
  *ₘassoc : {Γ Δ : Ctx} {σ τ ρ ψ : Sub Γ Δ} (ξ : Trans Γ Δ ρ ψ ) (ν : Trans Γ Δ τ ρ) (μ : Trans Γ Δ σ τ) → ξ *ₘ (ν *ₘ μ) ≡ (ξ *ₘ ν) *ₘ μ

  {-#REWRITE ∘assoc ∘id id∘ #-}
-- TransWhiskerLeftRightUnitality
  idwhiskerLeft : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Ξ) → whiskerLeft τ (idₘ {σ = σ}) ≡ idₘ

-- TransWhiskerRightLeftUnitality
  idwhiskerRight : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Ξ) → whiskerRight (idₘ {σ = τ}) σ ≡ idₘ

-- TransWhiskerLeftLeftUnitality
  whiskerLeftid : {Γ Δ : Ctx} (σ σ' : Sub Γ Δ) (μ : Trans Γ Δ σ σ') → whiskerLeft (id Δ) μ ≡ μ

-- TransWhiskerRightRightUnitality
  whiskerRightid : {Γ Δ : Ctx} (σ σ' : Sub Γ Δ) (μ : Trans Γ Δ σ σ') → whiskerRight μ (id Γ) ≡ μ

 -- TransWhiskerLeftAssoc
  whiskerLeft∘ : {Γ Δ Ξ Φ : Ctx} (σ σ' : Sub Γ Δ) (μ : Trans Γ Δ σ σ') (τ : Sub Δ Ξ) (τ' : Sub Ξ Φ) → whiskerLeft (τ' ∘ τ) μ  ≡ whiskerLeft τ' (whiskerLeft τ μ)

 -- TransWhiskerRightAssoc
  ∘whiskerRight : {Γ Δ Ξ Φ : Ctx} (σ : Sub Γ Δ) (σ' : Sub Δ Ξ) (τ τ' : Sub Ξ Φ) (μ : Trans Ξ Φ τ τ') → whiskerRight μ (σ' ∘ σ) ≡ whiskerRight (whiskerRight μ  σ')  σ

 -- TransWhiskerLeftDistr
  *ₘwhiskerLeft : {Γ Δ Ξ : Ctx} (τ τ' τ'' : Sub Γ Δ) (ν : Trans Γ Δ τ τ') (μ  : Trans Γ Δ τ' τ'') (σ : Sub Δ Ξ) → whiskerLeft σ (μ *ₘ ν) ≡ (whiskerLeft σ μ) *ₘ (whiskerLeft σ ν)

 -- TransWhiskerRightDistr
  whiskerRight*ₘ : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ τ' τ'' : Sub Δ Ξ) (μ : Trans Δ Ξ τ τ') (ν : Trans Δ Ξ τ' τ'') → whiskerRight (ν *ₘ μ) σ ≡ (whiskerRight ν σ) *ₘ (whiskerRight μ σ)

-- AdRightUnitality
  ∘ₐid : {Γ : Ctx} {A B : Ty Γ} (a : Ad _ A B) → a ∘ₐ idₐ ≡ a

 -- AdLeftUnitality
  id∘ₐ : {Γ : Ctx} {A B : Ty Γ} (a : Ad _ A B) → idₐ ∘ₐ a ≡ a

-- AdAssoc
  ∘ₐassoc : {Γ : Ctx} {A B C D : Ty Γ} (a : Ad _ A B) (b : Ad _ B C) (c : Ad _ C D) → c ∘ₐ (b ∘ₐ a) ≡ (c ∘ₐ b) ∘ₐ a

 -- AdTm
  adapt        : {Γ : Ctx} {A B : Ty Γ} → Ad Γ A B → Tm A → Tm B

 -- SubTy
  _[_]₁        : {Γ Δ : Ctx} → Ty Δ → Sub Γ Δ → Ty Γ

-- SubTyId
  [id]₁ : {Δ : Ctx} {A : Ty Δ} → A [ id Δ ]₁ ≡ A

-- SubTyComp
  [∘]₁   : {Γ Δ Φ : Ctx} {σ : Sub Φ Δ} {δ : Sub Γ Φ} {A : Ty  Δ} → A [ σ ]₁ [ δ ]₁ ≡ A [ σ ∘ δ ]₁

-- SubAd
  _[_]ₐ        : {Γ Δ : Ctx} {A B : Ty Δ} → Ad Δ A B → (σ : Sub Γ Δ) → Ad Γ (A [ σ ]₁) (B [ σ ]₁)

  {-#REWRITE [∘]₁ [id]₁ #-}
-- SubAdId
  [id]ₐ : {Γ : Ctx} {A B : Ty Γ} (a : Ad _ A B) → a [ id Γ ]ₐ ≡ a

-- SubAdComp
  [∘]ₐ : {Γ Δ Ξ : Ctx} {A B : Ty Δ} (a : Ad _ A B) (τ : Sub Ξ Γ) (σ : Sub Γ Δ) → a [ σ ]ₐ [ τ ]ₐ ≡ a [ σ ∘ τ ]ₐ

-- SubAdOnId
  id[]ₐ : {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ Δ) → idₐ {A = A} [ σ ]ₐ ≡ idₐ

-- SubAdOnComp
  ∘[]ₐ : {Γ Δ : Ctx} {A B C : Ty Δ} (a : Ad _ B C) (b : Ad _ A B) (σ : Sub Γ Δ) → (a ∘ₐ b) [ σ ]ₐ ≡ (a [ σ ]ₐ) ∘ₐ (b [ σ ]ₐ)

 -- SubTm
  _[_]₂        : {Γ Δ : Ctx} {A : Ty Δ} → Tm A → (σ : Sub Γ Δ) → Tm (A [ σ ]₁)

-- SubTmId
  [id]₂ : {Δ : Ctx} {A : Ty Δ} {t : Tm A} → t [ id Δ ]₂ ≡ t

-- SubTmComp
  [∘]₂ : {Γ Δ Φ : Ctx} {σ : Sub Φ Δ} {δ : Sub Γ Φ} {A : Ty Δ}  {x : Tm A    } → x [ σ ]₂ [ δ ]₂ ≡ x [ σ ∘ δ ]₂

-- AdTmId
  adaptid : {Γ : Ctx} {A : Ty Γ} {t : Tm A} → adapt idₐ t ≡ t

-- AdTmComp
  adapt∘ : {Γ : Ctx} {A B C : Ty Γ} {μ : Ad _ B C} {ν : Ad _ A B} {t : Tm A} → adapt (μ ∘ₐ ν) t ≡ adapt μ (adapt ν t)

-- SubTmOnAd
  adapt[]₂ : {Γ Δ : Ctx} {A B : Ty Δ} (a : Ad _ A B) (t : Tm A) (σ : Sub Γ Δ) → (adapt a t) [ σ ]₂ ≡ adapt (a [ σ ]ₐ) (t [ σ ]₂)

-- TransTy
  _⟦_⟧         : {Γ Δ : Ctx} (A : Ty Δ) {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) → Ad Γ (A [ σ ]₁) (A [ τ ]₁)

-- TransTyId
  ⟦id⟧ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {A : Ty Δ} → A ⟦ idₘ {σ = σ} ⟧ ≡ idₐ

-- TransTyComp
  ⟦∘ₐ⟧ : {Γ Δ : Ctx} (A : Ty Δ) {σ τ ξ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) (ν : Trans Γ Δ τ ξ) -> A ⟦ ν *ₘ μ ⟧ ≡ ((A ⟦ ν ⟧) ∘ₐ (A ⟦ μ ⟧))

-- SubTyOnTransTy
  ⟦whiskerRight⟧ : {Γ Δ Ξ : Ctx} (A : Ty Ξ) {σ τ : Sub Δ Ξ} (μ : Trans Δ Ξ σ τ) (δ : Sub Γ Δ) → (A ⟦ μ ⟧)[ δ ]ₐ ≡ (A ⟦ whiskerRight μ δ ⟧)

-- TransTyOnSubTy
  ⟦whiskerLeft⟧ : {Γ Δ Ξ : Ctx} (A : Ty Ξ) (ξ : Sub Δ Ξ)  {σ τ : Sub Γ Δ} (ν : Trans Γ Δ σ τ) → (A [ ξ ]₁)⟦ ν ⟧ ≡ (A ⟦ whiskerLeft ξ ν ⟧)

-- TransTyNatural
  AdaptTrans   : {Γ Δ : Ctx} {A B : Ty Δ} (f : Ad Δ A B)
                 {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) →
                 (B ⟦ μ ⟧) ∘ₐ (f [ σ ]ₐ) ≡ (f [ τ ]ₐ) ∘ₐ (A ⟦ μ ⟧)

-- TransTyAdTm
  TmTrans      : {Γ Δ : Ctx} {A : Ty Δ} (t : Tm A)
                 {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) →
                 (adapt (A ⟦ μ ⟧) (t [ σ ]₂)) ≡ (t [ τ ]₂)

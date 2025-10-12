{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir

infixr 7 _∘_
variable
  d d' : Dir

{- Appendix C.1 : All sorts of AdapTT2 -}
postulate
  Ctx   :  Set
  Sub   : Ctx → Ctx → Set
  Trans   : (Γ Δ : Ctx) → Sub Γ Δ → Sub Γ Δ → Set
  Ty    : Ctx → Set
  Ad    : (Γ : Ctx) (A A' : Ty Γ) → Set
  Tm    : {Γ : Ctx} → Ty Γ → Set

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

{- Provable lemmas: At this stage we can prove a few helper lemmas about polarities that will help Agda fire the rewrite rules -}

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

-- Specialisation to correct for  μ⁻⁻ not firing
μ⁻⁻-spe : {d : Dir} {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d)} → (μ ^ₘ -) ^ₘ - ≡ μ
μ⁻⁻-spe {d} {Γ} {Δ} {σ} {τ} {μ} = μ⁻⁻ (σ ^ₛ d) (τ ^ₛ d) μ

id^d : {Γ : Ctx} → id Γ ^ₛ d ≡ id (Γ ^ d)
id^d {+} {Γ} = refl
id^d { - } {Γ}= id^- Γ

∘^d : (d : Dir) {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Ξ Γ} → (σ ∘ τ) ^ₛ d ≡ (σ ^ₛ d) ∘ (τ ^ₛ d)
∘^d + = refl
∘^d - {σ = σ} {τ = τ} = ∘^- {σ = σ} {τ = τ}


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

lemma₁ : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ)(τ : Sub Δ Ξ) (A : Ty Δ) (B : Ty Ξ) (a : Ad _ A (B [ τ ]₁)) (t : Tm (A [ σ ]₁)) → (a [ WkTm Δ + A ]ₐ) [ σ ▹ₛ[ + , A ] t ]ₐ ≡ (a [ σ ]ₐ)
lemma₁ {Γ} {Δ} {Ξ} σ τ A B a t = [∘]ₐ a (σ ▹ₛ[ + , A ] t) (WkTm Δ + A)
{-#REWRITE lemma₁ #-}

lemma₂ : {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Δ Ξ} (A : Ty Γ) (B : Ty Δ) (C : Ty Ξ) (b : Ad _ B (C [ τ ]₁)) → (b [ σ ]ₐ) [ WkTm Γ + A ]ₐ ≡ b [ σ ∘ (WkTm Γ + A) ]ₐ
lemma₂ {Γ} {Δ} {Ξ} {σ} {τ} A B C b = [∘]ₐ b (WkTm Γ + A) σ
{-#REWRITE lemma₂ #-}

{- Definable structure : parallel extension, and associated lemmas -}
_▹▹[_,_]_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) {A : Ty (Γ ^ d)} (B : Ty (Δ ^ d)) (a : Ad _ A (B [ σ ^ₛ d ]₁)) → Sub (Γ ▹[ d ] A) (Δ ▹[ d ] B)
σ ▹▹[ + , A ] a = (σ ∘ (WkTm _ _ _)) ▹ₛ[ + , A ] adapt (a [ WkTm _ _ _ ]ₐ) vztm
σ ▹▹[ - , A ] a = ((σ ^ₛ -) ▹▹[ + , A ] a) ^ₛ -

{-#REWRITE [id]ₐ [∘]ₐ id[]ₐ ∘[]ₐ adaptid adapt∘ #-}
id▹▹id : (Γ : Ctx) (d : Dir) (A : Ty (Γ ^ d)) → id Γ ▹▹[ d , A ] (idₐ {A = A}) ≡ id (Γ ▹[ d ] A)
id▹▹id Γ + A = SubEta (id _)
id▹▹id Γ - A = SubEta- (id _)

{-#REWRITE ⋄ₛ∘ adapt[]₂ #-}
▹▹∘▹▹ : (d : Dir) {Γ Δ Ξ : Ctx} {τ : Sub Δ Ξ} {σ : Sub Γ Δ} {A : Ty (Γ ^ d)} {B : Ty (Δ ^ d)} {C : Ty (Ξ ^ d)} (a : Ad _ A (B [ σ ^ₛ d ]₁)) (b : Ad _ B (C [ τ ^ₛ d ]₁)) →
        (τ ▹▹[ d , C ] b) ∘ (σ ▹▹[ d , B ] a) ≡ (τ ∘ σ) ▹▹[ d , C ] ((b [ σ ^ₛ d ]ₐ) ∘ₐ a)
▹▹∘▹▹ + a b = refl
▹▹∘▹▹ - a b = refl

▹▹∘▹ : (d : Dir) {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Δ Ξ} {A : Ty (Δ ^ d)} {B : Ty (Ξ ^ d)} (t : Tm (A [ σ ^ₛ d ]₁)) (a : Ad _ A (B [ τ ^ₛ d ]₁)) →
         (τ ▹▹[ d , B ] a) ∘ (σ ▹ₛ[ d , A ] t) ≡ (τ ∘ σ) ▹ₛ[ d , B ] (adapt (a [ σ ^ₛ d ]ₐ) t)
▹▹∘▹ + t a = refl
▹▹∘▹ - t a = refl

{- Appendix C.5 : Telescopes -}
postulate
  Tel   : Ctx → Set
  TelAd  : (Γ : Ctx) (Θ Θ' : Tel Γ) → Set
  Inst  : (Γ : Ctx) → Tel Γ → Set

-- CtxExtTel
  _▹₃[_]_ : (Γ : Ctx) → (d : Dir) → Tel (Γ ^ d) → Ctx

-- TelEmp
  ⋄ₜ       : {Γ : Ctx} → Tel Γ

-- TelExtTy
  _▹ₜ_     : {Γ : Ctx} (Θ : Tel Γ) → (A : Ty (Γ ▹₃[ + ] Θ)) → Tel Γ

-- WkTel
  WkTel    : {Γ : Ctx} (d : Dir) (Θ : Tel (Γ ^ d)) → Sub (Γ ▹₃[ d ] Θ) Γ

-- SubTel
  _[_]₃    : {Γ Δ : Ctx} → Tel Δ → Sub Γ Δ → Tel Γ

-- TransTel
  _⟦_⟧₃    : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (Θ : Tel Δ) (μ : Trans Γ Δ σ τ) → TelAd Γ (Θ [ σ ]₃) (Θ [ τ ]₃)

-- AdInst
  teladapt : {Γ : Ctx} {Θ Θ' : Tel Γ} → TelAd Γ Θ Θ' →  Inst Γ Θ  → Inst Γ Θ'

-- VarInst
  vinst : {Γ : Ctx} (Θ : Tel Γ) → Inst (Γ ▹₃[ + ] Θ) (Θ [ WkTel + Θ ]₃)

-- SubExtInst
  _▹ₛᵢ[_]⟦_,_⟧ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) → Sub Γ (Δ ▹₃[ d ] Θ)

-- TransExt+Inst
  _▹ₜᵢ₊⟦_,_⟧ : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) (Θ : Tel Δ) (ι : Inst Γ (Θ [ σ ]₃)) → Trans Γ (Δ ▹₃[ + ] Θ) (σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧) (τ ▹ₛᵢ[ + ]⟦ Θ , teladapt (Θ ⟦ μ ⟧₃) ι ⟧)

-- TransExt-Inst
  _▹ₜᵢ₋⟦_,_⟧ : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) (Θ : Tel (Δ ^ -)) → (ι : Inst (Γ ^ -) (Θ [ τ ^ₛ - ]₃)) → Trans Γ (Δ ▹₃[ - ] Θ) (σ ▹ₛᵢ[ - ]⟦ Θ , teladapt (Θ ⟦ μ ^ₘ - ⟧₃) ι ⟧) (τ ▹ₛᵢ[ - ]⟦ Θ , ι ⟧)

-- SubTelId
  [id]₃ : {Δ : Ctx} {Θ : Tel Δ} → Θ [ id Δ ]₃ ≡ Θ

-- SubTelComp
  [∘]₃ : {Γ Δ Φ : Ctx} {σ : Sub Φ Δ} {δ : Sub Γ Φ} {Θ : Tel Δ} → Θ [ σ ]₃ [ δ ]₃ ≡ Θ [ σ ∘ δ ]₃
  {-#REWRITE [∘]₃ [id]₃ #-}

-- SubTelOnEmp
  ⋄ₜ[]₃ : {Γ Δ : Ctx} {σ : Sub Γ Δ} → ⋄ₜ {Γ = Δ} [ σ ]₃ ≡ ⋄ₜ
  {-#REWRITE ⋄ₜ[]₃ #-}

-- SubTelOnExt
  ▹₃[] : {Γ Δ : Ctx} {Θ : Tel Δ} {A : Ty (Δ ▹₃[ + ] Θ)} {σ : Sub Γ Δ} → (Θ ▹ₜ A) [ σ ]₃ ≡ (Θ [ σ ]₃) ▹ₜ (A [ (σ ∘ (WkTel + (Θ [ σ ]₃))) ▹ₛᵢ[ + ]⟦ Θ , vinst _ ⟧ ]₁)
  {-#REWRITE ▹₃[] #-}

-- SubInst
  _[_]₄ : {Γ Δ : Ctx} {Θ : Tel Δ} → Inst Δ Θ → (σ : Sub Γ Δ) → Inst Γ (Θ [ σ ]₃)

-- SubInstId
  [id]₄ : {Δ : Ctx} {Θ : Tel Δ} {ι : Inst Δ Θ} → ι [ id Δ ]₄ ≡ ι

-- SubInstComp
  [∘]₄ : {Γ Δ Φ : Ctx} {σ : Sub Φ Δ} {δ : Sub Γ Φ} {Θ : Tel Δ} {ι : Inst Δ Θ} → ι [ σ ]₄ [ δ ]₄ ≡ ι [ σ ∘ δ ]₄
  {-# REWRITE [id]₄ [∘]₄ #-}

-- TelAdId
  idₜₐ    : {Δ : Ctx} {Θ : Tel Δ} → TelAd Δ Θ Θ

-- TelAdComp
  _∘ₜₐ_   : {Δ : Ctx} {A B C : Tel Δ} → TelAd Δ B C → TelAd Δ A B → TelAd Δ A C

-- SubTelAd
  _[_]ₜₐ  : {Γ Δ : Ctx} {A B : Tel Δ} → TelAd Δ A B → (σ : Sub Γ Δ) → TelAd Γ (A [ σ ]₃) (B [ σ ]₃)

-- TelAdRightUnitality
  ∘ₜₐid : {Δ : Ctx} {A B : Tel Δ} (ta : TelAd Δ A B) → ta ∘ₜₐ idₜₐ ≡ ta

-- TelAdLeftUnitality
  id∘ₜₐ : {Δ : Ctx} {A B : Tel Δ} (ta : TelAd Δ A B) → idₜₐ ∘ₜₐ ta ≡ ta

-- TelAdAssociatitvity
  ∘ₜₐassoc : {Δ : Ctx} {A B C D : Tel Δ} (a : TelAd Δ A B) (b : TelAd Δ B C) (c : TelAd Δ C D) → c ∘ₜₐ (b ∘ₜₐ a) ≡ (c ∘ₜₐ b) ∘ₜₐ a
  {-#REWRITE ∘ₜₐassoc ∘ₜₐid id∘ₜₐ #-}

-- SubTelAdId
  [id]ₜₐ  : {Δ : Ctx} {A B : Tel Δ} {ad : TelAd Δ A B} → ad [ id Δ ]ₜₐ ≡ ad

-- SubTelAdComp
  [∘]ₜₐ   : {Γ Δ Ξ : Ctx} {A B : Tel Δ} (a : TelAd Δ A B) (σ : Sub Γ Δ) (τ : Sub Ξ Γ) → a [ σ ]ₜₐ [ τ ]ₜₐ ≡ a [ σ ∘ τ ]ₜₐ

-- SubTelAdOnId
  id[]ₜₐ  : {Γ Δ : Ctx} {A : Tel Δ} (σ : Sub Γ Δ) → idₜₐ {Θ = A} [ σ ]ₜₐ ≡ idₜₐ

-- SubTelAdOnComp
  ∘[]ₜₐ : {Γ Δ : Ctx} {A B C : Tel Δ} (a : TelAd Δ B C) (b : TelAd Δ A B) (σ : Sub Γ Δ) → (a ∘ₜₐ b) [ σ ]ₜₐ ≡ (a [ σ ]ₜₐ) ∘ₜₐ (b [ σ ]ₜₐ)
  {-#REWRITE [id]ₜₐ [∘]ₜₐ id[]ₜₐ ∘[]ₜₐ #-}

-- TransTelNaturality
  TelAdaptTrans   : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A B : Tel Δ} (f : TelAd Δ A B) (μ : Trans Γ Δ σ τ) → (B ⟦ μ ⟧₃) ∘ₜₐ (f [ σ ]ₜₐ) ≡ (f [ τ ]ₜₐ) ∘ₜₐ (A ⟦ μ ⟧₃)

-- TransTelId
  ⟦id⟧₃ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {Θ : Tel Δ} → Θ ⟦ idₘ {σ = σ} ⟧₃ ≡ idₜₐ

-- SubTelAdTransTel
  placeholder : {!!}

-- TransTelSubTel
  placeholder2 : {!!}

-- InstTransTel
  InstTransTel : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {A : Tel Δ} (t : Inst Δ A) (μ : Trans Γ Δ σ τ) → (teladapt (A ⟦ μ ⟧₃) (t [ σ ]₄)) ≡ (t [ τ ]₄)
  {-#REWRITE TelAdaptTrans InstTransTel #-}

-- AdInstId
  teladapt-id : {Γ : Ctx} {Θ : Tel Γ} (ι : Inst Γ Θ) → teladapt (idₜₐ {Θ = Θ}) ι ≡ ι

-- AdInstComp
  teladapt∘ : {Γ : Ctx} {Θ Θ' Θ'' : Tel Γ} (ta : TelAd Γ Θ Θ') (ta' : TelAd Γ Θ' Θ'') (ι : Inst Γ Θ) → teladapt (ta' ∘ₜₐ ta) ι ≡ teladapt ta' (teladapt ta ι)
  {-#REWRITE teladapt-id teladapt∘ #-}

-- SubInstOnAdInst
  teladapt[]₄ : {Γ Δ : Ctx} {A B : Tel Δ} (a : TelAd Δ A B) (t : Inst Δ A) (σ : Sub Γ Δ) → (teladapt a t) [ σ ]₄ ≡ teladapt (a [ σ ]ₜₐ) (t [ σ ]₄)
  {-#REWRITE teladapt[]₄ #-}

-- CtxExtTelDual
  ▹₃^- : {Γ : Ctx} (Θ : Tel (Γ ^ d)) → (Γ ▹₃[ d ] Θ) ^ - ≡ (Γ ^ -) ▹₃[ − d ] Θ
  {-#REWRITE ▹₃^- #-}

-- SubExtInstDual
  ▹ₛᵢ^- : {Γ Δ : Ctx} {σ : Sub Γ Δ} (Θ : Tel (Δ ^ d)) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) → (σ ▹ₛᵢ[ d ]⟦ Θ , ι ⟧) ^ₛ - ≡ ((σ ^ₛ -) ▹ₛᵢ[ − d ]⟦ Θ , ι ⟧)
  {-#REWRITE ▹ₛᵢ^- #-}

-- WkTelDual
  WkTel^- : {Δ : Ctx} (Θ : Tel (Δ ^ d)) → (WkTel {Δ} d Θ) ^ₛ - ≡ WkTel {Δ ^ - } (− d) Θ
  {-#REWRITE WkTel^- #-}

-- VarInstAdTrans
  adapt-vinst : {Γ Δ : Ctx} {A : Tel Δ} {σ τ : Sub Γ (Δ ▹₃[ + ] A)} (μ : Trans Γ (Δ ▹₃[ + ] A) σ τ) →  teladapt (A ⟦ whiskerLeft (WkTel + A) μ ⟧₃) (vinst A [ σ ]₄) ≡ vinst A [ τ ]₄
  {-#REWRITE adapt-vinst #-}

-- InstEmp
  ⋄ᵢ : {Γ : Ctx} → Inst Γ ⋄ₜ

-- InstExtTm
  [_]_▹ᵢ_ : (Γ : Ctx) {Θ : Tel Γ} (ι : Inst Γ Θ) {T : Ty (Γ ▹₃[ + ] Θ)} → Tm (T [ id Γ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧ ]₁) → Inst Γ (Θ ▹ₜ T)

-- InstTelEmp
  ⋄ₜ⇒⋄ᵢ : {Γ : Ctx} (ι : Inst Γ ⋄ₜ) → ι ≡ ⋄ᵢ

-- SubOnInstEmp
  ⋄ᵢ[] : {Γ Δ : Ctx} {σ : Sub Γ Δ} → ⋄ᵢ [ σ ]₄ ≡ ⋄ᵢ
  {-#REWRITE ⋄ᵢ[] #-}

-- SubExtInstTl
  SubTlᵢ        : {Γ Δ : Ctx} {σ : Sub Γ Δ} {Θ : Tel (Δ ^ d)} (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) → (WkTel d Θ) ∘ (σ ▹ₛᵢ[ d ]⟦ Θ , ι ⟧) ≡ σ
  {-#REWRITE SubTlᵢ #-}

-- SubExtInstEta
  SubEtaᵢ        : {Γ Δ : Ctx} {Θ : Tel Δ} (σ : Sub Γ (Δ ▹₃[ + ] Θ)) → ((WkTel + Θ) ∘ σ) ▹ₛᵢ[ + ]⟦ Θ , (vinst Θ [ σ ]₄) ⟧ ≡ σ
  {-#REWRITE SubEtaᵢ #-}

-- SubInstExtVarInst
  SubHdᵢ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel Δ) (t : Inst Γ (Θ [ σ ]₃)) → vinst Θ [ σ ▹ₛᵢ[ + ]⟦ Θ , t ⟧ ]₄ ≡ t
  {-#REWRITE SubHdᵢ #-}

-- Provable lemmas needed for computations

SubTlᵢComp : {Γ Δ Ξ : Ctx} {A : Tel Δ} {τ : Sub Ξ Γ } {σ : Sub Γ Δ} {t : Inst _ (A [ σ ]₃) } → WkTel + A ∘ (σ ▹ₛᵢ[ + ]⟦ A , t ⟧) ∘ τ ≡ σ ∘ τ
SubTlᵢComp {Γ} {Δ} {Ξ} {A} {τ} {σ} {t} = sym (∘assoc (WkTel + A) (σ ▹ₛᵢ[ + ]⟦ A , t ⟧) τ)
{-#REWRITE SubTlᵢComp #-}

SubHdᵢComp : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Ξ Γ) (A : Tel Δ) (t : Inst _ (A [ σ ]₃)) → (vinst A) [ (σ ▹ₛᵢ[ + ]⟦ A , t ⟧) ∘ τ ]₄ ≡ (t [ τ ]₄)
SubHdᵢComp σ τ A t = sym ([∘]₄ {σ = σ ▹ₛᵢ[ + ]⟦ A , t ⟧} {δ = τ} {ι = vinst A})
{-#REWRITE SubHdᵢComp #-}

SubEtaᵢ- : {Γ Δ : Ctx} {A : Tel (Δ ^ -)} (σ : Sub Γ (Δ ▹₃[ - ] A)) → (((WkTel + A) ∘ (σ ^ₛ -)) ▹ₛᵢ[ + ]⟦ A , ((vinst A) [ σ ^ₛ - ]₄) ⟧) ^ₛ -  ≡ σ
SubEtaᵢ- σ = σ⁻⁻ σ
{-#REWRITE SubEtaᵢ- #-}

∘ᵢ▹ₛᵢ : {d : Dir} {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Ξ Γ} {Θ : Tel (Δ ^ d)} {ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)} → (σ ▹ₛᵢ[ d ]⟦ Θ , ι ⟧) ∘ τ ≡ ((σ ∘ τ) ▹ₛᵢ[ d ]⟦ Θ , ι [ τ ^ₛ d ]₄ ⟧ )
∘ᵢ▹ₛᵢ {+} {Γ} {Δ} {Ξ} {σ} {τ} {Θ} {ι} = sym (SubEtaᵢ (σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧ ∘ τ))
∘ᵢ▹ₛᵢ { - } {Γ} {Δ} {Ξ} {σ} {τ} {Θ} {ι} = sym (SubEtaᵢ- (σ ▹ₛᵢ[ - ]⟦ Θ , ι ⟧ ∘ τ))
{-#REWRITE ∘ᵢ▹ₛᵢ #-}

SubEtaidᵢ : {Δ : Ctx} {Θ : Tel Δ} → (WkTel + Θ) ▹ₛᵢ[ + ]⟦ Θ , vinst Θ ⟧ ≡ id (Δ ▹₃[ + ] Θ)
SubEtaidᵢ {Δ} {Θ} = SubEtaᵢ (id (Δ ▹₃[ + ] Θ))
{-#REWRITE SubEtaidᵢ #-}

▹₃^d : (d' : Dir) {Γ : Ctx} (Θ : Tel (Γ ^ d)) → (Γ ▹₃[ d ] Θ) ^ d' ≡ (Γ ^ d') ▹₃[ d' × d ] Θ
▹₃^d + Θ = refl
▹₃^d - Θ = refl
{-#REWRITE ▹₃^d #-}
▹ₛᵢ^d : (d' : Dir) {Γ Δ : Ctx} {σ : Sub Γ Δ} (Θ : Tel (Δ ^ d)) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) → (σ ▹ₛᵢ[ d ]⟦ Θ , ι ⟧) ^ₛ d' ≡ ((σ ^ₛ d') ▹ₛᵢ[ d' × d ]⟦ Θ , ι ⟧)
▹ₛᵢ^d + Θ ι = refl
▹ₛᵢ^d - Θ ι = refl
{-#REWRITE ▹ₛᵢ^d #-}


postulate
-- CtxExtTelEmp
  ▹₃⋄  : {Γ : Ctx} → Γ ▹₃[ d ] ⋄ₜ ≡ Γ

-- CtxExtTelExt
  ▹₃▹ : (d : Dir) {Γ : Ctx} (Θ : Tel (Γ ^ d)) (A : Ty ((Γ ^ d) ▹₃[ + ] Θ)) → Γ ▹₃[ d ] (Θ ▹ₜ A) ≡ (Γ ▹₃[ d ] Θ) ▹[ d ] A
  {-#REWRITE ▹₃⋄ ▹₃▹ #-}

-- WkTelWkTy
  WkTel▹ : {d : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} {A : Ty ((Γ ^ d) ▹₃[ + ] Θ)} → WkTel {Γ} d Θ ∘ WkTm (Γ ▹₃[ d ] Θ) d A ≡ WkTel d (Θ ▹ₜ A)
  {-#REWRITE WkTel▹ #-}

-- more provable lemmas
▹₃₊⋄  : {Γ : Ctx} → Γ ▹₃[ + ] ⋄ₜ ≡ Γ
▹₃₊⋄ {Γ} = ▹₃⋄ {d = +} {Γ}
{-#REWRITE ▹₃₊⋄ #-}
▹₃₊▹ : {Γ : Ctx} (Θ : Tel Γ) (A : Ty (Γ ▹₃[ + ] Θ)) → Γ ▹₃[ + ] (Θ ▹ₜ A) ≡ (Γ ▹₃[ + ] Θ) ▹[ + ] A
▹₃₊▹ Θ A = ▹₃▹ + Θ A
{-#REWRITE ▹₃₊▹ #-}


lemma : (Γ Δ : Ctx)(σ : Sub Γ Δ) (Θ : Tel Δ) (t : Inst Γ (Θ [ σ ]₃)) → vinst (Θ [ σ ]₃) [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , t ⟧ ]₄ ≡ t
lemma Γ Δ σ Θ t = SubHdᵢ (id Γ) (Θ [ σ ]₃) t
{-#REWRITE lemma #-}

lemma₃ : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ)(τ : Sub Δ Ξ) (Θ : Tel Δ) (Θ' : Tel Ξ) (a : TelAd Δ Θ (Θ' [ τ ]₃)) (t : Inst Γ (Θ [ σ ]₃)) → (a [ WkTel + Θ ]ₜₐ) [ σ ▹ₛᵢ[ + ]⟦ Θ , t ⟧ ]ₜₐ ≡ (a [ σ ]ₜₐ)
lemma₃ σ τ Θ Θ' a t = [∘]ₜₐ a (WkTel + Θ) (σ ▹ₛᵢ[ + ]⟦ Θ , t ⟧)
{-#REWRITE lemma₃ #-}

lemma₄ : {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Δ Ξ} (A : Tel Γ) (B : Tel Δ) (C : Tel Ξ) (b : TelAd Δ B (C [ τ ]₃)) → b [ σ ]ₜₐ [ WkTel + A ]ₜₐ ≡ (b [ σ ∘ (WkTel + A) ]ₜₐ)
lemma₄ {Γ} {Δ} {Ξ} {σ} {τ} A B C b = [∘]ₜₐ b σ (WkTel + A)
{-#REWRITE lemma₄ #-}

-- {- Derivable operations : telescopic parallel extension  -}
-- SubTelAd
_▹▹₃[_]⟦_,_⟧ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) {Θ : Tel (Γ ^ d)} (Θ' : Tel (Δ ^ d)) (t : TelAd (Γ ^ d) Θ (Θ' [ σ ^ₛ d ]₃)) → Sub (Γ ▹₃[ d ] Θ) (Δ ▹₃[ d ] Θ')
_▹▹₃[_]⟦_,_⟧ {Γ} {Δ} σ + {Θ} Θ' t = (σ ∘ (WkTel {Γ = Γ} + Θ)) ▹ₛᵢ[ + ]⟦ Θ' , teladapt (t [ WkTel {Γ = Γ} + Θ ]ₜₐ) (vinst Θ) ⟧
σ ▹▹₃[ - ]⟦ Θ' , t ⟧ = ((σ ^ₛ -) ▹▹₃[ + ]⟦ Θ' , t ⟧) ^ₛ -

id▹▹₃id : (Γ : Ctx) (d : Dir) (Θ : Tel (Γ ^ d)) → (id Γ) ▹▹₃[ d ]⟦ Θ , idₜₐ {Θ = Θ} ⟧ ≡ id (Γ ▹₃[ d ] Θ)
id▹▹₃id Γ + A = refl
id▹▹₃id Γ - A = refl

▹▹₃∘▹▹₃ : {Γ Δ Ξ : Ctx} (d : Dir) {τ : Sub Δ Ξ} {σ : Sub Γ Δ} {Θ : Tel (Γ ^ d)} {Θ' : Tel (Δ ^ d)} {Θ'' : Tel (Ξ ^ d)} (a : TelAd (Γ ^ d) Θ (Θ' [ σ ^ₛ d ]₃)) (b : TelAd (Δ ^ d) Θ' (Θ'' [ τ ^ₛ d ]₃)) →
        (τ ▹▹₃[ d ]⟦ Θ'' , b ⟧) ∘ (σ ▹▹₃[ d ]⟦ Θ' , a ⟧) ≡ (τ ∘ σ) ▹▹₃[ d ]⟦ Θ'' , (b [ σ ^ₛ d ]ₜₐ) ∘ₜₐ a ⟧
▹▹₃∘▹▹₃ + a b = refl
▹▹₃∘▹▹₃ - a b = refl

▹▹₃∘▹ : (d : Dir) {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Δ Ξ} {A : Tel (Δ ^ d)} {B : Tel (Ξ ^ d)} (t : Inst _ (A [ σ ^ₛ d ]₃)) (a : TelAd (Δ ^ d) A (B [ τ ^ₛ d ]₃)) → (τ ▹▹₃[ d ]⟦ B , a ⟧) ∘ (σ ▹ₛᵢ[ d ]⟦ A , t ⟧) ≡ (τ ∘ σ) ▹ₛᵢ[ d ]⟦ B , teladapt (a [ σ ^ₛ d ]ₜₐ) t ⟧
▹▹₃∘▹ + t a = refl
▹▹₃∘▹ - t a = refl
{-#REWRITE id▹▹₃id #-}

postulate
-- VarInstExtVarZ
  placeholder3 : {!!}

-- SubExtInstEmp
  ▹ₛᵢ⋄ᵢ : {Γ Δ : Ctx} (σ : Sub Γ Δ)  → σ ▹ₛᵢ[ d ]⟦ ⋄ₜ , ⋄ᵢ ⟧ ≡ σ
  {-#REWRITE ▹ₛᵢ⋄ᵢ #-}

-- SubExtInstExt
  ▹ₛᵢ▹ᵢ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {Θ : Tel Δ} (ι : Inst Γ (Θ [ σ ]₃)) {A : Ty (Δ ▹₃[ + ] Θ)} (t : Tm (A [ σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧ ]₁)) → σ ▹ₛᵢ[ + ]⟦ Θ ▹ₜ A , ([ Γ ] ι ▹ᵢ t) ⟧ ≡ ((σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧) ▹ₛ[ + , A ] t)

-- TelAdExt
  _▹ₜₐ_ : {Γ : Ctx} {Θ Θ' : Tel Γ} (ta : TelAd Γ Θ Θ') {A : Ty (Γ ▹₃[ + ] Θ)} {A' : Ty (Γ ▹₃[ + ] Θ')} (a : Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ Θ' , ta ⟧ ]₁)) → TelAd Γ (Θ ▹ₜ A) (Θ' ▹ₜ A')

-- TelAdExtId
  id▹ₜₐid : {Γ : Ctx} {Θ : Tel Γ} {A : Ty (Γ ▹₃[ + ] Θ)}  → _▹ₜₐ_ {Γ} {Θ} {Θ} (idₜₐ {Γ} {Θ}) {A} {A} (idₐ {A = A}) ≡ idₜₐ

-- TelAdExtComp
  ∘▹ₜₐ∘  : {Γ : Ctx} {Θ Θ' Θ'' : Tel Γ}
          (ta : TelAd Γ Θ Θ') (ta' : TelAd Γ Θ' Θ'')
          {A : Ty (Γ ▹₃[ + ] Θ)} {A' : Ty (Γ ▹₃[ + ] Θ')}
          {A'' : Ty (Γ ▹₃[ + ] Θ'')}
          (a : Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ _ , ta ⟧  ]₁))
          (b : Ad _ A' (A'' [ id Γ ▹▹₃[ + ]⟦ _ , ta' ⟧ ]₁)) →
          (_▹ₜₐ_ {Γ} {Θ'} {Θ''} ta'{A'} {A''} b) ∘ₜₐ (_▹ₜₐ_ {Γ} {Θ} {Θ'} ta {A} {A'} a) ≡ (_▹ₜₐ_ {Γ} {Θ} {Θ''} (ta' ∘ₜₐ ta) {A} {A''} ((b [ id (Γ) ▹▹₃[ + ]⟦ _ , ta ⟧ ]ₐ) ∘ₐ a))

-- TransInst+
  _▹ₘᵢ₊⟦_,_⟧  : {Γ Δ : Ctx} {σ τ : Sub Γ Δ}  (μ : Trans Γ Δ σ τ) (Θ : Tel Δ) (ι : Inst Γ (Θ [ σ ]₃)) → Trans Γ (Δ ▹₃[ + ] Θ) (σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧) (τ ▹ₛᵢ[ + ]⟦ Θ , teladapt (Θ ⟦ μ ⟧₃) ι ⟧)

-- TransInst-
  _▹ₘᵢ₋⟦_,_⟧  : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) (Θ : Tel (Δ ^ -)) (ι : Inst (Γ ^ -) (Θ [ τ ^ₛ - ]₃)) → Trans Γ (Δ ▹₃[ - ] Θ) (σ ▹ₛᵢ[ - ]⟦ Θ , teladapt (Θ ⟦ μ ^ₘ - ⟧₃) ι ⟧ ) (τ ▹ₛᵢ[ - ]⟦ Θ , ι ⟧)

-- TransInst+Tl
  TransTlᵢ₊     : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) {Θ : Tel Δ} (ι : Inst Γ (Θ [ σ ]₃)) → whiskerLeft (WkTel + Θ) (μ ▹ₘᵢ₊⟦ Θ , ι ⟧) ≡ μ

-- TransInst-Tl
  TransTlᵢ₋     : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) {Θ : Tel (Δ ^ -)} (ι : Inst (Γ ^ -) (Θ [ τ ^ₛ - ]₃)) →  whiskerLeft (WkTel - Θ) (μ ▹ₘᵢ₋⟦ Θ , ι ⟧) ≡ μ

-- TransInstEta
  TransEtaᵢ     : {Γ Δ : Ctx} {Θ : Tel Δ} {σ τ : Sub Γ (Δ ▹₃[ + ] Θ)} (μ : Trans Γ (Δ ▹₃[ + ] Θ) σ τ) → (whiskerLeft (WkTel + Θ) μ) ▹ₘᵢ₊⟦ Θ , vinst Θ [ σ ]₄ ⟧  ≡ μ
  {-#REWRITE TransTlᵢ₊ TransTlᵢ₋ TransEtaᵢ #-}

-- TransInst+Dual
  ▹ₘᵢ₊^- : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {Θ : Tel Δ} (μ : Trans Γ Δ σ τ) (ι : Inst Γ (Θ [ σ ]₃)) → (μ ▹ₘᵢ₊⟦ Θ , ι ⟧) ^ₘ - ≡ (μ ^ₘ -) ▹ₘᵢ₋⟦ Θ , ι ⟧
  {-#REWRITE ▹ₘᵢ₊^- #-}

-- TransInst-Dual
  ▹ₘᵢ₋^- : {Γ Δ : Ctx} {σ τ : Sub Γ Δ} {Θ : Tel (Δ ^ -)} (μ : Trans Γ Δ σ τ) (ι : Inst (Γ ^ -) (Θ [ τ ^ₛ - ]₃)) → (μ ▹ₘᵢ₋⟦ Θ , ι ⟧) ^ₘ - ≡ (μ ^ₘ -) ▹ₘᵢ₊⟦ Θ , ι ⟧
  {-#REWRITE ▹ₘᵢ₋^- #-}

-- TelExtTel
  _++ₜ_ : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) → Tel Γ

-- InstExtInst
  _++ᵢ_ : {Γ : Ctx} {Θ₁ : Tel Γ} (ι₁ : Inst Γ Θ₁) {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (ι₂ : Inst (Γ ▹₃[ + ] Θ₁) Θ₂) → Inst Γ (Θ₁ ++ₜ Θ₂)

-- CtxExtTelExtTel
  ▹₃++ₜ : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) → Γ ▹₃[ + ] (Θ₁ ++ₜ Θ₂) ≡ ((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)
  {-# REWRITE ▹₃++ₜ #-}

-- TelExtTelEmp
  ++ₜ⋄ₜ : {Γ : Ctx} (Θ₁ : Tel Γ) → Θ₁ ++ₜ ⋄ₜ ≡ Θ₁
  {-#REWRITE ++ₜ⋄ₜ #-}

-- TelExtTelExtTy
  ++ₜ▹ₜ : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) (A : Ty ((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)) → Θ₁ ++ₜ (Θ₂ ▹ₜ A) ≡ (Θ₁ ++ₜ Θ₂) ▹ₜ A
  {-#REWRITE ++ₜ▹ₜ #-}

-- TelExtTelExtTel
  ++ₜ++ₜ : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) (Θ₃ : Tel ((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)) → Θ₁ ++ₜ (Θ₂ ++ₜ Θ₃) ≡ (Θ₁ ++ₜ Θ₂) ++ₜ Θ₃
  {-#REWRITE ++ₜ++ₜ #-}

-- SubTelOnExtTel
  ++ₜ[] : {Γ Δ : Ctx}
    (σ : Sub Δ Γ)
    (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) →
    (Θ₁ ++ₜ Θ₂) [ σ ]₃ ≡ (Θ₁ [ σ ]₃) ++ₜ (Θ₂ [ σ ▹▹₃[ + ]⟦ Θ₁ , idₜₐ {Θ = Θ₁ [ σ ]₃} ⟧ ]₃)
  {-#REWRITE ++ₜ[]  #-}

-- WkTelWkTel
  WkTel++ₜWkTel : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) → WkTel + Θ₁ ∘ WkTel + Θ₂ ≡ WkTel + (Θ₁ ++ₜ Θ₂)
  {-#REWRITE WkTel++ₜWkTel #-}

-- TelAdExtTelAd
  _++ₜₐ⟦_,_⟧ :
     {Γ : Ctx}
     {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (Θ₂' : Tel (Γ ▹₃[ + ] Θ₁')) (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃))
    → TelAd Γ (Θ₁ ++ₜ Θ₂) (Θ₁' ++ₜ Θ₂')

-- TelAdExtTelAdEmp
  _++ₜₐ⟦⋄ₜ⟧ :
    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) ⋄ₜ ⋄ₜ)
    → ta₁ ++ₜₐ⟦ ⋄ₜ , ta₂ ⟧ ≡ ta₁
  {-# REWRITE _++ₜₐ⟦⋄ₜ⟧ #-}

-- TelAdExtTelAdExtAd
  _++ₜₐ⟦▹ₐ⟧ :
    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)}
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (Θ₂' : Tel (Γ ▹₃[ + ] Θ₁')) (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃))
    {A : Ty ((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)} {A' : Ty ((Γ ▹₃[ + ] Θ₁') ▹₃[ + ] Θ₂')}
    (a :  Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ▹▹₃[ + ]⟦ _ , ta₂ ⟧ ]₁))
    → ta₁ ++ₜₐ⟦ Θ₂' ▹ₜ A' , ta₂ ▹ₜₐ a ⟧ ≡ _▹ₜₐ_ {Γ = Γ} {Θ = Θ₁ ++ₜ Θ₂} {Θ' = Θ₁' ++ₜ Θ₂'} (ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧) {A = A} {A' = A'} {!a!}

-- TelAdExtTelAdExtTelAd
  _++ₜₐ⟦++ₜₐ⟧ :
    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} {Θ₂' : Tel (Γ ▹₃[ + ] Θ₁')}
    (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃))
    {Θ₃ : Tel ((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)} {Θ₃' : Tel ((Γ ▹₃[ + ] Θ₁') ▹₃[ + ] Θ₂')}
    (ta₃ :  TelAd _ Θ₃ (Θ₃' [ id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧ ▹▹₃[ + ]⟦ Θ₂' , ta₂ ⟧ ]₃))
    → ta₁ ++ₜₐ⟦ Θ₂' ++ₜ Θ₃' , ta₂ ++ₜₐ⟦ {!Θ₃!} , ta₃ ⟧  ⟧ ≡  (ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧) ++ₜₐ⟦ {!!} , ta₃ ⟧

-- TelAdExtIdTelAd
  _++ₜₐ⟦id⟧ :
    {Γ : Ctx}
    {Θ₁ : Tel Γ}
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)}
    → idₜₐ {Θ = Θ₁} ++ₜₐ⟦ Θ₂ , idₜₐ  ⟧ ≡  idₜₐ

-- TelAdExtCompTelAd
  ∘++ₜₐ∘  : {Γ : Ctx} {Θ Θ' Θ'' : Tel Γ}
          (ta : TelAd Γ Θ Θ') (ta' : TelAd Γ Θ' Θ'')
          {Θ₁ : Tel (Γ ▹₃[ + ] Θ)} {Θ₁' : Tel (Γ ▹₃[ + ] Θ')}
          {Θ₁'' : Tel (Γ ▹₃[ + ] Θ'')}
          (ta₁ : TelAd _ Θ₁ (Θ₁' [ id Γ ▹▹₃[ + ]⟦ _ , ta ⟧  ]₃))
          (ta₁' : TelAd _ Θ₁' (Θ₁'' [ id Γ ▹▹₃[ + ]⟦ _ , ta' ⟧ ]₃)) →
          (ta' ++ₜₐ⟦ Θ₁'' , ta₁' ⟧) ∘ₜₐ (ta ++ₜₐ⟦ Θ₁' , ta₁ ⟧) ≡ ((ta' ∘ₜₐ ta) ++ₜₐ⟦ Θ₁'' , (ta₁' [ id (Γ) ▹▹₃[ + ]⟦ _ , ta ⟧ ]ₜₐ) ∘ₜₐ ta₁ ⟧)

foo : {Γ Δ : Ctx} {Θ Θ' : Tel Γ} (ta : TelAd Γ Θ Θ') (σ : Sub Δ Γ) →
  teladapt ((ta [ WkTel + Θ ]ₜₐ) [ ((σ ∘ WkTel + (Θ [ σ ]₃)) ^ₛ +) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₜₐ) (vinst Θ [ ((σ ∘ WkTel + (Θ [ σ ]₃)) ^ₛ +) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]₄) ≡
  (vinst (Θ' [ σ ]₃) [ ((id Δ ∘ WkTel + (Θ [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ' [ σ ]₃ , teladapt ((ta [ σ ]ₜₐ) [ WkTel + (Θ [ σ ]₃) ]ₜₐ) (vinst (Θ [ σ ]₃)) ⟧) ]₄)
foo {Θ = Θ} {Θ' = Θ'} ta σ = sym (SubHdᵢ (WkTel + (Θ [ σ ]₃)) (Θ' [ σ ]₃) (teladapt (ta [ σ ∘ WkTel + (Θ [ σ ]₃) ]ₜₐ) (vinst (Θ [ σ ]₃))))
{-#REWRITE foo #-}

postulate
-- SubTelAndOnExtTel
  ▹ₐ[] : {Γ Δ : Ctx} {Θ Θ' : Tel Γ} (ta : TelAd Γ Θ Θ') {A : Ty (Γ ▹₃[ + ] Θ)} {A' : Ty (Γ ▹₃[ + ] Θ')} (a : Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ Θ' , ta ⟧ ]₁)) (σ : Sub Δ Γ)
    → (_▹ₜₐ_ {Θ = Θ} {Θ' = Θ'} ta {A = A} {A' = A'} a)[ σ ]ₜₐ ≡ _▹ₜₐ_ {Θ = Θ [ σ ]₃} {Θ' = Θ' [ σ ]₃} (ta [ σ ]ₜₐ) (a [ (σ ∘ WkTel + (Θ [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₐ)

-- SubTelAndOnExtTelAd
  ++ₜₐ[] : {Γ Δ : Ctx} {Θ Θ' : Tel Γ} (ta₁ : TelAd Γ Θ Θ') {A : Tel (Γ ▹₃[ + ] Θ)} {A' : Tel (Γ ▹₃[ + ] Θ')} (ta₂ : TelAd _ A (A' [ id Γ ▹▹₃[ + ]⟦ Θ' , ta₁ ⟧ ]₃)) (σ : Sub Δ Γ)
    → (ta₁ ++ₜₐ⟦ A' , ta₂ ⟧ )[ σ ]ₜₐ ≡ (ta₁ [ σ ]ₜₐ) ++ₜₐ⟦ A' [ (σ ∘ WkTel + (Θ' [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ' , vinst (Θ' [ σ ]₃) ⟧ ]₃ , ta₂ [ (σ ∘ WkTel + (Θ [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₜₐ ⟧


  ⟦⟧[]₃ : (Γ Δ Ξ : Ctx) (τ ξ : Sub Γ Δ) (μ : Trans Γ Δ τ ξ) (σ : Sub Ξ Γ)
         (Θ : Tel Δ) → Θ ⟦ μ ⟧₃ [ σ ]ₜₐ ≡ Θ ⟦ whiskerRight μ σ ⟧₃
  []⟦⟧₃ : (Γ Δ Ξ : Ctx) (σ : Sub Γ Δ) (τ ξ : Sub Ξ Γ) (μ : Trans Ξ Γ τ ξ)
         (Θ : Tel Δ) → Θ [ σ ]₃ ⟦ μ ⟧₃ ≡ (Θ ⟦ whiskerLeft σ μ ⟧₃)
  {-#REWRITE []⟦⟧₃ #-}


-- -- {- Appendix C.6 : Type variables -}
-- -- postulate
-- --   _▸[_]⟦_,_⟧ :  (Γ : Ctx) (d : Dir) → Tel (Γ ^ d) → Dir → Ctx
-- --   _▸ₛ[_]⟦_,_⟧ : {d' : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) → Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d') → Sub Γ (Δ ▸[ d ]⟦ Θ , d' ⟧)
-- --   _▸ₘ₊_ : {d : Dir} {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
-- --           (μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d))
-- --           {Θ : Tel (Δ ^ d)}
-- --           {A : Ty (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃))}
-- --           {B : Ty (Γ ▹₃[ d ] (Θ [ τ ^ₛ d ]₃))}
-- --           → Ad _ A (B [ id Γ ▹▹₃[ d ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁)
-- --           → Trans Γ (Δ ▸[ d ]⟦ Θ , + ⟧) (σ ▸ₛ[ d ]⟦ Θ , A ⟧) (τ ▸ₛ[ d ]⟦ Θ , B ⟧)
-- --   _▸ₘ₋_ : {d : Dir} {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
-- --           (μ : Trans (Γ ^ (− d)) (Δ ^ (− d)) (σ ^ₛ (− d)) (τ ^ₛ (− d)))
-- --           {Θ : Tel (Δ ^ d)}
-- --           {A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ -)}
-- --           {B : Ty ((Γ ▹₃[ d ] (Θ [ τ ^ₛ d ]₃)) ^ -)}
-- --           → Ad _ B (A [ id (Γ ^ -) ▹▹₃[ − d ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧  ]₁)
-- --           → Trans Γ (Δ ▸[ d ]⟦ Θ , - ⟧) (σ ▸ₛ[ d ]⟦ Θ , A ⟧) (τ ▸ₛ[ d ]⟦ Θ , B ⟧)
-- --   WkTy  : (d : Dir) {Γ : Ctx}  (Θ : Tel (Γ ^ d)) (d' : Dir) → Sub (Γ ▸[ d ]⟦ Θ , d' ⟧) Γ
-- --   tyvz  : (d : Dir) {Γ : Ctx} (Θ : Tel (Γ ^ d)) → Ty ((Γ ▸[ d ]⟦ Θ , + ⟧) ▹₃[ d ]  ( Θ [ (WkTy d {Γ} Θ +) ^ₛ d ]₃))
-- --   ▸⟦⟧^- : {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (Γ ▸[ d ]⟦ Θ , d' ⟧) ^ - ≡ (Γ ^ -) ▸[ − d ]⟦ Θ , − d' ⟧
-- --   {-#REWRITE ▸⟦⟧^- #-}
-- --   WkTy^- : {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (WkTy d {Γ} Θ d') ^ₛ - ≡ WkTy (− d) {Γ ^ - } Θ (− d')
-- --   {-#REWRITE WkTy^- #-}
-- --   ▸ₛ^- : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) →
-- --     (_▸ₛ[_]⟦_,_⟧ {d'} σ d Θ A) ^ₛ - ≡ ((σ ^ₛ -) ▸ₛ[ − d ]⟦ Θ , A ⟧)
-- --   {-#REWRITE ▸ₛ^- #-}

-- --   {-#REWRITE μ⁻⁻-spe #-}
-- --   ▸ₘ₊^- : {d : Dir} {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
-- --           (μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d))
-- --           {Θ : Tel (Δ ^ d)}
-- --           {A : Ty (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃))}
-- --           {B : Ty (Γ ▹₃[ d ] (Θ [ τ ^ₛ d ]₃))}
-- --           (a : Ad _ A (B [ id Γ ▹▹₃[ d ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁)) →
-- --           (_▸ₘ₊_ {d} {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ^ₘ - ≡ ((μ ^ₘ -) ▸ₘ₋ a)
-- --   {-#REWRITE ▸ₘ₊^- #-}
-- --   ▸ₘ₋^- : {d : Dir} {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
-- --           (μ : Trans (Γ ^ (− d)) (Δ ^ (− d)) (σ ^ₛ (− d)) (τ ^ₛ (− d)))
-- --           {Θ : Tel (Δ ^ d)}
-- --           {A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ -)}
-- --           {B : Ty ((Γ ▹₃[ d ] (Θ [ τ ^ₛ d ]₃)) ^ -)}
-- --           (a : Ad _ B (A [ id (Γ ^ -) ▹▹₃[ − d ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧  ]₁)) →
-- --           (_▸ₘ₋_ {d} {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ^ₘ - ≡ ((μ ^ₘ -) ▸ₘ₊ a)
-- --   {-#REWRITE ▸ₘ₋^- #-}

-- -- -- provable results to help agda's computations

-- -- ▸⟦⟧^d : {d d' d'' : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (Γ ▸[ d ]⟦ Θ , d' ⟧) ^ d'' ≡ (Γ ^ d'') ▸[ d × d'' ]⟦ Θ , d' × d'' ⟧
-- -- ▸⟦⟧^d {d} {d'} {+} {Γ} {Θ} = refl
-- -- ▸⟦⟧^d {d} {d'} { - } {Γ} {Θ} = refl
-- -- {-#REWRITE ▸⟦⟧^d #-}
-- -- WkTy^d : {d d' d'' : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (WkTy d {Γ} Θ d') ^ₛ d'' ≡ WkTy (d × d'') {Γ ^ d'' } Θ (d' × d'')
-- -- WkTy^d {d} {d'} {+} {Γ} {Θ} = refl
-- -- WkTy^d {d} {d'} { - } {Γ} {Θ} = refl
-- -- {-#REWRITE WkTy^d #-}
-- -- ▸ₛ^d : {d d' d'' : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel (Δ ^ d)) (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) →
-- --        (_▸ₛ[_]⟦_,_⟧ {d'} σ d Θ A) ^ₛ d'' ≡ ((σ ^ₛ d'') ▸ₛ[ d × d'' ]⟦ Θ , A ⟧)
-- -- ▸ₛ^d {d} {d'} {+} {Γ} {Δ} σ Θ A = refl
-- -- ▸ₛ^d {d} {d'} { - } {Γ} {Δ} σ Θ A = refl
-- -- {-#REWRITE ▸ₛ^d #-}

-- -- lemma₆ : (d : Dir) {Γ Δ : Ctx} {Θ : Tel (Δ ^ d)} {σ τ : Sub Γ Δ} (μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d))
-- --          (ι : Inst (Δ ^ d) Θ) →
-- --          (id Γ ▹▹₃[ d ]⟦ Θ [ τ ^ₛ d ]₃ , Θ ⟦ μ ⟧₃ ⟧) ∘ (id Γ ▹ₛᵢ[ d ]⟦ Θ [ σ ^ₛ d ]₃ , ι [ σ ^ₛ d ]₄ ⟧)  ≡
-- --          id Γ ▹ₛᵢ[ d ]⟦ Θ [ τ ^ₛ d ]₃ , ι [ τ ^ₛ d ]₄ ⟧
-- -- lemma₆ d {Γ} {Δ} {Θ} {σ} {τ}  μ ι = ▹▹₃∘▹ d {Γ = Γ} {Δ = Γ} {σ = id Γ} {τ = id Γ}{A = Θ [ σ ^ₛ d ]₃} {B = Θ [ τ ^ₛ d ]₃} (ι [ σ ^ₛ d ]₄) (Θ ⟦ μ ⟧₃)
-- -- {-#REWRITE lemma₆ #-}

-- -- lemma₇ :  (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ)
-- --           (μ : Trans Γ Δ σ τ) (Θ : Tel Δ) (ι : Inst Γ (Θ [ σ ]₃)) →
-- --           ((Θ ⟦ μ ⟧₃) [ WkTel + (Θ [ σ ]₃) ]ₜₐ) [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]ₜₐ ≡ Θ ⟦ μ ⟧₃
-- -- lemma₇ Γ Δ σ τ μ Θ ι = [∘]ₜₐ (Θ ⟦ μ ⟧₃) (WkTel + (Θ [ σ ]₃)) (id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧)
-- -- {-#REWRITE lemma₇ #-}


-- -- postulate
-- --   SubTlTy : {Γ Δ : Ctx} {σ : Sub Γ Δ} {d d' : Dir} {Θ : Tel (Δ ^ d)} (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) → (WkTy d Θ d') ∘ (σ ▸ₛ[ d ]⟦ Θ , A ⟧) ≡ σ
-- --   {-#REWRITE SubTlTy #-}
-- --   SubHdTy : {d : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel (Δ ^ d))
-- --             (A : Ty (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃))) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) →
-- --             (tyvz d {Δ} Θ) [ (σ ▸ₛ[ d ]⟦ Θ , A ⟧) ▹ₛᵢ[ d ]⟦ Θ [ (WkTy d {Δ} Θ +) ^ₛ d ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ d ]⟦ Θ [ σ ^ₛ d ]₃ , ι ⟧ ]₁
-- --   {-#REWRITE SubHdTy #-}
-- --   SubEtaTy : {Γ Δ : Ctx} {A : Tel (Δ ^ d)} (σ : Sub Γ (Δ ▸[ d ]⟦ A  , + ⟧)) →
-- --              ((WkTy d A +) ∘ σ) ▸ₛ[ d ]⟦ A , tyvz d {Γ = Δ} A [ σ ▹▹₃[ d ]⟦ A [ WkTy + A d ]₃ , idₜₐ ⟧  ]₁ ⟧ ≡ σ
-- --   {-#REWRITE SubEtaTy #-}

-- -- SubHdTy+ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel Δ) (A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))) (ι : Inst Γ (Θ [ σ ]₃)) →
-- --             (tyvz + {Δ} Θ) [ (σ ▸ₛ[ + ]⟦ Θ , A ⟧) ▹ₛᵢ[ + ]⟦ Θ [ WkTy + {Δ} Θ + ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ^ₛ + ]₃ , ι ⟧ ]₁
-- -- SubHdTy+ σ = SubHdTy {+} σ
-- -- {-#REWRITE SubHdTy+ #-}

-- -- postulate
-- --   whisker▸ :
-- --     (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ)
-- --     (μ : Trans Γ Δ σ τ) (Θ : Tel Δ)
-- --     {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))} {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
-- --     (a : Ad (Γ ▹₃[ + ] (Θ [ σ ]₃)) A (B [ id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁))
-- --     → whiskerLeft (WkTy + Θ +) (_▸ₘ₊_ {+} {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ≡ μ
-- --   {-#REWRITE whisker▸ #-}

-- --   TransHdAd : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
-- --               (μ : Trans Γ Δ σ τ)
-- --               {Θ : Tel Δ}
-- --               {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))}
-- --               {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
-- --               (a : Ad (Γ ▹₃[ + ] (Θ [ σ ]₃)) A (B [ id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁))
-- --               (ι : Inst Γ (Θ [ σ ]₃)) →
-- --               (tyvz + {Δ} Θ ⟦ (_▸ₘ₊_ {+} {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ▹ₘᵢ₊⟦ Θ [ WkTy + Θ + ]₃ , ι ⟧ ⟧) ≡ (a [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]ₐ)


-- --   ▸ₛ∘ : (Γ Δ Ξ : Ctx) (σ : Sub Γ Δ) (τ : Sub Ξ Γ) (Θ : Tel Δ) (A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))) → (_▸ₛ[_]⟦_,_⟧ {d' = +} σ + Θ A ) ∘ τ ≡ (σ ∘ τ) ▸ₛ[ + ]⟦ Θ , A [ τ ▹▹₃[ + ]⟦ Θ [ σ ]₃ , idₜₐ ⟧ ]₁ ⟧


-- -- These rules are not necessary for this file. Are they necessary for the other files?:
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

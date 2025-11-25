{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Std
open import Dir
open import AppD1
open import AppD2
open import AppD3
open import AppD4


{- Definition of parallel extension, and associated lemmas -}
lemma₁ : {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ)(τ : Sub Δ Ξ) (A : Ty Δ) (B : Ty Ξ) (a : Ad _ A (B [ τ ]₁)) (t : Tm (A [ σ ]₁)) → (a [ WkTm Δ + A ]ₐ) [ σ ▹ₛ[ + , A ] t ]ₐ ≡ (a [ σ ]ₐ)
lemma₁ {Γ} {Δ} {Ξ} σ τ A B a t = [∘]ₐ a (σ ▹ₛ[ + , A ] t) (WkTm Δ + A)
{-#REWRITE lemma₁ #-}

lemma₂ : {Γ Δ Ξ : Ctx} {σ : Sub Γ Δ} {τ : Sub Δ Ξ} (A : Ty Γ) (B : Ty Δ) (C : Ty Ξ) (b : Ad _ B (C [ τ ]₁)) → (b [ σ ]ₐ) [ WkTm Γ + A ]ₐ ≡ b [ σ ∘ (WkTm Γ + A) ]ₐ
lemma₂ {Γ} {Δ} {Ξ} {σ} {τ} A B C b = [∘]ₐ b (WkTm Γ + A) σ
{-#REWRITE lemma₂ #-}

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

-- TelTransSub
  ⟦⟧[]₃ : (Γ Δ Ξ : Ctx) (τ ξ : Sub Γ Δ) (μ : Trans Γ Δ τ ξ) (σ : Sub Ξ Γ)
         (Θ : Tel Δ) → Θ ⟦ μ ⟧₃ [ σ ]ₜₐ ≡ Θ ⟦ whiskerRight μ σ ⟧₃
-- TelSubTrans
  []⟦⟧₃ : (Γ Δ Ξ : Ctx) (σ : Sub Γ Δ) (τ ξ : Sub Ξ Γ) (μ : Trans Ξ Γ τ ξ)
         (Θ : Tel Δ) → Θ [ σ ]₃ ⟦ μ ⟧₃ ≡ (Θ ⟦ whiskerLeft σ μ ⟧₃)
  {-#REWRITE []⟦⟧₃ #-}

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

-- TransTelComp
  ⟦∘ₜₐ⟧ : {Γ Δ : Ctx} (Θ : Tel Δ) {σ τ ξ : Sub Γ Δ} (μ : Trans Γ Δ σ τ) (ν : Trans Γ Δ τ ξ) -> Θ ⟦ ν *ₘ μ ⟧₃ ≡ ((Θ ⟦ ν ⟧₃) ∘ₜₐ (Θ ⟦ μ ⟧₃))

-- SubTelAdTransTel
  SubTelAdTransTel : {Γ Δ Ξ : Ctx} {Θ : Tel Δ} {σ τ : Sub Γ Δ} {μ : Trans Γ Δ σ τ} (ξ : Sub Ξ Γ) → (Θ ⟦ μ ⟧₃)[ ξ ]ₜₐ ≡ Θ ⟦ whiskerRight μ ξ ⟧₃

-- TransTelSubTel
  TransTelSubTel : {Γ Δ Ξ : Ctx} {Θ : Tel Δ}  {σ : Sub Ξ Δ} {τ ξ : Sub Γ Ξ} {𝜈 : Trans Γ Ξ τ ξ} → (Θ [ σ ]₃)⟦ 𝜈 ⟧₃ ≡  Θ ⟦ whiskerLeft σ 𝜈 ⟧₃

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

SubEtaWkTelCons : {Δ : Ctx} {Θ : Tel Δ} {A : Ty (Δ ▹₃[ + ] Θ)}  → (WkTel + (Θ ▹ₜ A)) ▹ₛᵢ[ + ]⟦ Θ , (vinst Θ) [ WkTm (Δ ▹₃[ + ] Θ) + A ]₄ ⟧ ≡  WkTm (Δ ▹₃[ + ] Θ) + A
SubEtaWkTelCons {Δ} {Θ} {A} = SubEtaᵢ {Θ = Θ} (WkTm (Δ ▹₃[ + ] Θ) + A)
{-#REWRITE SubEtaWkTelCons #-}

postulate
-- VarInstExtVarZ
  VarInstExtVarZ : (d : Dir) {Γ : Ctx} {Θ : Tel (Γ ^ d)} {A : Ty ((Γ ^ d) ▹₃[ + ] Θ)} →
    vinst (Θ ▹ₜ A) ≡
    ([ (Γ ^ d) ▹₃[ + ] (Θ ▹ₜ A) ] (vinst Θ) [ WkTm ((Γ ^ d) ▹₃[ + ] Θ) + A ]₄ ▹ᵢ  vztm)

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
  _extᵢ_ : {Γ : Ctx} {Θ₁ : Tel Γ} (ι₁ : Inst Γ Θ₁) {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (ι₂ : Inst Γ (Θ₂ [ id Γ ▹ₛᵢ[ + ]⟦ Θ₁ , ι₁ ⟧ ]₃) ) → Inst Γ (Θ₁ ++ₜ Θ₂)

_++ᵢ_ : {Γ : Ctx} {Θ₁ : Tel Γ} (ι₁ : Inst Γ Θ₁) {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (ι₂ : Inst (Γ ▹₃[ + ] Θ₁) Θ₂) → Inst Γ (Θ₁ ++ₜ Θ₂)
_++ᵢ_ {Γ} {Θ₁} ι₁ {Θ₂} ι₂ = ι₁ extᵢ (ι₂ [ id Γ ▹ₛᵢ[ + ]⟦ Θ₁ , ι₁ ⟧ ]₄)

postulate
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

-- SubExtInstExtInst
  ▹ₛᵢ▹ₛᵢ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {Θ : Tel Δ} (ι : Inst Γ (Θ [ σ ]₃)) {A : Tel (Δ ▹₃[ + ] Θ)} (ι' : Inst Γ (A [ σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧ ]₃)) → σ ▹ₛᵢ[ + ]⟦ Θ ++ₜ A , _extᵢ_ {Γ} {Θ [ σ ]₃} ι {A [ σ ▹▹₃[ + ]⟦ Θ , idₜₐ ⟧ ]₃} ι' ⟧ ≡ (((σ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧) ▹ₛᵢ[ + ]⟦ A , ι' ⟧))
  {-#REWRITE ▹ₛᵢ▹ₛᵢ #-}

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

-- VarInstTelExtTy
  vinst▹ : {Γ : Ctx} (Θ : Tel Γ) (A : Ty (Γ ▹₃[ + ] Θ)) → vinst {Γ} (Θ ▹ₜ A) ≡ ([ (Γ ▹₃[ + ] Θ) ▹[ + ] A ] vinst Θ [ WkTm (Γ ▹₃[ + ] Θ) + A ]₄ ▹ᵢ vztm {Γ ▹₃[ + ] Θ} {A})

-- VarInstTelExtTel                                                                                                                                                                                     --Should typecheck, doesnt, we don't know why..
  vinst++ : {Γ : Ctx} (Θ₁ : Tel Γ) (Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)) → vinst {Γ} (Θ₁ ++ₜ Θ₂) ≡ _extᵢ_ {(Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂} { Θ₁ [ WkTel + (Θ₁ ++ₜ Θ₂) ]₃ } (vinst {Γ} Θ₁ [ WkTel {Γ ▹₃[ + ] Θ₁} + Θ₂ ]₄) {{! Θ₂ [ (WkTel {Γ ▹₃[ + ] Θ₁} + Θ₂) ∘  (WkTel {((Γ ▹₃[ + ] Θ₁) ▹₃[ + ] Θ₂)} + (Θ₁ [ WkTel + (Θ₁ ++ₜ Θ₂) ]₃)) ]₃ !}} (vinst {Γ ▹₃[ + ] Θ₁} Θ₂) -- (vinst {Γ ▹₃[ + ] Θ₁} A)

-- _extᵢ_ : {Γ : Ctx} {Θ₁ : Tel Γ} (ι₁ : Inst Γ Θ₁) {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (ι₂ : Inst Γ (Θ₂ [ id Γ ▹ₛᵢ[ + ]⟦ Θ₁ , ι₁ ⟧ ]₃) ) → Inst Γ (Θ₁ ++ₜ Θ₂)
--  [_]_▹ᵢ_ : (Γ : Ctx) {Θ : Tel Γ} (ι : Inst Γ Θ) {T : Ty (Γ ▹₃[ + ] Θ)} → Tm (T [ id Γ ▹ₛᵢ[ + ]⟦ Θ , ι ⟧ ]₁) → Inst Γ (Θ ▹ₜ T)

foo₂ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {Θ₁ : Tel Γ} (Θ₁' : Tel Δ) (ta₁ : TelAd Γ Θ₁ (Θ₁' [ σ ]₃)) →
  vinst (Θ₁' [ σ ^ₛ + ]₃) [ ((id Γ ∘ WkTel + Θ₁) ▹ₛᵢ[ + ]⟦ Θ₁' [ σ ]₃ , teladapt (ta₁ [ WkTel + Θ₁ ]ₜₐ) (vinst Θ₁) ⟧) ^ₛ + ]₄ ≡ teladapt (ta₁ [ WkTel + Θ₁ ]ₜₐ) (vinst Θ₁)

foo₂ σ {Θ₁} Θ₁' ta₁ = SubHdᵢ (WkTel + Θ₁) (Θ₁' [ σ ]₃) (teladapt (ta₁ [ WkTel + Θ₁ ]ₜₐ) (vinst Θ₁))
{-#REWRITE foo₂ #-}


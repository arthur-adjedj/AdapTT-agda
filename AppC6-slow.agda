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
open import AppC6

{- Derivable operation -}
_w▹▹₃₊⟦_,_⟧ : {Γ Δ : Ctx}
              {σ : Sub Γ Δ}
              {τ : Sub Γ Δ}
              (μ : Trans Γ Δ σ τ)
              {Θ : Tel Γ}
              (Θ' : Tel Δ)
              (t : TelAd Γ Θ (Θ' [ σ ]₃)) →
              Trans (Γ ▹₃[ + ] Θ) (Δ ▹₃[ + ] Θ') (σ ▹▹₃[ + ]⟦ Θ' , t ⟧) (τ ▹▹₃[ + ]⟦ Θ' , (Θ' ⟦ μ ⟧₃) ∘ₜₐ t ⟧)
_w▹▹₃₊⟦_,_⟧ = {!!}

_w▹▹₃₋⟦_,_⟧ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ} (μ : Trans Γ Δ τ σ) {Θ : Tel (Γ ^ -)} (Θ' : Tel (Δ ^ -)) (t : TelAd (Γ ^ -) Θ (Θ' [ σ ^ₛ - ]₃)) → Trans (Γ ▹₃[ - ] Θ) (Δ ▹₃[ - ] Θ') (σ ▹▹₃[ - ]⟦ Θ' , t ⟧) (τ ▹▹₃[ - ]⟦ Θ' , (Θ' ⟦ μ ^ₘ - ⟧₃) ∘ₜₐ t ⟧)
_w▹▹₃₋⟦_,_⟧ = {!!}


-- provable results to help agda's computations

▸⟦⟧^d : {d d' d'' : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (Γ ▸[ d ]⟦ Θ , d' ⟧) ^ d'' ≡ (Γ ^ d'') ▸[ d × d'' ]⟦ Θ , d' × d'' ⟧
▸⟦⟧^d {d} {d'} {+} {Γ} {Θ} = refl
▸⟦⟧^d {d} {d'} { - } {Γ} {Θ} = refl
{-#REWRITE ▸⟦⟧^d #-}
WkTy^d : {d d' d'' : Dir} {Γ : Ctx} {Θ : Tel (Γ ^ d)} → (WkTy d {Γ} Θ d') ^ₛ d'' ≡ WkTy (d × d'') {Γ ^ d'' } Θ (d' × d'')
WkTy^d {d} {d'} {+} {Γ} {Θ} = refl
WkTy^d {d} {d'} { - } {Γ} {Θ} = refl
{-#REWRITE WkTy^d #-}
▸ₛ^d : {d d' d'' : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel (Δ ^ d)) (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) →
       (_▸ₛ[_]⟦_,_⟧ {d'} σ d Θ A) ^ₛ d'' ≡ ((σ ^ₛ d'') ▸ₛ[ d × d'' ]⟦ Θ , A ⟧)
▸ₛ^d {d} {d'} {+} {Γ} {Δ} σ Θ A = refl
▸ₛ^d {d} {d'} { - } {Γ} {Δ} σ Θ A = refl
{-#REWRITE ▸ₛ^d #-}

lemma₆ : (d : Dir) {Γ Δ : Ctx} {Θ : Tel (Δ ^ d)} {σ τ : Sub Γ Δ} (μ : Trans (Γ ^ d) (Δ ^ d) (σ ^ₛ d) (τ ^ₛ d))
         (ι : Inst (Δ ^ d) Θ) →
         (id Γ ▹▹₃[ d ]⟦ Θ [ τ ^ₛ d ]₃ , Θ ⟦ μ ⟧₃ ⟧) ∘ (id Γ ▹ₛᵢ[ d ]⟦ Θ [ σ ^ₛ d ]₃ , ι [ σ ^ₛ d ]₄ ⟧)  ≡
         id Γ ▹ₛᵢ[ d ]⟦ Θ [ τ ^ₛ d ]₃ , ι [ τ ^ₛ d ]₄ ⟧
lemma₆ d {Γ} {Δ} {Θ} {σ} {τ}  μ ι = ▹▹₃∘▹ d {Γ = Γ} {Δ = Γ} {σ = id Γ} {τ = id Γ}{A = Θ [ σ ^ₛ d ]₃} {B = Θ [ τ ^ₛ d ]₃} (ι [ σ ^ₛ d ]₄) (Θ ⟦ μ ⟧₃)
{-#REWRITE lemma₆ #-}

lemma₇ :  (Γ : Ctx) (Δ : Ctx) (σ : Sub Γ Δ) (τ : Sub Γ Δ)
          (μ : Trans Γ Δ σ τ) (Θ : Tel Δ) (ι : Inst Γ (Θ [ σ ]₃)) →
          ((Θ ⟦ μ ⟧₃) [ WkTel + (Θ [ σ ]₃) ]ₜₐ) [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]ₜₐ ≡ Θ ⟦ μ ⟧₃
lemma₇ Γ Δ σ τ μ Θ ι = [∘]ₜₐ (Θ ⟦ μ ⟧₃) (WkTel + (Θ [ σ ]₃)) (id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧)
{-#REWRITE lemma₇ #-}


postulate
-- SubTlTy
  SubTlTy : {Γ Δ : Ctx} {σ : Sub Γ Δ} {d d' : Dir} {Θ : Tel (Δ ^ d)} (A : Ty ((Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) ^ d')) → (WkTy d Θ d') ∘ (σ ▸ₛ[ d ]⟦ Θ , A ⟧) ≡ σ
  {-#REWRITE SubTlTy #-}

-- SubTyExtVarZ
  SubHdTy : {d : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel (Δ ^ d))
            (A : Ty (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃))) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) →
            (tyvz d {Δ} Θ) [ (σ ▸ₛ[ d ]⟦ Θ , A ⟧) ▹ₛᵢ[ d ]⟦ Θ [ (WkTy d {Δ} Θ +) ^ₛ d ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ d ]⟦ Θ [ σ ^ₛ d ]₃ , ι ⟧ ]₁
  {-#REWRITE SubHdTy #-}

-- SubEtaTy
  SubEtaTy : {Γ Δ : Ctx} {A : Tel (Δ ^ d)} (σ : Sub Γ (Δ ▸[ d ]⟦ A  , + ⟧)) →
             ((WkTy d A +) ∘ σ) ▸ₛ[ d ]⟦ A , tyvz d {Γ = Δ} A [ σ ▹▹₃[ d ]⟦ A [ WkTy + A d ]₃ , idₜₐ ⟧  ]₁ ⟧ ≡ σ
  {-#REWRITE SubEtaTy #-}

-- TransTlAd+
  whisker▸₊ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ + ] (Θ [ σ ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ + ] (Θ [ τ ]₃)) ^ d)}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ^ₛ d ]₁)) →
          whiskerLeft (WkTy + Θ d) (_▸ₘ₊⟦_⟧_ {Γ} {Δ} {σ} {τ} μ {Θ} d {A} {B} a) ≡ μ

-- TransTlAd-
  whisker▸₋ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel (Δ ^ -)}
          (d : Dir)
          {A : Ty ((Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃)) ^ d)}
          {B : Ty ((Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃)) ^ d)}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧) ^ₛ d ]₁))
          → whiskerLeft (WkTy - Θ d) (_▸ₘ₋⟦_⟧_ {Γ} {Δ} {σ} {τ} μ {Θ} d {A} {B} a) ≡ μ

SubEtaTy₊ : {Γ Δ : Ctx} {A : Tel Δ} (σ : Sub Γ (Δ ▸[ + ]⟦ A  , + ⟧)) →
             ((WkTy + A +) ∘ σ) ▸ₛ[ + ]⟦ A , tyvz + {Γ = Δ} A [ σ ▹▹₃[ + ]⟦ A [ WkTy + A + ]₃ , idₜₐ ⟧  ]₁ ⟧ ≡ σ
SubEtaTy₊ σ = SubEtaTy σ
{-#REWRITE SubEtaTy₊ #-}

foo1 : {Γ Δ : Ctx}
          {Θ : Tel Δ}
          {σ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
          {τ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
          (μ : Trans Γ (Δ ▸[ + ]⟦ Θ , + ⟧) σ τ) →
  vinst ((Θ [ WkTy + Θ + ]₃) [ τ ^ₛ + ]₃) [
    ((WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃) ^ₛ +) ▹ₛᵢ[ + ]⟦ Θ [ WkTy + Θ + ∘ τ ]₃ , teladapt ((Θ ⟦ whiskerLeft (WkTy + Θ +) μ ⟧₃) [ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃) ]ₜₐ) ((vinst (Θ [ WkTy + Θ + ∘ σ ]₃))) ⟧) ^ₛ + ]₄
   ≡ teladapt ((Θ ⟦ whiskerLeft (WkTy + Θ +) μ ⟧₃) [ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃) ]ₜₐ) (vinst (Θ [ WkTy + Θ + ∘ σ ]₃))
foo1 = {!!}
{-#REWRITE foo1 #-}

postulate
-- -- TransAdEta
--   TransAdEta : {Γ Δ : Ctx}
--           {Θ : Tel Δ}
--           {σ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
--           {τ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
--           (μ : Trans Γ (Δ ▸[ + ]⟦ Θ , + ⟧) σ τ) →
--           μ ≡ _▸ₘ₊⟦_⟧_ {Γ} {Δ} {(WkTy + Θ +) ∘ σ} {(WkTy + Θ +) ∘ τ} (whiskerLeft (WkTy + Θ +) μ) {Θ} + {(tyvz + Θ) [ σ ▹▹₃[ + ]⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ]₁} {(tyvz + Θ) [ τ ▹▹₃[ + ]⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ]₁} ((tyvz + Θ) ⟦ μ w▹▹₃₊⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ⟧)

-- -- TransAdEta-
--   TransAdEta- : {Γ Δ : Ctx}
--           {Θ : Tel (Δ ^ -)}
--           {σ : Sub Γ (Δ ▸[ - ]⟦ Θ , + ⟧)}
--           {τ : Sub Γ (Δ ▸[ - ]⟦ Θ , + ⟧)}
--           (μ : Trans Γ (Δ ▸[ - ]⟦ Θ , + ⟧) σ τ) →
--           μ ≡ _▸ₘ₋⟦_⟧_ {Γ} {Δ} {(WkTy - Θ +) ∘ σ} {(WkTy - Θ +) ∘ τ} (whiskerLeft (WkTy - Θ +) μ) {Θ} + {(tyvz - Θ) [ τ ▹▹₃[ - ]⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ]₁} {(tyvz - Θ) [ σ ▹▹₃[ - ]⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ]₁} ((tyvz - Θ) ⟦ μ w▹▹₃₋⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ⟧)

-- TransHdAd
  -- TransHdAd : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
  --             (μ : Trans Γ Δ σ τ)
  --             {Θ : Tel Δ}
  --             {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))}
  --             {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
  --             (a : Ad (Γ ▹₃[ + ] (Θ [ σ ]₃)) A (B [ id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁))
  --             (ι : Inst Γ (Θ [ σ ]₃)) →
  --             (tyvz + {Δ} Θ ⟦ (_▸ₘ₊_ {+} {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ▹ₘᵢ₊⟦ Θ [ WkTy + Θ + ]₃ , ι ⟧ ⟧) ≡ (a [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]ₐ)

  TransHdAd : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))}
          {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ]₁))
          (ι : Inst Γ (Θ [ σ ]₃)) →
          {!!}

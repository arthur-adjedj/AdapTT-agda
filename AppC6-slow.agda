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

-- provable results to help agda's computations

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
-- SubTyExtVarZ
  SubHdTy : {d : Dir} {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel (Δ ^ d))
            (A : Ty (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃))) (ι : Inst (Γ ^ d) (Θ [ σ ^ₛ d ]₃)) →
            (tyvz d {Δ} Θ) [ (σ ▸ₛ[ d ]⟦ Θ , A ⟧) ▹ₛᵢ[ d ]⟦ Θ [ (WkTy d {Δ} Θ +) ^ₛ d ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ d ]⟦ Θ [ σ ^ₛ d ]₃ , ι ⟧ ]₁
  {-#REWRITE SubHdTy #-}

  {-#REWRITE SubEtaTy #-}

-- TransTlAd++
  whisker▸₊₊ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))}
          {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
          (a : Ad _ A (B [ id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧ ]₁)) →
          whiskerLeft (WkTy + Θ +) (_▸ₘ₊₊_ {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ≡ μ

-- TransTlAd+-
  whisker▸₊₋ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          {A : Ty ((Γ ▹₃[ + ] (Θ [ σ ]₃)) ^ -)}
          {B : Ty ((Γ ▹₃[ + ] (Θ [ τ ]₃)) ^ -)}
          (a : Ad _ (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ^ₛ - ]₁) A) →
          whiskerLeft (WkTy + Θ -) (_▸ₘ₊₋_ {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ≡ μ

-- TransTlAd-+
  whisker▸₋₊ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel (Δ ^ -)}
          {B : Ty (Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃))}
          {A : Ty (Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃))}
          (a : Ad _ (A [ id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧ ]₁) B)
          → whiskerLeft (WkTy - Θ +) (_▸ₘ₋₊_ {Γ} {Δ} {σ} {τ} μ {Θ} {B} {A} a) ≡ μ

-- TransTlAd--
  whisker▸₋ : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel (Δ ^ -)}
          {B : Ty ((Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃)) ^ -)}
          {A : Ty ((Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃)) ^ -)}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧) ^ₛ - ]₁))
          → whiskerLeft (WkTy - Θ -) (_▸ₘ₋₋_ {Γ} {Δ} {σ} {τ} μ {Θ} {B} {A} a) ≡ μ

SubEtaTy₊ : {Γ Δ : Ctx} {A : Tel Δ} (σ : Sub Γ (Δ ▸[ + ]⟦ A  , + ⟧)) →
             ((WkTy + A +) ∘ σ) ▸ₛ[ + ]⟦ A , tyvz + {Γ = Δ} A [ σ ▹▹₃[ + ]⟦ A [ WkTy + A + ]₃ , idₜₐ ⟧  ]₁ ⟧ ≡ σ
SubEtaTy₊ σ = SubEtaTy σ
{-#REWRITE SubEtaTy₊ #-}

SubHdTy+ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Θ : Tel Δ)
            (A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))) (ι : Inst Γ (Θ [ σ ]₃)) →
            (tyvz + {Δ} Θ) [ (σ ▸ₛ[ + ]⟦ Θ , A ⟧) ▹ₛᵢ[ + ]⟦ Θ [ WkTy + {Δ} Θ + ]₃ , ι ⟧ ]₁ ≡ A [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]₁
SubHdTy+ σ Θ A = SubHdTy {d = +} σ Θ A
{-#REWRITE SubHdTy+ #-}


SubEtaTy₋ : {Γ Δ : Ctx} {Θ : Tel (Δ ^ -)} {σ : Sub Γ (Δ ▸[ - ]⟦ Θ , + ⟧)} →
     ((WkTy - Θ + ∘ σ) ▸ₛ[ - ]⟦ Θ , tyvz - {Γ = Δ} Θ [ σ ▹▹₃[ - ]⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ]₁ ⟧) ≡ σ
SubEtaTy₋ {σ = σ} = SubEtaTy { - } σ
{-#REWRITE SubEtaTy₋ #-}
-- {- Derivable operation -}

{-#REWRITE ⟦⟧[]₃ #-}
_w▹▹₃₊⟦_,_⟧ : {Γ Δ : Ctx}
              {σ : Sub Γ Δ}
              {τ : Sub Γ Δ}
              (μ : Trans Γ Δ σ τ)
              {Θ : Tel Γ}
              (Θ' : Tel Δ)
              (t : TelAd Γ Θ (Θ' [ σ ]₃)) →
              Trans (Γ ▹₃[ + ] Θ) (Δ ▹₃[ + ] Θ') (σ ▹▹₃[ + ]⟦ Θ' , t ⟧) (τ ▹▹₃[ + ]⟦ Θ' , (Θ' ⟦ μ ⟧₃) ∘ₜₐ t ⟧)
_w▹▹₃₊⟦_,_⟧ {Γ} {Δ} {σ} {τ} μ {Θ} Θ' t = (whiskerRight μ (WkTel + Θ)) ▹ₘᵢ₊⟦ Θ' , teladapt (t [ WkTel {Γ = Γ} + Θ ]ₜₐ) (vinst Θ) ⟧

-- {-#REWRITE whiskerRight^- #-}
-- _w▹▹₃₋⟦_,_⟧ : {Γ Δ : Ctx}
--               {σ : Sub Γ Δ}
--               {τ : Sub Γ Δ}
--               (μ : Trans Γ Δ τ σ)
--               {Θ : Tel (Γ ^ -)}
--               (Θ' : Tel (Δ ^ -))
--               (t : TelAd (Γ ^ -) Θ (Θ' [ σ ^ₛ - ]₃)) →
--               Trans (Γ ▹₃[ - ] Θ) (Δ ▹₃[ - ] Θ') (τ ▹▹₃[ - ]⟦ Θ' , (Θ' ⟦ μ ^ₘ - ⟧₃) ∘ₜₐ t ⟧) (σ ▹▹₃[ - ]⟦ Θ' , t ⟧)
-- _w▹▹₃₋⟦_,_⟧ {Γ} {Δ} {σ} {τ} μ {Θ} Θ' t = (whiskerRight μ (WkTel - Θ)) ▹ₘᵢ₋⟦ Θ' , teladapt (t [ WkTel {Γ = Γ ^ - } + Θ ]ₜₐ) (vinst Θ) ⟧

-- foo2 : {Γ Δ : Ctx}
--        {Θ : Tel Δ}
--        {σ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
--        {τ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
--        (μ : Trans Γ (Δ ▸[ + ]⟦ Θ , + ⟧) σ τ) →
--   teladapt ((((Θ [ WkTy + Θ + ]₃) ⟦ μ ⟧₃) ∘ₜₐ idₜₐ) [ WkTel + ((Θ [ WkTy + Θ + ]₃) [ σ ]₃) ]ₜₐ) (vinst ((Θ [ WkTy + Θ + ]₃) [ σ ]₃)) ≡
--   vinst ((Θ [ WkTy + Θ + ]₃) [ τ ^ₛ + ]₃) [ ((id Γ ∘ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃)) ▹ₛᵢ[ + ]⟦
--  Θ [ WkTy + Θ + ∘ τ ]₃ , teladapt ((Θ ⟦ whiskerLeft (WkTy + Θ +) μ ⟧₃) [ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃) ]ₜₐ) (vinst (Θ [ WkTy + Θ + ∘ σ ]₃)) ⟧) ^ₛ + ]₄
-- foo2 {Γ} {Δ} {Θ} {σ} {τ} μ = sym (SubHdᵢ (id Γ ∘ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃)) ((Θ [ WkTy + Θ + ]₃) [ τ ^ₛ + ]₃) (teladapt ((Θ ⟦ whiskerLeft (WkTy + Θ +) μ ⟧₃) [ WkTel + (Θ [ WkTy + Θ + ∘ σ ]₃) ]ₜₐ) (vinst (Θ [ WkTy + Θ + ∘ σ ]₃))))
-- {-#REWRITE foo2 #-}

sym∘whiskerRight : {Γ Δ Ξ Φ : Ctx} (σ : Sub Γ Δ) (σ' : Sub Δ Ξ) (τ τ' : Sub Ξ Φ) (μ : Trans Ξ Φ τ τ') → whiskerRight (whiskerRight μ  σ') σ ≡ whiskerRight μ (σ' ∘ σ)
sym∘whiskerRight σ σ' τ τ' μ = sym (∘whiskerRight σ σ' τ τ' μ)
{-#REWRITE sym∘whiskerRight #-}

foo3 :

postulate
-- TransAdEta
  -- TransAdEta : {Γ Δ : Ctx}
  --         {Θ : Tel Δ}
  --         {σ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
  --         {τ : Sub Γ (Δ ▸[ + ]⟦ Θ , + ⟧)}
  --         (μ : Trans Γ (Δ ▸[ + ]⟦ Θ , + ⟧) σ τ) →
  --         μ ≡ _▸ₘ₊₊_ {Γ} {Δ} {(WkTy + Θ +) ∘ σ} {(WkTy + Θ +) ∘ τ} (whiskerLeft (WkTy + Θ +) μ) {Θ} {(tyvz + Θ) [ σ ▹▹₃[ + ]⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ]₁} {(tyvz + Θ) [ τ ▹▹₃[ + ]⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ]₁} ((tyvz + Θ) ⟦ μ w▹▹₃₊⟦ Θ [ WkTy + Θ + ]₃ , idₜₐ ⟧ ⟧)

-- TransAdEta-
  -- TransAdEta- : {Γ Δ : Ctx}
  --         {Θ : Tel (Δ ^ -)}
  --         {σ : Sub Γ (Δ ▸[ - ]⟦ Θ , + ⟧)}
  --         {τ : Sub Γ (Δ ▸[ - ]⟦ Θ , + ⟧)}
  --         (μ : Trans Γ (Δ ▸[ - ]⟦ Θ , + ⟧) σ τ) →
  --         _▸ₘ₋⟦_⟧_ {Γ} {Δ} {(WkTy - Θ +) ∘ σ} {(WkTy - Θ +) ∘ τ} (whiskerLeft (WkTy - Θ +) μ) {Θ} + {(tyvz - {Δ} Θ) [ τ ▹▹₃[ - ]⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ]₁} {(tyvz - {Δ} Θ) [ σ ▹▹₃[ - ]⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧ ]₁} ((tyvz - Θ) ⟦ {!μ w▹▹₃₋⟦ Θ [ WkTy + Θ - ]₃ , idₜₐ ⟧!} ⟧) ≡ {!!}

-- TransHdAd+
  TransHdAd : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
          (μ : Trans Γ Δ σ τ)
          {Θ : Tel Δ}
          {A : Ty (Γ ▹₃[ + ] (Θ [ σ ]₃))}
          {B : Ty (Γ ▹₃[ + ] (Θ [ τ ]₃))}
          (a : Ad _ A (B [ (id Γ ▹▹₃[ + ]⟦ _ , Θ ⟦ μ ⟧₃ ⟧) ]₁))
          (ι : Inst Γ (Θ [ σ ]₃)) →
          (tyvz + Θ ⟦ (_▸ₘ₊₊_  {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ▹ₘᵢ₊⟦ Θ [ WkTy + Θ + ]₃ , ι ⟧ ⟧) ≡ ((a [ id Γ ▹ₛᵢ[ + ]⟦ Θ [ σ ]₃ , ι ⟧ ]ₐ))


-- -- TransHdAd-
--   TransHdAd- : {Γ Δ : Ctx} {σ : Sub Γ Δ} {τ : Sub Γ Δ}
--           (μ : Trans Γ Δ σ τ)
--           {Θ : Tel (Δ ^ -)}
--           {A : Ty (Γ ▹₃[ - ] (Θ [ τ ^ₛ - ]₃))}
--           {B : Ty (Γ ▹₃[ - ] (Θ [ σ ^ₛ - ]₃))}
--           (a : Ad _ A (B [ id Γ ▹▹₃[ - ]⟦ _ , Θ ⟦ μ ^ₘ - ⟧₃ ⟧ ]₁))
--           (ι : Inst (Γ ^ -) (Θ [ τ ^ₛ - ]₃)) →
--           (tyvz - Θ ⟦ (_▸ₘ₋₊_  {Γ} {Δ} {σ} {τ} μ {Θ} {A} {B} a) ▹ₘᵢ₋⟦ Θ [ WkTy + Θ - ]₃ , ι ⟧ ⟧) ≡ (a [ id Γ ▹ₛᵢ[ - ]⟦ Θ [ τ ^ₛ - ]₃ , ι ⟧ ]ₐ)

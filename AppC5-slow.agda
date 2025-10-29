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

postulate
  ▹▹₃++ₜₐ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {Θ₁ : Tel Γ} (Θ₁' : Tel Δ) (ta₁ : TelAd Γ Θ₁ (Θ₁' [ σ ]₃)) {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} (Θ₂' : Tel (Δ ▹₃[ + ] Θ₁')) (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ σ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧ ]₃)) →
    σ ▹▹₃[ + ]⟦ Θ₁' ++ₜ Θ₂' , ta₁ ++ₜₐ⟦ Θ₂' [ σ ▹▹₃[ + ]⟦ Θ₁' , idₜₐ ⟧ ]₃ , ta₂ ⟧ ⟧ ≡ (σ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧ ▹▹₃[ + ]⟦ Θ₂' , ta₂ ⟧)

foo₁ :    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)}
    (Θ₂' : Tel (Γ ▹₃[ + ] Θ₁'))
    (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃)) →
  (((WkTel + Θ₁ ∘ WkTel + (Θ₂' [ (id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧) ^ₛ + ]₃)) ▹ₛᵢ[ + ]⟦ Θ₁' , teladapt (ta₁ [ WkTel + Θ₁ ]ₜₐ) (vinst Θ₁) [ WkTel + (Θ₂' [ (id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧) ^ₛ + ]₃) ^ₛ + ]₄ ⟧) ∘ ((id (Γ ▹₃[ + ] Θ₁) ∘ WkTel + Θ₂) ▹ₛᵢ[ + ]⟦ Θ₂' [ id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧ ]₃ , teladapt (ta₂ [ WkTel + Θ₂ ]ₜₐ) (vinst Θ₂) ⟧)) ▹ₛᵢ[ + ]⟦ Θ₂' , vinst (Θ₂' [ (id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧) ^ₛ + ]₃) [ ((id (Γ ▹₃[ + ] Θ₁) ∘ WkTel + Θ₂) ▹ₛᵢ[ + ]⟦ Θ₂' [ id Γ ▹▹₃[ + ]⟦ Θ₁' , ta₁ ⟧ ]₃ , teladapt (ta₂ [ WkTel + Θ₂ ]ₜₐ) (vinst Θ₂) ⟧) ^ₛ + ]₄ ⟧ ≡ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧ ⟧
-- We verified the proof on pen and paper, but could not fill it in
foo₁ ta₁ Θ₂' ta₂ = {!!}
{-#REWRITE foo₁ #-}

postulate
--TelAdExtTelAdExtAd
  _++ₜₐ⟦▹ₐ⟧ :
    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)}
    (Θ₂' : Tel (Γ ▹₃[ + ] Θ₁'))
    (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃))
    {A : Ty (Γ ▹₃[ + ] (Θ₁ ++ₜ Θ₂))} {A' : Ty (Γ ▹₃[ + ] (Θ₁' ++ₜ Θ₂'))}
    (a :  Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧ ⟧ ]₁)) →
      ( ta₁ ++ₜₐ⟦ Θ₂' ▹ₜ A' , _▹ₜₐ_ {Γ ▹₃[ + ] Θ₁} {Θ₂} {Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃} ta₂ {A} {A' [ (id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧) ▹▹₃[ + ]⟦ Θ₂' , idₜₐ ⟧ ]₁} a ⟧) ≡
      _▹ₜₐ_ {Γ = Γ} {Θ = Θ₁ ++ₜ Θ₂} {Θ' = Θ₁' ++ₜ Θ₂'} (ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧) {A = A} {A' = A'} a

-- TelAdExtTelAdExtTelAd
  _++ₜₐ⟦++ₜₐ⟧ :
    {Γ : Ctx}
    {Θ₁ Θ₁' : Tel Γ} (ta₁ : TelAd Γ Θ₁ Θ₁')
    {Θ₂ : Tel (Γ ▹₃[ + ] Θ₁)} {Θ₂' : Tel (Γ ▹₃[ + ] Θ₁')}
    (ta₂ :  TelAd (Γ ▹₃[ + ] Θ₁) Θ₂ (Θ₂' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧ ]₃))
    {Θ₃ : Tel (Γ ▹₃[ + ] (Θ₁ ++ₜ Θ₂))} {Θ₃' : Tel (Γ ▹₃[ + ] (Θ₁' ++ₜ Θ₂'))}
    (ta₃ :  TelAd _ Θ₃ (Θ₃' [ id Γ ▹▹₃[ + ]⟦ _ , ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧ ⟧ ]₃))
    → ta₁ ++ₜₐ⟦ Θ₂' ++ₜ Θ₃' , ta₂ ++ₜₐ⟦  Θ₃' [ (id Γ ▹▹₃[ + ]⟦ _ , ta₁ ⟧) ▹▹₃[ + ]⟦ Θ₂' , idₜₐ ⟧ ]₃ , ta₃  ⟧  ⟧ ≡  (ta₁ ++ₜₐ⟦ Θ₂' , ta₂ ⟧) ++ₜₐ⟦ Θ₃' , ta₃ ⟧

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
  teladapt ((ta [ WkTel + Θ ]ₜₐ)
                [ ((σ ∘ WkTel + (Θ [ σ ]₃)) ^ₛ +) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₜₐ)
           (vinst Θ [ ((σ ∘ WkTel + (Θ [ σ ]₃)) ^ₛ +) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]₄) ≡
  (vinst (Θ' [ σ ]₃) [
         ((id Δ ∘ WkTel + (Θ [ σ ]₃))
              ▹ₛᵢ[ + ]⟦ Θ' [ σ ]₃ ,
                        teladapt ((ta [ σ ]ₜₐ) [ WkTel + (Θ [ σ ]₃) ]ₜₐ)
                                               (vinst (Θ [ σ ]₃)) ⟧) ]₄)
foo {Θ = Θ} {Θ' = Θ'} ta σ = sym (SubHdᵢ (WkTel + (Θ [ σ ]₃)) (Θ' [ σ ]₃) (teladapt (ta [ σ ∘ WkTel + (Θ [ σ ]₃) ]ₜₐ) (vinst (Θ [ σ ]₃))))
{-#REWRITE foo #-}

postulate
-- SubTelAdOnExtAd
  ▹ₐ[] : {Γ Δ : Ctx} {Θ Θ' : Tel Γ} (ta : TelAd Γ Θ Θ') {A : Ty (Γ ▹₃[ + ] Θ)} {A' : Ty (Γ ▹₃[ + ] Θ')} (a : Ad _ A (A' [ id Γ ▹▹₃[ + ]⟦ Θ' , ta ⟧ ]₁)) (σ : Sub Δ Γ)
    → (_▹ₜₐ_ {Θ = Θ} {Θ' = Θ'} ta {A = A} {A' = A'} a)[ σ ]ₜₐ ≡ _▹ₜₐ_ {Θ = Θ [ σ ]₃} {Θ' = Θ' [ σ ]₃} (ta [ σ ]ₜₐ) (a [ (σ ∘ WkTel + (Θ [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₐ)

-- SubTelAdOnExtTelAd
  ++ₜₐ[] : {Γ Δ : Ctx} {Θ Θ' : Tel Γ} (ta₁ : TelAd Γ Θ Θ') {A : Tel (Γ ▹₃[ + ] Θ)} {A' : Tel (Γ ▹₃[ + ] Θ')} (ta₂ : TelAd _ A (A' [ id Γ ▹▹₃[ + ]⟦ Θ' , ta₁ ⟧ ]₃)) (σ : Sub Δ Γ)
    → (ta₁ ++ₜₐ⟦ A' , ta₂ ⟧ )[ σ ]ₜₐ ≡ (ta₁ [ σ ]ₜₐ) ++ₜₐ⟦ A' [ (σ ∘ WkTel + (Θ' [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ' , vinst (Θ' [ σ ]₃) ⟧ ]₃ , ta₂ [ (σ ∘ WkTel + (Θ [ σ ]₃)) ▹ₛᵢ[ + ]⟦ Θ , vinst (Θ [ σ ]₃) ⟧ ]ₜₐ ⟧


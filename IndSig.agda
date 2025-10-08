{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Dir
open import Std
open import Pi
open import AdapTT2

_▹ₛ₃[_]_ : (σ : Sub Γ Δ) (d : Dir) (Θ : Tel (Δ ^ d)) → Sub (Γ ▹₃[ d ] (Θ [ σ ^ₛ d ]₃)) (Δ ▹₃[ d ] Θ)
_▹ₛ₃[_]_ {Γ = Γ} {Δ = Δ} σ d Θ = σ ▹▹₃[ d ]⟦ Θ , idₜₐ ⟧


{- Appendix C.8 : Inductive types -}
record RecDesc (Γₚ : Ctx) (Θargs Θᵢ : Tel Γₚ) : Set where
  constructor mkRecDesc
  field
    recArity : Tel ((Γₚ ▹₃[ + ] Θargs) ^ -)
    recInst  : Inst ((Γₚ ▹₃[ + ] Θargs) ▹₃[ - ] recArity) (Θᵢ [ WkTel + Θargs ∘ WkTel - recArity ]₃)

RecTel : (Γₚ : Ctx) (Θargs Θᵢ : Tel Γₚ) → Set
RecTel Γₚ Θargs Θᵢ = List (RecDesc Γₚ Θargs Θᵢ)

record ConDesc (Γₚ : Ctx) (Θᵢ : Tel Γₚ) : Set where
  constructor mkConDesc
  field
    Θargs : Tel Γₚ
    Θrec : RecTel Γₚ Θargs Θᵢ
    ιᵢ : Inst (Γₚ ▹₃[ + ] Θargs) (Θᵢ [ WkTel + Θargs ]₃)

IndDesc : (Γₚ : Ctx) (Θᵢ : Tel Γₚ) → Set
IndDesc Γₚ Θᵢ = List (ConDesc Γₚ Θᵢ)

recData :
  {Γₚ  : Ctx} {Θᵢ Θargs : Tel Γₚ}
  → RecDesc Γₚ Θargs Θᵢ → Ty ((Γₚ ▸[ + ]⟦ Θᵢ , + ⟧) ▹₃[ + ] (Θargs [ WkTy + Θᵢ + ]₃))

recData {Γₚ = Γₚ}{Θᵢ = Θᵢ} {Θargs = Θargs} (mkRecDesc Θarit indInst) =
  TelToPi (Θarit [ (WkTy - {Γ = (Γₚ ^ -)} Θᵢ -) ▹ₛ₃[ - ] Θargs ]₃)
  ((tyvz + Θᵢ) [
    (WkTel + (Θargs [ WkTy + Θᵢ + ]₃) ∘
     WkTel - (Θarit [ WkTy - {Γₚ ^ - } Θᵢ - ▹ₛ₃[ - ] Θargs ]₃)
    ) ▹ₛᵢ[ + ]⟦ Θᵢ [ WkTy + Θᵢ + ^ₛ + ]₃ , indInst [ 
        ((WkTy + Θᵢ + ∘
        (WkTel + (Θargs [ WkTy + Θᵢ + ]₃) ^ₛ +) ∘
        (WkTel - (Θarit [ WkTy - {Γₚ ^ - } Θᵢ - ▹ₛ₃[ - ] Θargs ]₃)))
        ▹ₛᵢ[ + ]⟦ Θargs , vinst (Θargs [ WkTy + Θᵢ + ]₃) [ WkTel - (Θarit [ WkTy - {Γₚ ^ - } Θᵢ - ▹ₛ₃[ - ] Θargs ]₃) ]₄ ⟧)
        ▹ₛᵢ[ - ]⟦ Θarit , vinst (Θarit [ (WkTy - {Γₚ ^ - } Θᵢ - ▹ₛ₃[ - ] Θargs)  ]₃)  ⟧
        ]₄ 
      ⟧

   ]₁)

recDatas :
  {Γₚ  : Ctx} {Θᵢ Θargs : Tel Γₚ}
  → RecTel Γₚ Θargs Θᵢ
  → Tel ((Γₚ ▸[ + ]⟦ Θᵢ , + ⟧) ▹₃[ + ] (Θargs [ WkTy + Θᵢ + ]₃))
recDatas {Θargs = Θargs} [] = ⋄ₜ
recDatas {Θᵢ = Θᵢ} {Θargs = Θargs} (recDesc ∷ l) =
  (recDatas {Θargs = Θargs} l) ▹ₜ ((recData recDesc) [ WkTel + (recDatas l) ]₁)

conData :{Γₚ  : Ctx} {Θᵢ : Tel Γₚ}
  → ConDesc Γₚ Θᵢ → Tel (Γₚ ▸[ + ]⟦ Θᵢ , + ⟧)
conData {Θᵢ = Θᵢ} (mkConDesc Θargs Θrec _) = (Θargs [ WkTy + Θᵢ + ]₃) ++ₜ recDatas Θrec

postulate
  ind :
    {Γₚ  : Ctx} {Θᵢ : Tel Γₚ} (I : IndDesc Γₚ Θᵢ)
    → Ty (Γₚ ▹₃[ + ] Θᵢ)

assocIssueFix : 
  {Γₚ  : Ctx} {Θᵢ : Tel Γₚ} (I : Ty (Γₚ ▹₃[ + ] Θᵢ))
  (Θargs : Tel Γₚ) → 
  ( WkTy + Θᵢ + 
    ∘ ((id Γₚ ▸ₛ[ + ]⟦ Θᵢ , I ⟧) ) 
    ∘ (WkTel + Θargs) 
  )
  ≡ 
  WkTel + Θargs
  
assocIssueFix {Γₚ} {Θᵢ} I Θargs = sym (∘assoc (WkTy + Θᵢ +) (id Γₚ ▸ₛ[ + ]⟦ Θᵢ , I ⟧) (WkTel + Θargs))

{-#REWRITE assocIssueFix #-}

postulate
 constr :
   {Γₚ  : Ctx} {Θᵢ : Tel Γₚ} (I : IndDesc Γₚ Θᵢ)
   (C : ConDesc Γₚ Θᵢ) → C ∈ I →
   Tm {Γₚ ▹₃[ + ] ((conData C) [ id _ ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧ ]₃)}
     ((ind I) [ WkTel + (conData C [ id _ ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧ ]₃)
        ▹ₛᵢ[ + ]⟦ Θᵢ ,
         (ConDesc.ιᵢ C) [
          WkTel {(Γₚ ▹₃[ + ] C .ConDesc.Θargs)} + (recDatas (C .ConDesc.Θrec) [
           ((id _ ▸ₛ[ + ]⟦ Θᵢ , ind I ⟧) ∘
           WkTel + (C .ConDesc.Θargs)) ▹ₛᵢ[ + ]⟦ C .ConDesc.Θargs [ WkTy + Θᵢ + ]₃ , vinst (C .ConDesc.Θargs) ⟧
          ]₃)
         ]₄ ⟧  ]₁
     )


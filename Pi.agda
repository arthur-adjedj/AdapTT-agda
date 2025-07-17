{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Dir
open import Std
open import AdapTT2

variable
  Γ Δ Φ Ξ : Ctx
  σ τ : Sub Γ Δ

-- provable lemmas for needed for computations
▹ₛᵢ⋄ₜ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (d : Dir) → (ι : Inst (Γ ^ d) _) → σ ▹ₛᵢ[ d ]⟦ ⋄ₜ , ι ⟧ ≡ σ
▹ₛᵢ⋄ₜ σ d ι = cong (λ ι → σ ▹ₛᵢ[ d ]⟦ ⋄ₜ , ι ⟧) (⋄ₜ⇒⋄ᵢ ι)
{-#REWRITE ▹ₛᵢ⋄ₜ #-}

▹ₛᵢ₊⋄ₜ : {Γ Δ : Ctx} (σ : Sub Γ Δ) → (ι : Inst Γ _) → σ ▹ₛᵢ[ + ]⟦ ⋄ₜ , ι ⟧ ≡ σ
▹ₛᵢ₊⋄ₜ σ ι = ▹ₛᵢ⋄ₜ σ + ι
{-#REWRITE ▹ₛᵢ₊⋄ₜ #-}

vztm[id▹ₛ] : {Γ : Ctx} {A : Ty Γ} {t : Tm (A [ WkTm Γ + A ]₁)}→ vztm [ id (Γ ▹[ + ] A) ▹ₛ[ + , A [ WkTm Γ + A ]₁ ] t ]₂ ≡ t
vztm[id▹ₛ] {Γ} {A = A} {t = t} = SubHd (id (Γ ▹[ + ] A)) (A [ WkTm Γ + A ]₁ ) t
{-#REWRITE vztm[id▹ₛ] #-}

rm : {Γ : Ctx} {d : Dir} {A : Ty (Γ ^ d)} (t : Tm A) → Sub Γ (Γ ▹[ d ] A)
rm {Γ} {d = d} {A = A} t = id Γ ▹ₛ[ d , A ] t

_↑ : {Γ Δ : Ctx} {A : Ty Δ} → (σ : Sub Γ Δ) → Sub (Γ ▹[ + ] (A [ σ ]₁)) (Δ ▹[ + ] A)
_↑ {Γ} {Δ} {A = A} σ = (σ ∘ WkTm Γ + (A [ σ ]₁)) ▹ₛ[ + , A ] vztm
_↑₋ : {Γ Δ : Ctx} {A : Ty (Δ ^ -)} → (σ : Sub Γ Δ) → Sub (Γ ▹[ - ] (A [ σ ^ₛ - ]₁)) (Δ ▹[ - ] A)
_↑₋ {Γ} {Δ} {A = A} σ = (σ ∘ WkTm Γ - (A [ σ ^ₛ - ]₁)) ▹ₛ[ - , A ] vztm


{- Appendix C.7 : Rules for Π -}
postulate
  _Π_ : (A : Ty (Γ ^ -)) → Ty (Γ ▹[ - ] A) → Ty Γ
  lam : {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)} → Tm B → Tm (A Π B)
  app : {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)} → Tm (A Π B) → (u : Tm A) → Tm (B [ rm u ]₁)

  Π[]₁ :
    (A : Ty (Γ ^ -)) (B : Ty (Γ ▹[ - ] A)) →
    (A Π B) [ σ ]₁ ≡ (A [ σ ^ₛ - ]₁) Π (B [ σ ↑₋ ]₁)
  {-#REWRITE Π[]₁ #-}

  lam[]₂ :
      {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)} (t : Tm B)
      (σ : Sub Δ Γ)
      → (lam t) [ σ ]₂ ≡ lam (t [ σ ↑₋ ]₂)

  app[]₂ :
      {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)}
      (f : Tm (A Π B)) (x : Tm A)
      (σ : Sub Δ Γ)
      → (app f x) [ σ ]₂ ≡
        {! app {A = A [ σ ^ₛ - ]₁} {B = B [ _↑₋ {A = A } σ ]₁} (f [ σ ]₂) (x [ σ ^ₛ - ]₂)  !}

  β :
    {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)} (b : Tm B) (x : Tm A) →
    app (lam b) x ≡ b [ rm x ]₂

  η :
    {Γ : Ctx}
    {A : Ty (Γ ^ -)} {B : Ty (Γ ▹[ - ] A)} (f : Tm (A Π B))→
    f ≡ lam (app (f [ WkTm Γ - A ]₂) vztm)

postulate
  TelToPi :
    {Γ : Ctx} (Θ : Tel (Γ ^ -)) (A : Ty (Γ ▹₃[ - ] Θ)) →
    Ty Γ

  TelToPi⋄ₜ :
    {Γ : Ctx} (A : Ty Γ) →
    TelToPi ⋄ₜ A ≡ A
  {-# REWRITE TelToPi⋄ₜ #-}
  TelToPi▹ₜ :
    {Γ : Ctx} (Θ : Tel (Γ ^ -)) (A : Ty ((Γ ^ -) ▹₃[ + ] Θ)) (B : Ty (Γ ▹₃[ - ] (Θ ▹ₜ A)))→
    TelToPi {Γ = Γ} (Θ ▹ₜ A) B ≡ TelToPi Θ (A Π B)
  {-# REWRITE TelToPi▹ₜ #-}
  TelToPi[] :
    {Γ : Ctx} (Θ : Tel (Γ ^ -)) (A : Ty (Γ ▹₃[ - ] Θ))
    (σ : Sub Δ Γ) →
    (TelToPi Θ A) [ σ ]₁ ≡ TelToPi (Θ [ σ ^ₛ - ]₃) (A [ σ ▹▹₃[ - ]⟦ Θ , idₜₐ ⟧ ]₁)
  {-# REWRITE TelToPi[] #-}

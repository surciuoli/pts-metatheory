open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Subset.Propositional
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Binary.Construct.Union

open import Stoughton.Var

module PTSs2.Metatheory {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  private
    _≟_ = IsVar._≟_ isVar
    
  open import PTSs isVar 𝒜 ℛ renaming (genProd to genProdₛ; validCxt to validCxtₛ) hiding (genLam)
  open import PTSs2 isVar 𝒜 ℛ 
  open import PTSs.Metatheory isVar 𝒜 ℛ
    renaming (freshAsg to freshAsgₛ; syntacticValidity to syntacticValidityₛ; thinning to thinningₛ; closureAlpha to closureAlphaₛ;
      cut to cutₛ; unaryRen to unaryRenₛ)
    using ()
    
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_
  open import Context.Properties 𝒞 isVar  
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar

  ptsSoundCxt : ∀ {Γ} → Γ okₛ → Γ okₛ₂
  ptsSound : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → Γ ⊢ₛ₂ M ∶ A

  ptsSoundCxt ⊢nil = ⊢nil
  ptsSoundCxt (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (ptsSoundCxt Γok) x∉Γ (ptsSound Γ⊢A:s)

  ptsSound (⊢sort Γok As₁s₂) = ⊢sort (ptsSoundCxt Γok) As₁s₂
  ptsSound (⊢var Γok x,A∈Γ) = ⊢var (ptsSoundCxt Γok) x,A∈Γ
  ptsSound {Γ} Γ⊢Π[x:A]B:s₃@(⊢prod {x} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (ptsSound Γ⊢A:s₁) y∉fvB-x (ptsSound Γ,y:A⊢B[x=y]:s₂)
  ptsSound {Γ} (⊢abs {x} {y} {_} {s₂} {s₃} {A} {B} {M} ℛs₁s₂s₃ z∉fvM-x z∉fvB-y Γ⊢A:s₁ Γ,z:A⊢M[x=z]:B[y=z] Γ,z:A⊢B[y=z]:s₂) =
    ⊢abs z∉fvM-x z∉fvB-y (ptsSound Γ,z:A⊢M[x=z]:B[y=z]) (⊢prod ℛs₁s₂s₃ (ptsSound Γ⊢A:s₁) z∉fvB-y (ptsSound Γ,z:A⊢B[y=z]:s₂))
  ptsSound (⊢app Γ⊢M:Π[x:A]B Γ⊢N:A) = ⊢app (ptsSound Γ⊢M:Π[x:A]B) (ptsSound Γ⊢N:A)
  ptsSound (⊢conv Γ⊢M:A A=B Γ⊢B:s) = ⊢conv (ptsSound Γ⊢M:A) A=B (ptsSound Γ⊢B:s)

  ptsCompleteCxt : ∀ {Γ} → Γ okₛ₂ → Γ okₛ
  ptsComplete : ∀ {Γ M A} → Γ ⊢ₛ₂ M ∶ A → Γ ⊢ₛ M ∶ A

  ptsCompleteCxt ⊢nil = ⊢nil
  ptsCompleteCxt (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (ptsCompleteCxt Γok) x∉Γ (ptsComplete Γ⊢A:s)

  ptsComplete (⊢sort Γok As₁s₂) = ⊢sort (ptsCompleteCxt Γok) As₁s₂
  ptsComplete (⊢var Γok x,A∈Γ) = ⊢var (ptsCompleteCxt Γok) x,A∈Γ
  ptsComplete {Γ} (⊢prod {x} {y} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (ptsComplete Γ⊢A:s₁) y∉fvB-x (ptsComplete Γ,y:A⊢B[x=y]:s₂)
  ptsComplete {Γ} h@(⊢abs {x} {y} {z} {s} {A} {B} {M} z∉fvM-x z∉fvB-y Γ,z:A⊢M[x=z]:B[y=z] Γ⊢Π[y:A]B:s)
    with genProdₛ (ptsComplete Γ⊢Π[y:A]B:s)
  ... | s₁ , s₂ , s₃ , y' , ℛs₁s₂s₃ , Γ⊢A:s₁ , y'∉fvB-y , Γ,y':A⊢B[y=y']:s₂ , _ =
    ⊢abs ℛs₁s₂s₃ z∉fvM-x z∉fvB-y Γ⊢A:s₁ Γ‚z:A⊢ₛM[x=z]:B[y=z] Γ‚z:A⊢B[y=z]:s₂
    where
    Γ‚z:A⊢ₛM[x=z]:B[y=z] : Γ ‚ z ∶ A ⊢ₛ M [ x := v z ] ∶ B [ y := v z ] 
    Γ‚z:A⊢ₛM[x=z]:B[y=z] = ptsComplete Γ,z:A⊢M[x=z]:B[y=z]
    z∉domΓ : z ∉ dom Γ
    z∉domΓ with validCxt Γ,z:A⊢M[x=z]:B[y=z]
    ... | ⊢cons _ g _ = g
    Γ‚z:A⊢B[y=y'][y'=z]:s₂ : Γ ‚ z ∶ A ⊢ₛ B [ y := v y' ] [ y' := v z ] ∶ c s₂
    Γ‚z:A⊢B[y=y'][y'=z]:s₂ = unaryRenₛ z∉domΓ Γ,y':A⊢B[y=y']:s₂
    Γ‚z:A⊢B[y=z]:s₂ : Γ ‚ z ∶ A ⊢ₛ B [ y := v z ] ∶ c s₂
    Γ‚z:A⊢B[y=z]:s₂ = subst (λ C → Γ ‚ z ∶ A ⊢ₛ C ∶ c s₂) (sym (composRenUpd {y} {y'} {B} y'∉fvB-y)) Γ‚z:A⊢B[y=y'][y'=z]:s₂       
      
  ptsComplete {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛ₂M:Π[x:A]B Γ⊢ₛ₂N:A) = ⊢app (ptsComplete Γ⊢ₛ₂M:Π[x:A]B) (ptsComplete Γ⊢ₛ₂N:A)
  ptsComplete (⊢conv Γ⊢M:A A=B Γ⊢B:s) =
    ⊢conv (ptsComplete Γ⊢M:A) A=B (ptsComplete Γ⊢B:s)
  
  eqJudgCxt : ∀ {Γ} → Γ okₛ ↔ Γ okₛ₂
  eqJudgAsg : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A ↔ Γ ⊢ₛ₂ M ∶ A 
 
  eqJudgCxt = ptsSoundCxt , ptsCompleteCxt
  eqJudgAsg = ptsSound , ptsComplete 

  module _ where

    thinning : ∀ {Γ Δ M A} →  Γ ⊆ Δ → Δ okₛ₂ → Γ ⊢ₛ₂ M ∶ A → Δ ⊢ₛ₂ M ∶ A
    thinning Γ⊆Δ Δok 𝒟 = ptsSound (thinningₛ Γ⊆Δ (ptsCompleteCxt Δok) (ptsComplete 𝒟))

    closureAlpha : ∀ {Γ Δ M N A B} → Γ ≈α Δ → M ∼α N → A ∼α B → Γ ⊢ₛ₂ M ∶ A → Δ ⊢ₛ₂ N ∶ B
    closureAlpha Γ∼Δ M∼N A∼B 𝒟 = ptsSound (closureAlphaₛ Γ∼Δ M∼N A∼B (ptsComplete 𝒟))

    -- infix 2 _∶_⇀_
    -- _∶_⇀ₛ₂_ : Sub → Cxt → Cxt → Set
    -- σ ∶ Γ ⇀ₛ₂ Δ = ∀ {x A} → (x , A) ∈ Γ → Δ ⊢ₛ₂ σ x ∶ A ∙ σ
      
    -- closureSub : ∀ {σ Γ Δ M A} → Γ ⊢ₛ₂ M ∶ A → σ ∶ Γ ⇀ Δ → Δ okₛ₂ → Δ ⊢ₛ₂ M ∙ σ ∶ A ∙ σ
    -- closureSub 𝒟 𝓈 ℰ = ptsSound (closureSubInf 𝓈 (ptsCompleteCxt ℰ) (ptsComplete 𝒟))

    cut :  ∀ {Γ M N A B x} → Γ ‚ x ∶ A ⊢ₛ₂ M ∶ B → Γ ⊢ₛ₂ N ∶ A → Γ ⊢ₛ₂ M [ x := N ] ∶ B [ x := N ]
    cut 𝒟 ℰ = ptsSound (cutₛ (ptsComplete 𝒟) (ptsComplete ℰ))

    unaryRen : ∀ {Γ x y A M B} → y ∉ dom Γ → Γ ‚ x ∶ A ⊢ₛ₂ M ∶ B → Γ ‚ y ∶ A ⊢ₛ₂ M [ x := v y ] ∶ B [ x := v y ]
    unaryRen y∉domΓ 𝒟 = ptsSound (unaryRenₛ y∉domΓ (ptsComplete 𝒟))
    
    syntacticValidity : ∀ {Γ M A} → Γ ⊢ₛ₂ M ∶ A → ∃ λ s → A ≡ c s ⊎ Γ ⊢ₛ₂ A ∶ c s
    syntacticValidity 𝒟 with syntacticValidityₛ (ptsComplete 𝒟)
    ... | s , ℰ = s , Data.Sum.map (λ x → x) ptsSound ℰ

    freshAsg : ∀ {Γ M A w} → w ∉ dom Γ → Γ ⊢ₛ₂ M ∶ A → w # M · A
    freshAsg w∉domΓ 𝒟 = freshAsgₛ w∉domΓ (ptsComplete 𝒟)

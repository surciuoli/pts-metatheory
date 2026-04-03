open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Subset.Propositional
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Binary.Construct.Union

open import Stoughton.Var

module PTSs.Metatheory {𝒞 𝒱 : Set} (isVar : Enum 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  private
    _≟_ = Enum._≟_ isVar
    
  open import PTS isVar 𝒜 ℛ renaming (genProd to genProdInf; freshAsg to freshAsgInf) hiding (validCxt; genLam)
  open import PTSs isVar 𝒜 ℛ 
  open import PTS.SyntacticValidity isVar 𝒜 ℛ renaming (syntacticValidity to syntacticValidityInf)
  open import PTS.ClosureSub isVar 𝒜 ℛ using (_∶_⇀_)
    renaming (closureSub to closureSubInf; subUnary to subUnarInf; unaryRen to unaryRenInf; cut to cutInf) public
    
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar  
  open import Context 𝒱 Λ _≟_
  open import Context.Properties 𝒞 isVar  
  open import Stoughton.Chi (Enum.encode isVar) (Enum.decode isVar) (Enum.inverse isVar)  
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar

  ptsSoundCxt : ∀ {Γ} → Γ ok → Γ okₛ
  ptsSound : ∀ {Γ M A} → Γ ⊢ M ∶ A → Γ ⊢ₛ M ∶ A

  ptsSoundCxt ⊢nil = ⊢nil
  ptsSoundCxt (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (ptsSoundCxt Γok) x∉Γ (ptsSound Γ⊢A:s)

  ptsSound (⊢sort Γok As₁s₂) = ⊢sort (ptsSoundCxt Γok) As₁s₂
  ptsSound (⊢var Γok x,A∈Γ) = ⊢var (ptsSoundCxt Γok) x,A∈Γ
  ptsSound {Γ} Γ⊢Π[x:A]B:s₃@(⊢prod {x} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ ∀y→Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (ptsSound Γ⊢A:s₁) y∉fvB-x (ptsSound (∀y→Γ,y:A⊢B[x=y]:s₂ y y∉domΓ))
    where
    y : 𝒱
    y = X' (dom Γ)
    y∉domΓ : y ∉ dom Γ
    y∉domΓ = Xpfresh (dom Γ)
    y∉fvB-x : y ∉ fv B - x
    y∉fvB-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsgInf y∉domΓ Γ⊢Π[x:A]B:s₃))
  ptsSound {Γ} Γ⊢λ[x:A]M:Π[y:A]B@(⊢abs {x} {y} {s₁} {s₂} {s₃} {A} {B} {M} ℛs₁s₂s₃ Γ⊢A:s₁ ∀z→Γ,z:A⊢M[x=z]:B[y=z] ∀z→Γ,z:A⊢B[y=z]:s₂) =
    ⊢abs
        ℛs₁s₂s₃
        z∉fvM-x
        z∉fvB-y
        (ptsSound Γ⊢A:s₁)
        (ptsSound (∀z→Γ,z:A⊢M[x=z]:B[y=z] z z∉domΓ))
        (ptsSound (∀z→Γ,z:A⊢B[y=z]:s₂ z z∉domΓ))
    where
    z : 𝒱
    z = X' (dom Γ)
    z∉domΓ : z ∉ dom Γ
    z∉domΓ = Xpfresh (dom Γ)
    z∉fvM-x : z ∉ fv M - x
    z∉fvM-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsgInf z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
    z∉fvB-y : z ∉ fv B - y
    z∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉ys {xs = fv (λ[ x ∶ A ] M)} (freshAsgInf z∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))
  ptsSound (⊢app Γ⊢M:Π[x:A]B Γ⊢N:A _) = ⊢app (ptsSound Γ⊢M:Π[x:A]B) (ptsSound Γ⊢N:A)
  ptsSound (⊢conv Γ⊢M:A A=B Γ⊢B:s) = ⊢conv (ptsSound Γ⊢M:A) A=B (ptsSound Γ⊢B:s)

  ptsCompleteCxt : ∀ {Γ} → Γ okₛ → Γ ok
  ptsComplete : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → Γ ⊢ M ∶ A

  ptsCompleteCxt ⊢nil = ⊢nil
  ptsCompleteCxt (⊢cons Γok x∉Γ Γ⊢A:s) = ⊢cons (ptsCompleteCxt Γok) x∉Γ (ptsComplete Γ⊢A:s)

  ptsComplete (⊢sort Γok As₁s₂) = ⊢sort (ptsCompleteCxt Γok) As₁s₂
  ptsComplete (⊢var Γok x,A∈Γ) = ⊢var (ptsCompleteCxt Γok) x,A∈Γ
  ptsComplete {Γ} (⊢prod {x} {y} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ y∉fvB-x Γ,y:A⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ (ptsComplete Γ⊢A:s₁) goal
    where
    goal : ∀ y' → y' ∉ dom Γ → Γ ‚ y' ∶ A ⊢ B [ x := v y' ] ∶ c s₂
    goal y' y'∉domΓ = Γ‚y':A⊢B[x=y']:s₂
      where
      Γ‚y:A⊢B[x=y]:s₂ : Γ ‚ y ∶ A ⊢ B [ x := v y ] ∶ c s₂
      Γ‚y:A⊢B[x=y]:s₂ = ptsComplete Γ,y:A⊢B[x=y]:s₂
      Γ‚y':A⊢B[x=y][y=y']:s₂ : Γ ‚ y' ∶ A ⊢ B [ x := v y ] [ y := v y' ] ∶ c s₂
      Γ‚y':A⊢B[x=y][y=y']:s₂ = unaryRenInf y'∉domΓ Γ‚y:A⊢B[x=y]:s₂ 
      Γ‚y':A⊢B[x=y']:s₂ : Γ ‚ y' ∶ A ⊢ B [ x := v y' ] ∶ c s₂
      Γ‚y':A⊢B[x=y']:s₂ = subst (λ C → Γ ‚ y' ∶ A ⊢ C ∶ c s₂) (sym (composRenUpd {x} {y} {B} y∉fvB-x)) Γ‚y':A⊢B[x=y][y=y']:s₂   
  ptsComplete {Γ} h@(⊢abs {x} {y} {z} {s₁} {s₂} {s₃} {A} {B} {M} ℛs₁s₂s₃ z∉fvM-x z∉fvB-y Γ⊢A:s₁ Γ,z:A⊢M[x=z]:B[y=z] Γ,z:A⊢B[y=z]:s₂) =
    ⊢abs ℛs₁s₂s₃ (ptsComplete Γ⊢A:s₁) goal2 goal
    where    
    goal2 : ∀ z' → z' ∉ dom Γ → Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
    goal2 z' z'∉domΓ = Γ‚z':A⊢M[x=z']:B[y=z']
      where
      Γ‚z:A⊢M[x=z]:B[y=z] : Γ ‚ z ∶ A ⊢ M [ x := v z ] ∶ B [ y := v z ] 
      Γ‚z:A⊢M[x=z]:B[y=z] = ptsComplete Γ,z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z ] [ z := v z' ] ∶ B [ y := v z ] [ z := v z' ] 
      Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z'] = unaryRenInf z'∉domΓ Γ‚z:A⊢M[x=z]:B[y=z]
      Γ‚z':A⊢M[x=z']:B[y=z'] : Γ ‚ z' ∶ A ⊢ M [ x := v z' ] ∶ B [ y := v z' ] 
      Γ‚z':A⊢M[x=z']:B[y=z'] =
        subst₂
          (λ N C → Γ ‚ z' ∶ A ⊢ N ∶ C)
          (sym (composRenUpd {x} {z} {M} z∉fvM-x))
          (sym (composRenUpd {y} {z} {B} z∉fvB-y))
          Γ‚z':A⊢M[x=z][z=z']:B[y=z][z=z']
    goal : ∀ z' → z' ∉ dom Γ → Γ ‚ z' ∶ A ⊢ B [ y := v z' ] ∶ c s₂
    goal z' z'∉domΓ = Γ‚z':A⊢B[y=z']:s₂
      where
      Γ‚z:A⊢B[y=z]:s₂ : Γ ‚ z ∶ A ⊢ B [ y := v z ] ∶ c s₂
      Γ‚z:A⊢B[y=z]:s₂ = ptsComplete Γ,z:A⊢B[y=z]:s₂
      Γ‚z':A⊢B[y=z][z=z']:s₂ : Γ ‚ z' ∶ A ⊢ B [ y := v z ] [ z := v z' ] ∶ c s₂
      Γ‚z':A⊢B[y=z][z=z']:s₂ = unaryRenInf z'∉domΓ Γ‚z:A⊢B[y=z]:s₂ 
      Γ‚z':A⊢B[y=z']:s₂ : Γ ‚ z' ∶ A ⊢ B [ y := v z' ] ∶ c s₂
      Γ‚z':A⊢B[y=z']:s₂ = subst (λ C → Γ ‚ z' ∶ A ⊢ C ∶ c s₂) (sym (composRenUpd {y} {z} {B} z∉fvB-y)) Γ‚z':A⊢B[y=z][z=z']:s₂          
      
  ptsComplete {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛM:Π[x:A]B Γ⊢ₛN:A) with syntacticValidityInf Γ⊢M:Π[x:A]B
    where
    Γ⊢M:Π[x:A]B : Γ ⊢ M ∶ Π[ x ∶ A ] B 
    Γ⊢M:Π[x:A]B = ptsComplete Γ⊢ₛM:Π[x:A]B    
  ptsComplete _ | _ , inj₁ ()
  ptsComplete {Γ} (⊢app {x} {M} {N} {A} {B} Γ⊢ₛM:Π[x:A]B Γ⊢ₛN:A) | s , inj₂ Γ⊢Π[x:A]B:s =
    ⊢app Γ⊢M:Π[x:A]B Γ⊢N:A (proj₂ Γ⊢B[x=N]:s)
    where
    Γ⊢M:Π[x:A]B : Γ ⊢ M ∶ Π[ x ∶ A ] B 
    Γ⊢M:Π[x:A]B = ptsComplete Γ⊢ₛM:Π[x:A]B        
    Γ⊢N:A : Γ ⊢ N ∶ A
    Γ⊢N:A = ptsComplete Γ⊢ₛN:A
    z : 𝒱
    z = X' (dom Γ)
    z∉Γ : z ∉ dom Γ
    z∉Γ = Xpfresh (dom Γ)
    Γ,z:A⊢B[x=z]:s : ∃ λ s → Γ ‚ z ∶ A ⊢ B [ x := v z ] ∶ c s
    Γ,z:A⊢B[x=z]:s with genProdInf Γ⊢Π[x:A]B:s
    ... | _ , s , _ , _ , _ , h , _ = s , h z z∉Γ 
    z∉fvB-x : z ∉ fv B - x
    z∉fvB-x = c∉xs++ys→c∉ys (c∉xs++ys→c∉ys {xs = fv M} (freshAsgInf z∉Γ Γ⊢M:Π[x:A]B))
    B[x=z][z=N]=B[x=N] : B [ x := v z ] [ z := N ] ≡ B [ x := N ]
    B[x=z][z=N]=B[x=N] = sym (composRenUpd {x} {z} {B} {N} z∉fvB-x)
    Γ⊢B[x=N]:s : ∃ λ s → Γ ⊢ B [ x := N ] ∶ c s
    Γ⊢B[x=N]:s = s' , subst (λ X → Γ ⊢ X ∶ c s') B[x=z][z=N]=B[x=N] (cutInf (proj₂ Γ,z:A⊢B[x=z]:s) Γ⊢N:A)
      where
      s' : 𝒞
      s' = proj₁ Γ,z:A⊢B[x=z]:s
  ptsComplete (⊢conv Γ⊢M:A A=B Γ⊢B:s) =
    ⊢conv (ptsComplete Γ⊢M:A) A=B (ptsComplete Γ⊢B:s)
  
  eqJudgCxt : ∀ {Γ} → Γ ok ↔ Γ okₛ
  eqJudgAsg : ∀ {Γ M A} → Γ ⊢ M ∶ A ↔ Γ ⊢ₛ M ∶ A 
 
  eqJudgCxt = ptsSoundCxt , ptsCompleteCxt
  eqJudgAsg = ptsSound , ptsComplete 

  module _ where
  
    open import PTS.Thinning isVar 𝒜 ℛ renaming (thinning to thinningInf)
    open import PTS.ClosureAlpha isVar 𝒜 ℛ renaming (closureAlpha to closureAlphaInf) public

    thinning : ∀ {Γ Δ M A} →  Γ ⊆ Δ → Δ okₛ → Γ ⊢ₛ M ∶ A → Δ ⊢ₛ M ∶ A
    thinning Γ⊆Δ Δok 𝒟 = ptsSound (thinningInf Γ⊆Δ (ptsCompleteCxt Δok) (ptsComplete 𝒟))

    closureAlpha : ∀ {Γ Δ M N A B} → Γ ≈α Δ → M ∼α N → A ∼α B → Γ ⊢ₛ M ∶ A → Δ ⊢ₛ N ∶ B
    closureAlpha Γ∼Δ M∼N A∼B 𝒟 = ptsSound (closureAlphaInf Γ∼Δ M∼N A∼B (ptsComplete 𝒟))

    cut :  ∀ {Γ M N A B x} → Γ ‚ x ∶ A ⊢ₛ M ∶ B → Γ ⊢ₛ N ∶ A → Γ ⊢ₛ M [ x := N ] ∶ B [ x := N ]
    cut 𝒟 ℰ = ptsSound (cutInf (ptsComplete 𝒟) (ptsComplete ℰ))

    unaryRen : ∀ {Γ x y A M B} → y ∉ dom Γ → Γ ‚ x ∶ A ⊢ₛ M ∶ B → Γ ‚ y ∶ A ⊢ₛ M [ x := v y ] ∶ B [ x := v y ]
    unaryRen y∉domΓ 𝒟 = ptsSound (unaryRenInf y∉domΓ (ptsComplete 𝒟))
    
    syntacticValidity : ∀ {Γ M A} → Γ ⊢ₛ M ∶ A → ∃ λ s → A ≡ c s ⊎ Γ ⊢ₛ A ∶ c s
    syntacticValidity 𝒟 with syntacticValidityInf (ptsComplete 𝒟)
    ... | s , ℰ = s , Data.Sum.map (λ x → x) ptsSound ℰ

    freshAsg : ∀ {Γ M A w} → w ∉ dom Γ → Γ ⊢ₛ M ∶ A → w # M · A
    freshAsg w∉domΓ 𝒟 = freshAsgInf w∉domΓ (ptsComplete 𝒟)

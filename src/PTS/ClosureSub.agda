open import Data.Empty
open import Data.List 
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq 
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.Nat hiding (_≟_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
import Relation.Binary.Reasoning.Preorder as PreR

open import Stoughton.Var
 
module PTS.ClosureSub {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where
  
  open import PTS isVar 𝒜 ℛ
  open import PTS.Thinning isVar 𝒜 ℛ
  open import PTS.ClosureAlpha isVar 𝒜 ℛ
  open import PTS.SyntacticValidity isVar 𝒜 ℛ
  
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)
  open import Stoughton.Substitution 𝒞 isVar
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Syntax 𝒞 𝒱 _≟_ hiding (length)
  open import Context 𝒱 Λ _≟_ 
  open import BetaConversion 𝒞 isVar
  
  open PreR ≈-preorder∼

  infix 2 _∶_⇀_
  _∶_⇀_ : Sub → Cxt → Cxt → Set
  σ ∶ Γ ⇀ Δ = ∀ {x A} → (x , A) ∈ Γ → Δ ⊢ σ x ∶ A ∙ σ

  subRen : ∀ {Γ Δ x y s A σ} → x ∉ dom Γ → y ∉ dom Δ → Γ ⊢ A ∶ c s → Δ ⊢ A ∙ σ ∶ c s → σ ∶ Γ ⇀ Δ → σ ‚ x := v y ∶ (Γ ‚ x ∶ A) ⇀ Δ ‚ y ∶ A ∙ σ
  subRen {Γ} {Δ} {x} {y} {s} {A} {σ} x∉domΓ y∉domΔ Γ⊢A:s Δ⊢Aσ:s h = lemma2
    where
    Δok : Δ ok
    Δok = validCxtAsg Δ⊢Aσ:s
    Δ,y:Aσok : Δ ‚ y ∶ A ∙ σ ok
    Δ,y:Aσok = ⊢cons Δok y∉domΔ Δ⊢Aσ:s
    lemma2 : ∀ {z B} → (z , B) ∈ (Γ ‚ x ∶ A) → Δ ‚ y ∶ A ∙ σ ⊢ (σ ‚ x := v y) z ∶ B ∙ σ ‚ x := v y
    lemma2 {z} {B} _ with x ≟ z
    lemma2 {.x} {.A} (here refl) | yes refl = subst (_⊢_∶_ (Δ ‚ y ∶ A ∙ σ) (v y)) Aσ=Aσ<+x,y Δ,y:Aσ⊢y:Aσ
      where      
      x#A : x # A 
      x#A = c∉xs++ys→c∉xs (freshAsg x∉domΓ Γ⊢A:s)
      Aσ=Aσ<+x,y : A ∙ σ ≡ A ∙ σ ‚ x := v y
      Aσ=Aσ<+x,y = sym (updFresh {x} {A} x#A)
      Δ,y:Aσ⊢y:Aσ : Δ ‚ y ∶ A ∙ σ ⊢ v y ∶ A ∙ σ
      Δ,y:Aσ⊢y:Aσ = ⊢var Δ,y:Aσok (here refl)
    lemma2 {.x} {B} (there x,B∈Γ) | yes refl = ⊥-elim (x∉domΓ (inCxtInDom x,B∈Γ))
    lemma2 {.x} {.A} (here refl) | no x≢x = ⊥-elim (x≢x refl)
    lemma2 {z} {B} (there z,B∈Γ) | no _ = subst (_⊢_∶_ (Δ ‚ y ∶ A ∙ σ) (σ z)) Bσ=Bσ<+x,y Δ,y:Aσ⊢σz:Bσ
      where
      Δ⊆Δ,y:A : Δ ⊆ (Δ ‚ y ∶ A ∙ σ)
      Δ⊆Δ,y:A = xs⊆x∷xs Δ (y , A ∙ σ)
      Γok : Γ ok
      Γok = validCxtAsg Γ⊢A:s
      x#B : x # B
      x#B = freshCxt Γok x∉domΓ z,B∈Γ
      Bσ=Bσ<+x,y : B ∙ σ ≡ B ∙ σ ‚ x := v y
      Bσ=Bσ<+x,y = sym (updFresh {x} {B} x#B)
      Δ⊢σz:Bσ : Δ ⊢ σ z ∶ B ∙ σ
      Δ⊢σz:Bσ = h z,B∈Γ
      Δ,y:Aσ⊢σz:Bσ : Δ ‚ y ∶ A ∙ σ ⊢ σ z ∶ B ∙ σ
      Δ,y:Aσ⊢σz:Bσ = thinning Δ⊆Δ,y:A Δ,y:Aσok Δ⊢σz:Bσ      

  closureSub : ∀ {Γ Δ M A σ} → σ ∶ Γ ⇀ Δ → Δ ok → Γ ⊢ M ∶ A → Δ ⊢ M ∙ σ ∶ A ∙ σ
  closureSub _ Δok (⊢sort _ As₁s₂) = ⊢sort Δok As₁s₂
  closureSub sub _ (⊢var _ x,A∈Γ) = sub x,A∈Γ
  closureSub {Γ} {Δ} {_} {_} {σ} sub Δok Γ⊢λ[x:A]M:Π[y:A]B@(⊢abs {x} {y} {s₁} {s₂} {s₃} {A} {B} {M} Rs₁s₂s₃ Γ⊢A:s₁ h₀ h) =
    ⊢abs Rs₁s₂s₃ Δ⊢Aσ:s₁ goal₀ goal
    where
    x' y' : 𝒱    
    x' = X (σ , fv M - x)
    y' = X (σ , fv B - y)
    x'#σ⇂fvM-x : x' #⇂ (σ , fv M - x)
    x'#σ⇂fvM-x = Xfresh σ (fv M - x)
    y'#σ⇂fvB-y : y' #⇂ (σ , fv B - y)
    y'#σ⇂fvB-y = Xfresh σ (fv B - y)    
    Δ⊢Aσ:s₁ : Δ ⊢ A ∙ σ ∶ c s₁
    Δ⊢Aσ:s₁ = closureSub sub Δok Γ⊢A:s₁
    goal₀ : ∀ z → z ∉ dom Δ → Δ ‚ z ∶ A ∙ σ ⊢ (B ∙ σ ‚ y := v y') [ y' := v z ] ∶ c s₂
    goal₀ z z∉domΔ =
      closureAlpha ∼ρs lemma2 ∼ρ ih
      where
      z' : 𝒱
      z' = X' (dom Γ)
      z'∉domΓ : z' ∉ dom Γ
      z'∉domΓ = Xpfresh (dom Γ)
      sub' : σ ‚ z' := v z ∶ (Γ ‚ z' ∶ A) ⇀ Δ ‚ z ∶ A ∙ σ 
      sub' = subRen z'∉domΓ z∉domΔ Γ⊢A:s₁ Δ⊢Aσ:s₁ sub
      Δ,z:Aσok : Δ ‚ z ∶ A ∙ σ ok
      Δ,z:Aσok = ⊢cons Δok z∉domΔ Δ⊢Aσ:s₁
      ih : Δ  ‚ z ∶ A ∙ σ ⊢ B [ y := v z' ] ∙ σ ‚ z' := v z ∶ c s₂
      ih = closureSub sub' Δ,z:Aσok (h₀ z' z'∉domΓ)
      lemma2 : B [ y := v z' ] ∙ σ ‚ z' := v z ∼α (B ∙ σ ‚ y := v y') [ y' := v z ]
      lemma2 = 
        begin
        B [ y := v z' ] ∙ σ ‚ z' := v z
        ≈⟨ sym (composRenUpd {y} {z'} {B} {v z} z'∉fvB-y) ⟩
        B ∙ σ ‚ y := v z
        ∼⟨ ∼σ (composRenUnary {y} {y'} {σ} {B} y'#σ⇂fvB-y) ⟩
        (B ∙ σ ‚ y := v y') [ y' := v z ]
        ∎
        where
        z'∉fvB-y : z' ∉ fv B - y
        z'∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉ys {xs = fv A ++ (fv M - x)} (freshAsg z'∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))      
    goal : ∀ z → z ∉ dom Δ → Δ ‚ z ∶ A ∙ σ ⊢ (M ∙ σ ‚ x := v x') [ x' := v z ] ∶ (B ∙ σ ‚ y := v y') [ y' := v z ]
    goal z z∉domΔ =
      closureAlpha ∼ρs lemma1 lemma2 ih
      where
      z' : 𝒱
      z' = X' (dom Γ)
      z'∉domΓ : z' ∉ dom Γ
      z'∉domΓ = Xpfresh (dom Γ)
      sub' : σ ‚ z' := v z ∶ (Γ ‚ z' ∶ A) ⇀ Δ ‚ z ∶ A ∙ σ 
      sub' = subRen z'∉domΓ z∉domΔ Γ⊢A:s₁ Δ⊢Aσ:s₁ sub
      Δ,z:Aσok : Δ ‚ z ∶ A ∙ σ ok
      Δ,z:Aσok = ⊢cons Δok z∉domΔ Δ⊢Aσ:s₁
      ih : Δ  ‚ z ∶ A ∙ σ ⊢ M [ x := v z' ] ∙ σ ‚ z' := v z ∶ B [ y := v z' ] ∙ σ ‚ z' := v z
      ih = closureSub sub' Δ,z:Aσok (h z' z'∉domΓ)
      lemma1 : M [ x := v z' ] ∙ σ ‚ z' := v z ∼α (M ∙ σ ‚ x := v x') [ x' := v z ]
      lemma1 = 
        begin
        M [ x := v z' ] ∙ σ ‚ z' := v z
        ≈⟨ sym (composRenUpd {x} {z'} {M} {v z} z'∉fvM-x) ⟩
        M ∙ σ ‚ x := v z
        ∼⟨ ∼σ (composRenUnary {x} {x'} {σ} {M} x'#σ⇂fvM-x) ⟩
        (M ∙ σ ‚ x := v x') [ x' := v z ]
        ∎
        where
        z'∉fvM-x : z' ∉ fv M - x
        z'∉fvM-x = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsg z'∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))              
      lemma2 : B [ y := v z' ] ∙ σ ‚ z' := v z ∼α (B ∙ σ ‚ y := v y') [ y' := v z ]
      lemma2 = 
        begin
        B [ y := v z' ] ∙ σ ‚ z' := v z
        ≈⟨ sym (composRenUpd {y} {z'} {B} {v z} z'∉fvB-y) ⟩
        B ∙ σ ‚ y := v z
        ∼⟨ ∼σ (composRenUnary {y} {y'} {σ} {B} y'#σ⇂fvB-y) ⟩
        (B ∙ σ ‚ y := v y') [ y' := v z ]
        ∎
        where
        z'∉fvB-y : z' ∉ fv B - y
        z'∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉ys {xs = fv A ++ (fv M - x)} (freshAsg z'∉domΓ Γ⊢λ[x:A]M:Π[y:A]B))                
  closureSub {Γ} {Δ} {_} {_} {σ} sub Δok (⊢app {x} {s} {M} {N} {A} {B} Γ⊢M:ΠxAB Γ⊢N:A Γ⊢[N/x]B:s) =
    closureAlpha ∼ρs ∼ρ (∼σ lemma) Δ⊢σMσN:[σN/x']x'/x,σB 
    where
    x' : 𝒱
    x' = X (σ , fv B - x)
    x'#σ⇂fvB-x : x' #⇂ (σ , fv B - x)
    x'#σ⇂fvB-x = Xfresh σ (fv B - x)
    Δ⊢σM:Π[x:Aσ]x'/x,σB : Δ ⊢ M ∙ σ ∶ Π[ x' ∶ A ∙ σ ] (B ∙ σ ‚ x := v x') 
    Δ⊢σM:Π[x:Aσ]x'/x,σB = closureSub sub Δok Γ⊢M:ΠxAB
    Δ⊢σN:σA : Δ ⊢ N ∙ σ ∶ A ∙ σ 
    Δ⊢σN:σA = closureSub sub Δok Γ⊢N:A
    Δ⊢σ[N/x]B:s : Δ ⊢ B [ x := N ] ∙ σ ∶ c s
    Δ⊢σ[N/x]B:s = closureSub sub Δok Γ⊢[N/x]B:s
    lemma : B [ x := N ] ∙ σ ∼α (B ∙ σ ‚ x := v x') [ x' := N ∙ σ ] 
    lemma = 
      begin 
      B [ x := N ] ∙ σ
      ≈⟨ sym (subDistribUpd {B} {N} {σ} {x}) ⟩
      B ∙ σ ‚ x := (N ∙ σ)
      ∼⟨ ∼σ (composRenUnary {x} {x'} {σ} {B} {N ∙ σ} x'#σ⇂fvB-x) ⟩
      (B ∙ σ ‚ x := v x') [ x' := N ∙ σ ] 
      ∎ 
    Δ⊢σMσN:[σN/x']x'/x,σB : Δ ⊢ (M · N) ∙ σ ∶ (B ∙ σ ‚ x := v x') [ x' := N ∙ σ ]
    Δ⊢σMσN:[σN/x']x'/x,σB = ⊢app Δ⊢σM:Π[x:Aσ]x'/x,σB Δ⊢σN:σA (closAlphaAsg ∼ρs lemma Δ⊢σ[N/x]B:s)
  closureSub sub Δok (⊢conv Γ⊢M:A A=B Γ⊢B:s) = ⊢conv (closureSub sub Δok Γ⊢M:A) (compatConvSub A=B) (closureSub sub Δok Γ⊢B:s)
  closureSub {Γ} {Δ} {_} {_} {σ} sub Δok Γ⊢Π[y:A]B:𝒰@(⊢prod {y} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ h) = ⊢prod Rs₁s₂s₃ Δ⊢Aσ:s₁ goal
    where
    y' : 𝒱
    y' = X (σ , fv B - y)
    y'#σ⇂fvB-y : y' #⇂ (σ , fv B - y)
    y'#σ⇂fvB-y = Xfresh σ (fv B - y)  
    Δ⊢Aσ:s₁ : Δ ⊢ A ∙ σ ∶ c s₁
    Δ⊢Aσ:s₁ = closureSub sub Δok Γ⊢A:s₁
    goal : ∀ z → z ∉ dom Δ → Δ ‚ z ∶ A ∙ σ ⊢ (B ∙ σ ‚ y := v y') [ y' := v z ] ∶ c s₂
    goal z z∉domΔ = closAlphaAsg ∼ρs lemma ih
      where
      z' : 𝒱
      z' = X' (dom Γ)
      z'∉domΓ : z' ∉ dom Γ
      z'∉domΓ = Xpfresh (dom Γ)
      z'∉fvB-y : z' ∉ fv B - y
      z'∉fvB-y = c∉xs++ys→c∉ys {xs = fv A} (c∉xs++ys→c∉xs (freshAsg z'∉domΓ Γ⊢Π[y:A]B:𝒰))
      sub' : σ ‚ z' := v z ∶ (Γ ‚ z' ∶ A) ⇀ Δ ‚ z ∶ A ∙ σ 
      sub' = subRen z'∉domΓ z∉domΔ Γ⊢A:s₁ Δ⊢Aσ:s₁ sub
      Δ,z:Aσok : Δ ‚ z ∶ A ∙ σ ok
      Δ,z:Aσok = ⊢cons Δok z∉domΔ Δ⊢Aσ:s₁
      ih : Δ ‚ z ∶ A ∙ σ ⊢ B [ y := v z' ] ∙ σ ‚ z' := v z ∶ c s₂
      ih = closureSub sub' Δ,z:Aσok (h z' z'∉domΓ)         
      lemma : B [ y := v z' ] ∙ σ ‚ z' := v z ∼α (B ∙ σ ‚ y := v y') [ y' := v z ]
      lemma = 
        begin
        B [ y := v z' ] ∙ σ ‚ z' := v z
        ≈⟨ sym (composRenUpd {y} {z'} {B} {v z} z'∉fvB-y) ⟩
        B ∙ σ ‚ y := v z
        ∼⟨ ∼σ (composRenUnary {y} {y'} {σ} {B} y'#σ⇂fvB-y) ⟩
        (B ∙ σ ‚ y := v y') [ y' := v z ]
        ∎ 

  infixl 6 _∙∙_ 
  _∙∙_ : Cxt → Sub → Cxt
  [] ∙∙ _ = []
  ((x , A) ∷ Γ) ∙∙ σ = (x , A ∙ σ) ∷ (Γ ∙∙ σ)

  subDistribDecl : ∀ {Γ x A σ} → (x , A) ∈ Γ → (x , A ∙ σ) ∈ (Γ ∙∙ σ) 
  subDistribDecl (here refl) = here refl
  subDistribDecl (there x,A∈Γ) = there (subDistribDecl x,A∈Γ)

  open import Data.List.Relation.Binary.Pointwise as PW

  lemma∙∙ι : ∀ {Γ} → Γ ≈α Γ ∙∙ ι
  lemma∙∙ι {[]} = []
  lemma∙∙ι {(x , A) ∷ Γ} = (PEq.refl , lemma∙ι) ∷ lemma∙∙ι {Γ}

  subUnaryAux : ∀ {x s Γ N A} → x ∉ dom Γ → Γ ⊢ A ∶ s → Γ ∙∙ ι ⊢ N ∶ A ∙ ι → ι ‚ x := N ∶ (Γ ‚ x ∶ A) ⇀ Γ ∙∙ ι
  subUnaryAux {x} x∉domΓ Γ⊢A:𝒰 Γι⊢N:Aι {y} y∈domΓ,x:Aι with x ≟ y
  subUnaryAux {x} {s} {Γ} {N} {A} x∉domΓ Γ⊢A:s Γι⊢N:Aι {.x} (here refl) | yes refl = subst (_⊢_∶_ (Γ ∙∙ ι) N) Aι=Aι<+x,N Γι⊢N:Aι
    where
    x#A : x # A
    x#A = c∉xs++ys→c∉xs (freshAsg x∉domΓ Γ⊢A:s)
    Aι=Aι<+x,N : A ∙ ι ≡ A ∙ ι ‚ x := N
    Aι=Aι<+x,N = sym (updFresh {x} {A} x#A)
  subUnaryAux {x} x∉domΓ _ _ {.x} (there x,B∈Γ) | yes refl = ⊥-elim (x∉domΓ (inCxtInDom x,B∈Γ))
  subUnaryAux {x} {Γ} {N} {A} _ _ _ {.x} (here refl) | no x≠x = ⊥-elim (x≠x PEq.refl)
  subUnaryAux {x} {s} {Γ} {N} {A} x∉domΓ Γ⊢A:s Γι⊢N:Aι {y} {B} (there y,B∈Γ) | no _ = subst (_⊢_∶_ (Γ ∙∙ ι) (v y)) Bι=[N/x]B ιΓ⊢y:ιB
    where
    Γok : Γ ok
    Γok = validCxtAsg Γ⊢A:s
    Γιok : Γ ∙∙ ι ok
    Γιok = validCxtAsg Γι⊢N:Aι
    x#B : x # B
    x#B = freshCxt Γok x∉domΓ y,B∈Γ
    Bι=[N/x]B : B ∙ ι ≡ B ∙ ι ‚ x := N
    Bι=[N/x]B = sym (updFresh {x} {B} x#B)
    y,Bι∈Γι : (y , B ∙ ι) ∈ (Γ ∙∙ ι)
    y,Bι∈Γι = subDistribDecl y,B∈Γ
    ιΓ⊢y:ιB : Γ ∙∙ ι ⊢ v y ∶ B ∙ ι
    ιΓ⊢y:ιB = ⊢var Γιok y,Bι∈Γι

  subUnary : ∀ {x s Γ N A} → x ∉ dom Γ → Γ ⊢ A ∶ s → Γ ⊢ N ∶ A → ι ‚ x := N ∶ (Γ ‚ x ∶ A) ⇀ Γ
  subUnary {x} {s} {Γ} {N} {A} x∉domΓ Γ⊢A:s Γ⊢N:A {z} {B} z,B∈Γ =
    closAlphaAsg (∼σs lemma∙∙ι) ∼ρ Γι⊢z[x=N]:A[x=N] 
    where
    ιΓ⊢N:ιA : Γ ∙∙ ι ⊢ N ∶ A ∙ ι
    ιΓ⊢N:ιA = closAlphaPred lemma∙∙ι lemma∙ι Γ⊢N:A
    ιΓok : Γ ∙∙ ι ok
    ιΓok = validCxtAsg ιΓ⊢N:ιA
    ι,x=N:Γ,x:A→Γι : ι ‚ x := N ∶ (Γ ‚ x ∶ A) ⇀ Γ ∙∙ ι
    ι,x=N:Γ,x:A→Γι = subUnaryAux x∉domΓ Γ⊢A:s ιΓ⊢N:ιA
    Γι⊢z[x=N]:A[x=N] : Γ ∙∙ ι ⊢ (ι ‚ x := N) z ∶ B ∙ ι ‚ x := N
    Γι⊢z[x=N]:A[x=N] = ι,x=N:Γ,x:A→Γι z,B∈Γ

  cut :  ∀ {Γ M N A B x} → Γ ‚ x ∶ A ⊢ M ∶ B → Γ ⊢ N ∶ A → Γ ⊢ M [ x := N ] ∶ B [ x := N ]
  cut {Γ} {M} {N} {A} {B} {x} Γ,x:A⊢M:B Γ⊢N:A with syntacticValidity Γ⊢N:A
  cut {Γ} {M} {N} {.(c s)} {B} {x} Γ,x:s⊢M:B Γ⊢N:s | s , inj₁ refl =
    closureSub ι,x=N:Γ,x:s→Γ Γok Γ,x:s⊢M:B
    where
    x∉domΓ : x ∉ dom Γ
    x∉domΓ with validCxtAsg Γ,x:s⊢M:B
    ... | ⊢cons _ x∉domΓ _ = x∉domΓ
    Γok : Γ ok
    Γok = validCxtAsg Γ⊢N:s
    Γ⊢s:s' : ∃ λ s' → Γ ⊢ c s ∶ c s'
    Γ⊢s:s' with validCxtAsg Γ,x:s⊢M:B
    ... | ⊢cons {s = s'} _ _ Γ⊢s:s' = s' , Γ⊢s:s'
    ι,x=N:Γ,x:s→Γ : ι ‚ x := N ∶ (Γ ‚ x ∶ c s) ⇀ Γ
    ι,x=N:Γ,x:s→Γ = subUnary x∉domΓ (proj₂ Γ⊢s:s') Γ⊢N:s  
  ... | s , inj₂ Γ⊢A:s =
    closureSub ι,x=N:Γ,x:A→Γ Γok Γ,x:A⊢M:B
    where
    x∉domΓ : x ∉ dom Γ
    x∉domΓ with validCxtAsg Γ,x:A⊢M:B
    ... | ⊢cons _ x∉domΓ _ = x∉domΓ
    Γok : Γ ok
    Γok = validCxtAsg Γ⊢N:A
    ι,x=N:Γ,x:A→Γ : ι ‚ x := N ∶ (Γ ‚ x ∶ A) ⇀ Γ
    ι,x=N:Γ,x:A→Γ = subUnary x∉domΓ Γ⊢A:s Γ⊢N:A

  identSub : ∀ {Γ} → Γ ok → ι ∶ Γ ⇀ Γ ∙∙ ι
  identSub {_} Γok {x} x,A∈Γ = closureAlpha lemma∙∙ι ∼ρ lemma∙ι (⊢var Γok x,A∈Γ)

  unaryRen : ∀ {Γ x y A M B} → y ∉ dom Γ → Γ ‚ x ∶ A ⊢ M ∶ B → Γ ‚ y ∶ A ⊢ M [ x := v y ] ∶ B [ x := v y ]
  unaryRen {Γ} {x} {y} {A} {M} {B} y∉domΓ Γ,x:A⊢M:B = closureAlpha Γι,y:Aι∼Γ,y:A ∼ρ ∼ρ Γι,y:Aι⊢M[x=y]:B[x=y]
    where
    Γ,x:Aok : Γ ‚ x ∶ A ok
    Γ,x:Aok = validCxtAsg Γ,x:A⊢M:B
    Γ⊢A:s : ∃ λ s → Γ ⊢ A ∶ c s
    Γ⊢A:s with Γ,x:Aok
    ... | ⊢cons {s = s} _ _ Γ⊢A:s = s , Γ⊢A:s
    x∉domΓ : x ∉ dom Γ
    x∉domΓ with Γ,x:Aok
    ... | ⊢cons _ x∉domΓ _ = x∉domΓ
    y∉domΓι : y ∉ dom (Γ ∙∙ ι)
    y∉domΓι = lemma∉≈α y∉domΓ (∼σs lemma∙∙ι)
    Γι⊢Aι:s : ∃ λ s → Γ ∙∙ ι ⊢ A ∙ ι ∶ c s
    Γι⊢Aι:s = proj₁ Γ⊢A:s , closureAlpha lemma∙∙ι lemma∙ι ∼ρ (proj₂ Γ⊢A:s)
    Γok : Γ ok
    Γok = validCxtAsg (proj₂ Γ⊢A:s)
    Γιok : Γ ∙∙ ι ok
    Γιok = closAlphaCxt lemma∙∙ι Γok
    Γι,y:Aι∼Γ,y:A : Γ ∙∙ ι ‚ y ∶ A ∙ ι ≈α Γ ‚ y ∶ A
    Γι,y:Aι∼Γ,y:A = _∷_ (PEq.refl , (∼σ lemma∙ι)) (∼σs lemma∙∙ι)
    Γι,y:Aιok : Γ ∙∙ ι ‚ y ∶ A ∙ ι ok    
    Γι,y:Aιok =  ⊢cons Γιok y∉domΓι (proj₂ Γι⊢Aι:s)
    ι,x=y:Γ,x:A→Γ,y:Aι : (ι ‚ x := v y) ∶ (Γ ‚ x ∶ A) ⇀ (Γ ‚ y ∶ A) ∙∙ ι
    ι,x=y:Γ,x:A→Γ,y:Aι = subRen x∉domΓ y∉domΓι (proj₂ Γ⊢A:s) (proj₂ Γι⊢Aι:s) (identSub Γok)
    Γι,y:Aι⊢M[x=y]:B[x=y] : Γ ∙∙ ι ‚ y ∶ A ∙ ι ⊢ M [ x := v y ] ∶ B [ x := v y ]
    Γι,y:Aι⊢M[x=y]:B[x=y] = closureSub ι,x=y:Γ,x:A→Γ,y:Aι Γι,y:Aιok Γ,x:A⊢M:B

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as StarProp
open import Relation.Binary.Construct.Union
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Level

open import Stoughton.Var

module BetaReduction (𝒞 : Set) {𝒱 : Set} (var : IsVar 𝒱) where

  private
    _≟_ = IsVar._≟_ var

  open import Stoughton.Chi (IsVar.encode var) (IsVar.decode var) (IsVar.inverse var)
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Alpha 𝒞 var
  open import Stoughton.Substitution 𝒞 var
  open import Stoughton.SubstitutionLemmas 𝒞 var  
  open import Beta 𝒞 var
  open import CxtClosure 𝒞 var _▹β_ as OneStepBeta using (→cxt; →λL; →λR; →ΠL; →ΠR; →·L; →·R) renaming (_→C_ to _→β_) public

  infix 3 _→β*_
  
  _→β*_ = Star (_∼α_ ∪ _→β_)
    
  abs-star-ty : ∀ {x A B M} → A →β* B → λ[ x ∶ A ] M →β* λ[ x ∶ B ] M
  abs-star-ty ε = ε
  abs-star-ty {x} {A} {B} {M} (_◅_ {_} {M'} (inj₁ A∼C) C→β*B) = inj₁ (∼λ A∼C y∉fvM-x y∉fvM-x (compatSubAlpha {M} ∼ρ)) ◅ abs-star-ty C→β*B
    where
    y : 𝒱
    y = X' (fv M - x)
    y∉fvM-x : y ∉ fv M - x
    y∉fvM-x = Xpfresh (fv M - x)
  abs-star-ty (inj₂ A→C ◅ C→β*B)  = (inj₂ (→λL A→C)) ◅ abs-star-ty C→β*B    

  abs-star : ∀ {x A M N} → M →β* N → λ[ x ∶ A ] M →β* λ[ x ∶ A ] N
  abs-star ε = ε
  abs-star {x} {A} {M} {N} (_◅_ {_} {M'} (inj₁ M∼M') (t'→β*t''))  = inj₁ (∼λ ∼ρ y∉fvM-x y∉fvM'-x (compatSubAlpha M∼M')) ◅ abs-star t'→β*t''
    where
    y : 𝒱
    y = X' ((fv M - x) ++ (fv M' - x))
    y∉fvM-x : y ∉ fv M - x
    y∉fvM-x = c∉xs++ys→c∉xs (Xpfresh ((fv M - x) ++ (fv M' - x)))
    y∉fvM'-x : y ∉ fv M' - x
    y∉fvM'-x = c∉xs++ys→c∉ys (Xpfresh ((fv M - x) ++ (fv M' - x)))
  abs-star (inj₂ t→t' ◅ t'→β*t'')  = (inj₂ (→λR t→t')) ◅ abs-star t'→β*t''

  pi-star-ty : ∀ {x A B M} → A →β* B → Π[ x ∶ A ] M →β* Π[ x ∶ B ] M
  pi-star-ty ε = ε
  pi-star-ty {x} {A} {B} {M} (_◅_ {_} {M'} (inj₁ A∼C) C→β*B) = inj₁ (∼Π A∼C y∉fvM-x y∉fvM-x (compatSubAlpha {M} ∼ρ)) ◅ pi-star-ty C→β*B
    where
    y : 𝒱
    y = X' (fv M - x)
    y∉fvM-x : y ∉ fv M - x
    y∉fvM-x = Xpfresh (fv M - x)
  pi-star-ty (inj₂ A→C ◅ C→β*B)  = (inj₂ (→ΠL A→C)) ◅ pi-star-ty C→β*B    

  pi-star : ∀ {x A M N} → M →β* N → Π[ x ∶ A ] M →β* Π[ x ∶ A ] N
  pi-star ε = ε
  pi-star {x} {A} {M} {N} (_◅_ {_} {M'} (inj₁ M∼M') (t'→β*t''))  = inj₁ (∼Π ∼ρ y∉fvM-x y∉fvM'-x (compatSubAlpha M∼M')) ◅ pi-star t'→β*t''
    where
    y : 𝒱
    y = X' ((fv M - x) ++ (fv M' - x))
    y∉fvM-x : y ∉ fv M - x
    y∉fvM-x = c∉xs++ys→c∉xs (Xpfresh ((fv M - x) ++ (fv M' - x)))
    y∉fvM'-x : y ∉ fv M' - x
    y∉fvM'-x = c∉xs++ys→c∉ys (Xpfresh ((fv M - x) ++ (fv M' - x)))
  pi-star (inj₂ t→t' ◅ t'→β*t'')  = (inj₂ (→ΠR t→t')) ◅ pi-star t'→β*t''    

  app-star-l : ∀ {M N P} → M →β* P → M · N →β* P · N
  app-star-l ε                 = ε
  app-star-l (inj₁ t∼t' ◅ t'→β*t'')  = (inj₁ (∼· t∼t' ∼ρ)) ◅ app-star-l t'→β*t''  
  app-star-l (inj₂ t→t' ◅ t'→β*t'')  = (inj₂ (→·L t→t')) ◅ app-star-l t'→β*t''

  app-star-r : ∀ {M N P} → N →β* P → M · N →β* M · P
  app-star-r ε                 = ε
  app-star-r (inj₁ t∼t' ◅ t'→β*t'')  = (inj₁ (∼· ∼ρ t∼t')) ◅ app-star-r t'→β*t''  
  app-star-r (inj₂ t→t' ◅ t'→β*t'')  = (inj₂ (→·R t→t')) ◅ app-star-r t'→β*t''

  open OneStepBeta.PreservesFreshness βpreserves# using (∈→C-) renaming (lemma*→C⁻¹ to lemma*→β⁻¹; lemma#→C to lemma#→β) public
  open import Definitions 𝒞 var
  
  lemma→α** : {x : 𝒱}{M N : Λ} → x * N → M →β* N → x * M
  lemma→α** x*N ε = x*N
  lemma→α** x*N (inj₁ M∼αP ◅ P→β*N) = lemmaM∼M'→free← M∼αP (lemma→α** x*N P→β*N)  
  lemma→α** x*N (inj₂ M→βP ◅ P→β*N) = lemma*→β⁻¹ (lemma→α** x*N P→β*N) M→βP

  lemma→α*# : {x : 𝒱}{M N : Λ} → x # M → M →β* N → x # N
  lemma→α*# = antipres*⇒pres# {_→β*_} lemma→α**

  lemma→β**- : {x y : 𝒱}{M M' : Λ} → M →β* M' → y ∈ fv M' - x → y ∈ fv M - x
  lemma→β**- ε y∈fvM-x = y∈fvM-x
  lemma→β**- {x} {y} (inj₁ P∼M ◅ M→β*N) y∈fvN-x = subst (λ xs → y ∈ xs - x) (M∼M'→fvM≡fvM' (∼σ P∼M)) (lemma→β**- M→β*N y∈fvN-x)  
  lemma→β**- (inj₂ P→M ◅ M→β*N) y∈fvN-x = ∈→C- (lemma→β**- M→β*N y∈fvN-x) P→M

  lemma→β*#- : {x y : 𝒱}{M M' : Λ} → M →β* M' → y ∉ fv M - x → y ∉ fv M' - x
  lemma→β*#- M→β*N y∉fvM-x y∈fvM'-x = ⊥-elim (y∉fvM-x (lemma→β**- M→β*N y∈fvM'-x))

  open OneStepBeta.CompatSubst βpreserves# compat∙β using () renaming (compat→C∙ to compatRedSub) public
  open OneStepBeta.CommutesAlpha βpreserves# compat∙β commutβα using () renaming (commut→Cα to compatAlphaRed) public  

  compatRedsSub : ∀ {M N σ} → M →β* N → M ∙ σ →β* N ∙ σ
  compatRedsSub ε = ε
  compatRedsSub (inj₁ M∼P ◅ P→*N) = inj₁ (≡⇒∼ (compatSubAlpha M∼P)) ◅ compatRedsSub P→*N
  compatRedsSub (inj₂ M→P ◅ P→*N) with compatRedSub M→P
  ... | Q , Mσ→Q , Q∼Pσ = inj₂ Mσ→Q ◅ inj₁ Q∼Pσ ◅ compatRedsSub P→*N

  ∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
  ∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c

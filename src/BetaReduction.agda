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
  infix 3 _→β*₀_  
  
  _→β*_ = Star (_∼α_ ∪ _→β_)
  _→β*₀_ = Star _→β_

{-
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
-}

  abs-star-ty : ∀ {x A B M} → A →β*₀ B → λ[ x ∶ A ] M →β*₀ λ[ x ∶ B ] M
  abs-star-ty ε = ε
  abs-star-ty (A→C ◅ C→β*B)  = →λL A→C ◅ abs-star-ty C→β*B    

  abs-star : ∀ {x A M N} → M →β*₀ N → λ[ x ∶ A ] M →β*₀ λ[ x ∶ A ] N
  abs-star ε = ε
  abs-star (t→t' ◅ t'→β*t'') = →λR t→t' ◅ abs-star t'→β*t''

  pi-star-ty : ∀ {x A B M} → A →β*₀ B → Π[ x ∶ A ] M →β*₀ Π[ x ∶ B ] M
  pi-star-ty ε = ε
  pi-star-ty (A→C ◅ C→β*B)  = →ΠL A→C ◅ pi-star-ty C→β*B    

  pi-star : ∀ {x A M N} → M →β*₀ N → Π[ x ∶ A ] M →β*₀ Π[ x ∶ A ] N
  pi-star ε = ε
  pi-star (t→t' ◅ t'→β*t'')  = →ΠR t→t' ◅ pi-star t'→β*t''    

  app-star-l : ∀ {M N P} → M →β*₀ P → M · N →β*₀ P · N
  app-star-l ε                 = ε
  app-star-l (t→t' ◅ t'→β*t'')  = →·L t→t' ◅ app-star-l t'→β*t''

  app-star-r : ∀ {M N P} → N →β*₀ P → M · N →β*₀ M · P
  app-star-r ε                 = ε 
  app-star-r (t→t' ◅ t'→β*t'')  = →·R t→t' ◅ app-star-r t'→β*t''
  
  open OneStepBeta.PreservesFreshness βpreserves# using (∈→C-) renaming (lemma*→C⁻¹ to lemma*→β⁻¹; lemma#→C to lemma#→β) public
  open import Definitions 𝒞 var

{-
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
-}

  lemma→α** : {x : 𝒱}{M N : Λ} → x * N → M →β*₀ N → x * M
  lemma→α** x*N ε = x*N
  lemma→α** x*N (M→βP ◅ P→β*N) = lemma*→β⁻¹ (lemma→α** x*N P→β*N) M→βP

  lemma→α*# : {x : 𝒱}{M N : Λ} → x # M → M →β*₀ N → x # N
  lemma→α*# = antipres*⇒pres# {_→β*₀_} lemma→α**

  lemma→β**- : {x y : 𝒱}{M M' : Λ} → M →β*₀ M' → y ∈ fv M' - x → y ∈ fv M - x
  lemma→β**- ε y∈fvM-x = y∈fvM-x
  lemma→β**- (P→M ◅ M→β*N) y∈fvN-x = ∈→C- (lemma→β**- M→β*N y∈fvN-x) P→M

  lemma→β*#- : {x y : 𝒱}{M M' : Λ} → M →β*₀ M' → y ∉ fv M - x → y ∉ fv M' - x
  lemma→β*#- M→β*N y∉fvM-x y∈fvM'-x = ⊥-elim (y∉fvM-x (lemma→β**- M→β*N y∈fvM'-x))
  
  open OneStepBeta.CompatSubst βpreserves# compat∙β using () renaming (compat→C∙ to compatRedSub) public
  open OneStepBeta.CommutesAlpha βpreserves# compat∙β commutβα using () renaming (commut→Cα to compatAlphaRed) public  

  manyStepCommutesAlpha : ∀ {M N P} → M ∼α N → N →β*₀ P → ∃ λ Q → M →β*₀ Q × Q ∼α P
  manyStepCommutesAlpha {M} {N} {.N} M∼N ε = M , ε , M∼N
  manyStepCommutesAlpha M∼N (N→P ◅ P→*Q) with compatAlphaRed M∼N N→P
  ... | R , M→R , R∼P with manyStepCommutesAlpha R∼P P→*Q
  ... | S , R→*S , S∼Q = S , M→R ◅ R→*S , S∼Q

  compatRedsSub : ∀ {M N σ} → M →β*₀ N → ∃ λ P → M ∙ σ →β*₀ P × P ∼α N ∙ σ
  compatRedsSub {M} {.M} {σ} ε = M ∙ σ , ε , ∼ρ
  compatRedsSub (M→P ◅ P→*N) with compatRedSub M→P | compatRedsSub P→*N
  ... | Q , Mσ→Q , Q∼Pσ | Q' , Pσ→*Q' , Q'∼Nσ with manyStepCommutesAlpha Q∼Pσ Pσ→*Q'
  ... | R , Q→*R , R∼Q' = R , Mσ→Q ◅ Q→*R , ∼τ R∼Q' Q'∼Nσ

{-
  compatRedsSub : ∀ {M N σ} → M →β* N → M ∙ σ →β* N ∙ σ
  compatRedsSub ε = ε
  compatRedsSub (inj₁ M∼P ◅ P→*N) = inj₁ (≡⇒∼ (compatSubAlpha M∼P)) ◅ compatRedsSub P→*N
  compatRedsSub (inj₂ M→P ◅ P→*N) with compatRedSub M→P
  ... | Q , Mσ→Q , Q∼Pσ = inj₂ Mσ→Q ◅ inj₁ Q∼Pσ ◅ compatRedsSub P→*N
-}

  ∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} (D : (x : A) → (y : B x) → C x y → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
  ∃₃ D = ∃ λ a → ∃ λ b → ∃ λ c → D a b c

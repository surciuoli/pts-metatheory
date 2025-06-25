{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat as Nat hiding (_*_; _≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.List
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Stoughton.Var

-- TODO: Rename to Thinning
module PTS.Thinning {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where 

  open import PTS isVar 𝒜 ℛ

  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Context 𝒱 Λ _≟_
  open import Stoughton.Alpha 𝒞 isVar
  open import Stoughton.Substitution 𝒞 isVar 

  inDomInCxt : ∀ {Γ x} → x ∈ dom Γ → ∃ λ A → (x , A) ∈ Γ
  inDomInCxt {[]} ()
  inDomInCxt {(x , A) ∷ _} (here refl) = A , here refl
  inDomInCxt {(_ , _) ∷ _} (there x∈domΓ) with inDomInCxt x∈domΓ
  ... | A , x,A∈Γ = A , there x,A∈Γ

  domCxtExt : ∀ {Γ Δ} → Γ ⊆ Δ → dom Γ ⊆ dom Δ
  domCxtExt Γ⊆Δ = λ x∈domΓ → inCxtInDom (Γ⊆Δ (proj₂ (inDomInCxt x∈domΓ)))

  ⊆⇒∉ : ∀ {x Γ Δ} → Γ ⊆ Δ → x ∉ dom Δ → x ∉ dom Γ
  ⊆⇒∉ h x∉domΔ x∈domΓ = ⊥-elim (x∉domΔ (domCxtExt h x∈domΓ))

  thinning : ∀ {Γ Δ M A} → Γ ⊆ Δ → Δ ok → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A  
  thinning {Γ} {Δ} {_} {A} Γ⊆Δ Δok (⊢var {x} _ x,A∈Γ) = ⊢var Δok (Γ⊆Δ x,A∈Γ)
  thinning _ Δok (⊢sort _ As₁s₂) = ⊢sort Δok As₁s₂
  thinning {Γ} {Δ} Γ⊆Δ Δok (⊢abs {x} {x′} {s₁} {s₂} {s₃} {A} {B} {M} Rs₁s₂s₃ Γ⊢A:s₁ h₀ h {- Γ⊢Π[x':A]B:s₂ -}) =
    ⊢abs Rs₁s₂s₃ Δ⊢A:s₁ {!!} goal {- Δ⊢Π[x':A]B:s₂ -}
    where
    --Δ⊢Π[x':A]B:s₂ : Δ ⊢ Π[ x′ ∶ A ] B ∶ c s₂
    --Δ⊢Π[x':A]B:s₂ = thinning Γ⊆Δ Δok Γ⊢Π[x':A]B:s₂
    Δ⊢A:s₁ : Δ ⊢ A ∶ c s₁
    Δ⊢A:s₁ = thinning Γ⊆Δ Δok Γ⊢A:s₁
    goal : ∀ y → y ∉ dom Δ → Δ ‚ y ∶ A ⊢ M ∙ ι ‚ x := v y ∶ B ∙ ι ‚ x′ := v y
    goal y y∉Δ = thinning Γ,y⊆Δ,y Δ,y:Aok (h y y∉Γ)
      where
      Δ,y:Aok : Δ ‚ y ∶ A ok
      Δ,y:Aok = ⊢cons Δok y∉Δ Δ⊢A:s₁
      y∉Γ : y ∉ dom Γ
      y∉Γ = ⊆⇒∉ Γ⊆Δ y∉Δ
      Γ,y⊆Δ,y : (Γ ‚ y ∶ A) ⊆ (Δ ‚ y ∶ A)
      Γ,y⊆Δ,y = ∷⁺ʳ (y , A) Γ⊆Δ
  thinning Γ⊆Δ Δok (⊢app Γ⊢M:ΠxAB Γ⊢N:A Γ⊢Π[x:A]B:s) =
    ⊢app (thinning Γ⊆Δ Δok Γ⊢M:ΠxAB) (thinning Γ⊆Δ Δok Γ⊢N:A) (thinning Γ⊆Δ Δok Γ⊢Π[x:A]B:s)
  thinning Γ⊆Δ Δok (⊢conv Γ⊢M:A A=B Γ⊢B:s) =
    ⊢conv (thinning Γ⊆Δ Δok Γ⊢M:A) A=B (thinning Γ⊆Δ Δok Γ⊢B:s)
  thinning {Γ} {Δ} Γ⊆Δ Δok (⊢prod {x} {s₁} {s₂} {s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ ∀y∉Γ→Γ,y⊢B[x=y]:s₂) =
    ⊢prod Rs₁s₂s₃ Δ⊢A:s₁ goal
    where
    Δ⊢A:s₁ : Δ ⊢ A ∶ c s₁
    Δ⊢A:s₁ = thinning Γ⊆Δ Δok Γ⊢A:s₁
    goal : ∀ y → y ∉ dom Δ → Δ ‚ y ∶ A ⊢ B ∙ ι ‚ x := v y ∶ c s₂
    goal y y∉Δ = thinning Γ,y⊆Δ,y Δ,y:Aok (∀y∉Γ→Γ,y⊢B[x=y]:s₂ y y∉Γ)
      where
      Δ,y:Aok : Δ ‚ y ∶ A ok
      Δ,y:Aok = ⊢cons Δok y∉Δ Δ⊢A:s₁
      y∉Γ : y ∉ dom Γ
      y∉Γ = ⊆⇒∉ Γ⊆Δ y∉Δ
      Γ,y⊆Δ,y : (Γ ‚ y ∶ A) ⊆ (Δ ‚ y ∶ A)
      Γ,y⊆Δ,y = ∷⁺ʳ (y , A) Γ⊆Δ 

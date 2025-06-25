import Stoughton.Syntax as Term
open import Stoughton.Var

module Beta (𝒞 : Set) {𝒱} (var : IsVar 𝒱) where

  open import Level
  open import Data.Product
  open import Data.Nat hiding (_*_; _≟_)
  open import Relation.Nullary
  import Relation.Binary.Reasoning.Preorder as PreR
  open import Relation.Binary.PropositionalEquality.Core
  open import Data.List renaming (map to mapL)
  open import Data.List.Properties
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.Empty
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any
  
  private
    _≟_ = IsVar._≟_ var
  
  open Term 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 var
  open import Stoughton.SubstitutionLemmas 𝒞 var
  open import Stoughton.Alpha 𝒞 var
  open import Definitions 𝒞 var
  open import Stoughton.Chi (IsVar.encode var) (IsVar.decode var) (IsVar.inverse var)

  infix 3 _▹β_
  data _▹β_ : Λ → Λ → Set where
    β : ∀ {x M N A} → λ[ x ∶ A ] M · N ▹β M [ x := N ]

  β⁻¹preserves* : AntiPreserves* _▹β_
  β⁻¹preserves* {x} .{λ[ y ∶ _ ] M · N} x*M[y/N] (β {y} {M} {N}) with lemmafreeσ→ₗ {x} {M} x*M[y/N]
  ...  | z , z*M , x*z[y/N] with y ≟ z
  β⁻¹preserves* {x} .{λ[ y ∶ A ] M · N} x*M[y/N] (β {y} {M} {N} {A}) | .y , y*M , x*N           | yes refl = ∈-++⁺ʳ (fv (λ[ y ∶ A ] M)) x*N
  β⁻¹preserves* {x} .{λ[ y ∶ A ] M · N} x*M[y/N] (β {y} {M} {N} {A})     | .x , x*M , here refl | no y≢z = ∈-++⁺ˡ (∈-++⁺ʳ (fv A) (lemma∈-≢ x*M y≢z)) 

  βpreserves# : Preserves# _▹β_
  βpreserves# = antipres*⇒pres# {_▹β_} β⁻¹preserves*
  
  compat∙β : Compat∙ _▹β_
  compat∙β .{λ[ x ∶ A ] M · N} {_} {σ} (β {x} {M} {N} {A}) = (M ∙ σ ‚ x := v y) ∙ ι ‚ y := (N ∙ σ) , β , aux
    where
    open PreR ≈-preorder∼
    y : 𝒱
    y = X (σ , fv M - x)
    aux : (M ∙ σ ‚ x := v y) ∙ ι ‚ y := (N ∙ σ) ∼α (M ∙ ι ‚ x := N) ∙ σ
    aux = begin
      (M ∙ σ ‚ x := v y) ∙ ι ‚ y := (N ∙ σ)
      ∼⟨ composRenUnary {x} {y} {σ} {M} (Xfresh σ (fv M - x)) ⟩
      M ∙ σ ‚ x := (N ∙ σ)
      ≈⟨ subDistribUpd {M} {N} {σ} {x} ⟩
      (M ∙ ι ‚ x := N) ∙ σ
      ∎

  commutβα : Comm∼α _▹β_
  commutβα .{λ[ x ∶ A ] M · N} .{λ[ x′ ∶ A′ ] M′ · N′} (∼· {_} {_} {N} .{N′} (∼λ {x} .{x′} {y} {A} .{A′} {M} .{M′} A∼A′ y#λxM y#λx′M′ M[y/x]∼M′[y/x′]) N∼N′) (β {x′} {M′} {N′} {A′}) =
    M ∙ ι ‚ x := N , β , aux
    where
    open PreR ≈-preorder∼
    aux : M ∙ ι ‚ x := N ∼α M′ ∙ ι ‚ x′ := N′
    aux = begin
      M ∙ ι ‚ x := N
      ≈⟨ composRenUpd {x} {y} {M} y#λxM ⟩
      (M ∙ ι ‚ x := v y) ∙ ι ‚ y := N
      ∼⟨ lemma-subst (≡⇒∼ M[y/x]∼M′[y/x′]) (lemma≺+∼α⇂ {y} lemmaι∼α⇂ N∼N′) ⟩
      (M′ ∙ ι ‚ x′ := v y) ∙ ι ‚ y := N′
      ≈⟨ sym (composRenUpd {x′} {y} {M′} y#λx′M′) ⟩
      M′ ∙ ι ‚ x′ := N′
      ∎

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PEq
open import Data.List
open import Relation.Nullary
open import Data.Empty
open import Data.List.Relation.Binary.Pointwise as Pw
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any as Any
open import Relation.Binary.Construct.Closure.SymmetricTransitive hiding (sym)
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Stoughton.Var

module PTS.ClosureAlpha
  {𝒞 𝒱 : Set}
  (enum : Enum 𝒱)
  (𝒜 : 𝒞 → 𝒞 → Set)
  (ℛ : 𝒞 → 𝒞 → 𝒞 → Set)
  where

  open Enum enum
    
  open import PTS enum 𝒜 ℛ
  open import PTS.Thinning enum 𝒜 ℛ
  
  open import Stoughton.Alpha 𝒞 enum
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 enum
  open import Stoughton.SubstitutionLemmas 𝒞 enum
  
  open import Context 𝒱 Λ _≟_
  open import Context.Properties 𝒞 enum
  
  open import Beta 𝒞 enum
  open import Conversion 𝒞 enum _▹β_ renaming (_≃_ to _≃β_)
  
  open import Relation.Binary.Reasoning.Preorder ≈-preorder∼

  lemma∉≈α : ∀ {y Γ Δ} → y ∉ dom Δ → Γ ≈α Δ → y ∉ dom Γ
  lemma∉≈α y∉Γ′ [] = λ ()
  lemma∉≈α {y} y∉Γ′,x (_∷_ {(x , _)} {(.x , _)} (refl , _) Γ∼Γ′) with y ≟ x
  lemma∉≈α {y} y∉Γ′,y (_∷_ {(.y , _)} {(.y , _)} (refl , _) Γ∼Γ′) | yes refl = ⊥-elim (y∉Γ′,y (here PEq.refl))
  lemma∉≈α {y} y∉Γ′,x (_∷_ {(x , A)} _ Γ∼Γ′) | no y≢x = ∉≢, y≢x (lemma∉≈α (lemma∉‚ y∉Γ′,x) Γ∼Γ′)

  alphaConvDecl : ∀ {x A Γ Δ} → Γ ≈α Δ → (x , A) ∈ Γ → ∃ λ B → (x , B) ∈ Δ × B ∼α A
  alphaConvDecl {x} {A} (_∷_ .{(x , A)} {(.x , B)} (refl , A∼B) _) (here refl) = B , here PEq.refl , ∼σ A∼B
  alphaConvDecl (_∷_ (refl , _) Γ∼Δ) (there x∈Γ) with alphaConvDecl Γ∼Δ x∈Γ
  ... | B , x,B∈Γ' , B∼A = B , there x,B∈Γ' , B∼A

  renameInvAux : ∀ {x x' y z B B'} → z ∉ fv B - x → z ∉ fv B' - x' → [ var z / x ] B ≡ [ var z / x' ] B' → [ var y / x ] B ≡ [ var y / x' ] B'
  renameInvAux {x} {x'} {y} {z} {B} {B'} z#ƛxB z#ƛx'B' [z/x]B∼[z/x']B' =
    begin-equality
    B ∙ ι ‚ x := var y
    ≡⟨ composRenUpd {x} {z} {B} {var y} {ι} z#ƛxB ⟩
    (B ∙ ι ‚ x := var z) ∙ ι ‚ z := var y
    ≡⟨ cong₂ _∙_ [z/x]B∼[z/x']B' PEq.refl  ⟩
    (B' ∙ ι ‚ x' := var z) ∙ ι ‚ z := var y
    ≡⟨ sym (composRenUpd {x'} {z} {B'} {var y} {ι} z#ƛx'B') ⟩
    B' ∙ ι ‚ x' := var y
    ∎

  invλ : ∀ {x x' y A A' M M'} → λ[ x ∶ A ] M ∼α λ[ x' ∶ A' ] M' → M [ x := var y ] ≡ M' [ x' := var y ]
  invλ {_} {_} {y} (∼λ {x} {x'} {z} {_} {_} {M} {M'} _ z∉fvM-x z∉fvM'-x' M[x=z]=M'[x'=z]) = renameInvAux {x} {x'} {y} {z} {M} {M'} z∉fvM-x z∉fvM'-x' M[x=z]=M'[x'=z]

  invΠ : ∀ {x x' y A A' M M'} → Π[ x ∶ A ] M ∼α Π[ x' ∶ A' ] M' → M [ x := var y ] ≡ M' [ x' := var y ]
  invΠ {_} {_} {y} (∼Π {x} {x'} {z} {_} {_} {M} {M'} _ z∉fvM-x z∉fvM'-x' M[x=z]=M'[x'=z]) = renameInvAux {x} {x'} {y} {z} {M} {M'} z∉fvM-x z∉fvM'-x' M[x=z]=M'[x'=z]
    
  closAlphaCxt : ∀ {Γ Δ} → Γ ≈α Δ → Γ ok → Δ ok
  closAlphaAsg : ∀ {Γ Δ M N A} → Γ ≈α Δ → M ∼α N → Γ ⊢ M ∶ A → Δ ⊢ N ∶ A
  
  closAlphaCxt [] ⊢nil = ⊢nil
  closAlphaCxt (_∷_ (refl , A∼B) Γ∼Δ) (⊢cons Γok x∉Γ Γ⊢A:s) =
    ⊢cons (closAlphaCxt Γ∼Δ Γok) (lemma∉≈α x∉Γ (∼σs Γ∼Δ)) (closAlphaAsg Γ∼Δ A∼B Γ⊢A:s)

  closAlphaAsg Γ∼Δ ∼const (⊢sort Γok As₁s₂) = ⊢sort (closAlphaCxt Γ∼Δ Γok) As₁s₂
  closAlphaAsg Γ∼Δ ∼var (⊢var Γok x,A∈Γ) with alphaConvDecl Γ∼Δ x,A∈Γ | closAlphaCxt Γ∼Δ Γok
  ... | B , x,B∈Δ , B∼A | Δok = ⊢conv (⊢var Δok x,B∈Δ) (lemma∼α⊆≃ B∼A) (proj₂ (lemma Γok Δok x,A∈Γ Γ∼Δ))
    where
    lemma : ∀ {Γ Δ x A} → Γ ok → Δ ok → (x , A) ∈ Γ → Γ ≈α Δ → ∃ λ s → Δ ⊢ A ∶ const s
    lemma ⊢nil _ ()
    lemma (⊢cons {.Γ'} {.x} {s} {.A} _ _ Γ'⊢A:s) Δ',x:Bok (here refl) (_∷_ {(x , A)} {(.x , B)} {Γ'} {Δ'} (refl , _) Γ'∼Δ') =
      s , thinning (xs⊆x∷xs Δ' (x , B)) Δ',x:Bok (closAlphaAsg Γ'∼Δ' ∼ρ Γ'⊢A:s)
    lemma (⊢cons Γok _ _) Δ,y:Bok@(⊢cons {Δ} {y} {_} {B} Δok y∉Δ Δ⊢C:𝒰) (there x,A∈Γ) (_∷_ (refl , _) Γ∼Δ) with lemma Γok Δok x,A∈Γ Γ∼Δ
    ... | s , Δ⊢A:s = s , thinning (xs⊆x∷xs Δ (y , B)) Δ,y:Bok Δ⊢A:s
  closAlphaAsg {Γ} {Δ} Γ∼Δ λ[x:A]B∼λ[x':A']B'@(∼λ {.x} {x'} {w} {.A} {A'} {.M} {M'} A∼A' w#ƛxM w#ƛx'M' M[x=w]∼M'[x'=w])
    (⊢abs {x} {y} {s₁} {s₂} {s₃} {A} {B} {M} Rs₁s₂s₂ Γ⊢A:s₁ h2 h1) =
    ⊢conv (⊢abs {Δ} {x'} {y} {s₁} {s₂} {s₃} {A'} {B} Rs₁s₂s₂  Δ⊢A':s₁ goal goal₀) (lemma∼α⊆≃ (∼σ Π[y:A]B∼Π[y:A']B)) Δ⊢Π[y:A]B:s₃
    where
    Π[y:A]B∼Π[y:A']B : Π[ y ∶ A ] B ∼α Π[ y ∶ A' ] B
    Π[y:A]B∼Π[y:A']B = ∼Π A∼A' (∉- (fv B)) (∉- (fv B)) PEq.refl
    goal : ∀ z → z ∉ dom Δ → Δ ‚ z ∶ A' ⊢ M' [ x' := var z ] ∶ B [ y := var z ]
    goal z z∉Δ = closAlphaAsg (_∷_ (PEq.refl , A∼A') Γ∼Δ) (≡⇒∼ M[x=z]∼M'[x'=z]) (h2 z z∉Γ)
      where
      z∉Γ : z ∉ dom Γ
      z∉Γ = lemma∉≈α z∉Δ Γ∼Δ
      M[x=z]∼M'[x'=z] : M ∙ ι ‚ x := var z ≡ M' ∙ ι ‚ x' := var z
      M[x=z]∼M'[x'=z] = invλ {y = z} λ[x:A]B∼λ[x':A']B'
    goal₀ : ∀ z → z ∉ dom Δ → Δ ‚ z ∶ A' ⊢ B [ y := var z ] ∶ const s₂
    goal₀ z z∉Δ = closAlphaAsg (_∷_ (PEq.refl , A∼A') Γ∼Δ) ∼ρ (h1 z z∉Γ)
      where
      z∉Γ : z ∉ dom Γ
      z∉Γ = lemma∉≈α z∉Δ Γ∼Δ         
    Δ⊢A':s₁ : Δ ⊢ A' ∶ const s₁
    Δ⊢A':s₁ = closAlphaAsg Γ∼Δ A∼A' Γ⊢A:s₁
    Δ⊢Π[y:A]B:s₃ : Δ ⊢ Π[ y ∶ A ] B ∶ const s₃
    Δ⊢Π[y:A]B:s₃ = ⊢prod Rs₁s₂s₂ (closAlphaAsg Γ∼Δ ∼ρ Γ⊢A:s₁) (λ z z∉Δ → closAlphaAsg (_∷_ (PEq.refl , ∼ρ) Γ∼Δ) ∼ρ (h1 z (lemma∉≈α z∉Δ Γ∼Δ)))
  closAlphaAsg {Γ} {Δ} Γ∼Δ (∼· {M} {M'} {N} {N'} M∼M' N∼N') (⊢app {x} {s} {A = A} {B = B} Γ⊢M:Π[x:A]B Γ⊢N:A Γ⊢[N/x]B:s) =
    ⊢conv Δ⊢M'N':[N'/x]B (lemma∼α⊆≃ (∼σ [N/x]B∼[N'/x]B)) Δ⊢[N/x]B:s
    where
    Δ⊢M':Π[x:A]B : Δ ⊢ M' ∶ Π[ x ∶ A ] B
    Δ⊢M':Π[x:A]B = closAlphaAsg Γ∼Δ M∼M' Γ⊢M:Π[x:A]B
    Δ⊢N':A : Δ ⊢ N' ∶ A
    Δ⊢N':A = closAlphaAsg Γ∼Δ N∼N' Γ⊢N:A
    [N/x]B∼[N'/x]B : B [ x := N ] ∼α B [ x := N' ]
    [N/x]B∼[N'/x]B = subAlpha {B} (lemma≺+∼α⇂ lemmaι∼α⇂ N∼N')
    Δ⊢[N'/x]B:s : Δ ⊢ B [ x := N' ] ∶ const s
    Δ⊢[N'/x]B:s = closAlphaAsg Γ∼Δ [N/x]B∼[N'/x]B Γ⊢[N/x]B:s
    Δ⊢M'N':[N'/x]B : Δ ⊢ M' · N' ∶ B [ x := N' ]
    Δ⊢M'N':[N'/x]B = ⊢app Δ⊢M':Π[x:A]B Δ⊢N':A Δ⊢[N'/x]B:s
    Δ⊢[N/x]B:s : Δ ⊢ B [ x := N ] ∶ const s
    Δ⊢[N/x]B:s = closAlphaAsg Γ∼Δ ∼ρ Γ⊢[N/x]B:s
  closAlphaAsg Γ∼Δ M∼N (⊢conv Γ⊢M:A A=B Γ⊢B:s) = ⊢conv (closAlphaAsg Γ∼Δ M∼N Γ⊢M:A) A=B (closAlphaAsg Γ∼Δ ∼ρ Γ⊢B:s)
  closAlphaAsg {Γ} {Δ} Γ∼Δ Π[x:A]B∼Π[x':A']B'@(∼Π {x} {x′} {z} {A} {A′}{B}{B′} A∼A′ z#ƛxB z#ƛx′B′ B[x=z]∼B′[x′=z]) Γ⊢Πx:AB:𝒰@(⊢prod {x}{s₁}{s₂}{s₃} {A} {B} Rs₁s₂s₃ Γ⊢A:s₁ ∀y∉Γ→Γ,y:A⊢B[x=y]:s₂) = 
    ⊢prod Rs₁s₂s₃ (closAlphaAsg Γ∼Δ A∼A′ Γ⊢A:s₁) goal
    where
    goal : ∀ y → y ∉ dom Δ → Δ ‚ y ∶ A′ ⊢ B′ ∙ ι ‚ x′ := var y ∶ const s₂
    goal y y∉Δ = closAlphaAsg (_∷_ (PEq.refl , A∼A′) Γ∼Δ) (≡⇒∼ B[x=y]∼B′[x′=y]) (∀y∉Γ→Γ,y:A⊢B[x=y]:s₂ y y∉Γ)
      where
      y∉Γ : y ∉ dom Γ
      y∉Γ = lemma∉≈α y∉Δ Γ∼Δ
      B[x=y]∼B′[x′=y] : B ∙ ι ‚ x := var y ≡ B′ ∙ ι ‚ x′ := var y
      B[x=y]∼B′[x′=y] = invΠ {y = y} Π[x:A]B∼Π[x':A']B'

  open import PTS.SyntacticValidity enum 𝒜 ℛ

  closAlphaPred : ∀ {Γ Δ M A B} → Γ ≈α Δ → A ∼α B → Γ ⊢ M ∶ A → Δ ⊢ M ∶ B
  closAlphaPred {Γ} {Δ} {M} {A} {B} Γ∼Δ A∼B Γ⊢M:A with syntacticValidity Γ⊢M:A
  closAlphaPred {Γ} {Δ} {M} {.(const s)} {.(const s)} Γ∼Δ ∼const Γ⊢M:s | s , inj₁ refl = Δ⊢M:s
    where
    Δ⊢M:s : Δ ⊢ M ∶ const s
    Δ⊢M:s = closAlphaAsg Γ∼Δ ∼ρ Γ⊢M:s
  closAlphaPred {Γ} {Δ} {M} {A} {B} Γ∼Δ A∼B Γ⊢M:A | s , inj₂ Γ⊢A:s = ⊢conv Δ⊢M:A (lemma∼α⊆≃ A∼B) Δ⊢B:s
    where
    Δ⊢M:A : Δ ⊢ M ∶ A
    Δ⊢M:A = closAlphaAsg Γ∼Δ ∼ρ Γ⊢M:A
    Δ⊢B:s : Δ ⊢ B ∶ const s
    Δ⊢B:s = closAlphaAsg Γ∼Δ A∼B Γ⊢A:s

  closureAlpha : ∀ {Γ Δ M N A B} → Γ ≈α Δ → M ∼α N → A ∼α B → Γ ⊢ M ∶ A → Δ ⊢ N ∶ B
  closureAlpha Γ∼Δ M∼N A∼B Γ⊢M:A = closAlphaPred ∼ρs A∼B (closAlphaAsg Γ∼Δ M∼N Γ⊢M:A)

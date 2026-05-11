open import Relation.Binary.PropositionalEquality 
open import Data.List 
open import Data.Product hiding (map)
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional
open import Data.Empty
open import Relation.Binary
open import Relation.Nullary

module Context (K : Set) (D : Set) (_≟_ : Decidable {A = K} _≡_)  where

  Cxt : Set
  Cxt = List (K × D)

  ∅ : Cxt
  ∅ = []

  dom : Cxt → List K
  dom = map proj₁

  infixl 4 _‚_∶_ 
  _‚_∶_ : Cxt → K → D → Cxt
  Γ ‚ x ∶ A = (x , A) ∷ Γ

  ∉≢, : {y x : K} {Γ : List K} → y ≢ x → y ∉ Γ → y ∉ x ∷ Γ
  ∉≢, {y} {.y} y≢y _ (here refl) = ⊥-elim (y≢y refl)
  ∉≢, {y} {x} _ y∉Γ (there y∈Γ) = ⊥-elim (y∉Γ y∈Γ)

  lemma∉‚ : {x y : K}{Γ : List K} → x ∉ y ∷ Γ → x ∉ Γ
  lemma∉‚ {x} {y} x∉y,Γ x∈Γ with x ≟ y
  lemma∉‚ {x} {.x} x∉Γ,y x∈Γ | yes refl = x∉Γ,y (here refl)
  ... | no x≢y = x∉y,Γ (there x∈Γ)

  inCxtInDom : ∀ {x A Γ} → (x , A) ∈ Γ → x ∈ dom Γ
  inCxtInDom (here refl) = here refl
  inCxtInDom (there x,A∈Γ) = there (inCxtInDom x,A∈Γ)

  lemma∉′∷ : {x y : K}{Γ : List K} → x ∉ y ∷ Γ → x ∉ Γ 
  lemma∉′∷ h a = h (Any.there a)

  lemma∉′∷≢ : {x y : K}{Γ : List K} → x ∉ y ∷ Γ → x ≢ y
  lemma∉′∷≢ {x} {y} x∉y::Γ with x ≟ y
  lemma∉′∷≢ {x} {.x} x∉x::Γ | yes refl = ⊥-elim (x∉x::Γ (Any.here refl))
  lemma∉′∷≢ {x} {y} _ | no x≢y = x≢y

  lemma∈‚≢ : {z y : K}{Γ : List K} → z ∈ y ∷ Γ → z ≢ y → z ∈ Γ
  lemma∈‚≢ (here z=y) z≢y = ⊥-elim (z≢y z=y)
  lemma∈‚≢ (there z∈Γ) _ = z∈Γ

  lemma-z≢x : ∀ {x z Γ} → z ∈ Γ → x ∉ Γ → z ≢ x
  lemma-z≢x {x} {z} x∈Γ z∉Γ with z ≟ x
  lemma-z≢x {x} {.x} x∈Γ x∉Γ | yes refl = ⊥-elim (x∉Γ x∈Γ)
  ... | no z≢x = z≢x

open import Data.Product
open import Level

module Utils where

  ∃₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) → (y : B x) → C x y → Set d}
       (E : (x : A) → (y : B x) → (z : C x y) → D x y z → Set e) → Set (a ⊔ b ⊔ c ⊔ d ⊔ e)
  ∃₄ E = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → E a b c d
  
  ∃₅ : ∀ {a b c d e f} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) → (y : B x) → C x y → Set d}
       {E : (x : A) → (y : B x) → (z : C x y) → D x y z → Set e}
       (F : (x : A) → (y : B x) → (z : C x y) → (α : D x y z) → E x y z α → Set f) → Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f)
  ∃₅ F = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → ∃ λ e → F a b c d e 

  ∃₆ : ∀ {a b c d e f g} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : (x : A) → (y : B x) → C x y → Set d}
     {E : (x : A) → (y : B x) → (z : C x y) → D x y z → Set e} {F : (x : A) → (y : B x) → (z : C x y) → (α : D x y z) → E x y z α → Set f}
     (G : (x : A) → (y : B x) → (z : C x y) → (α : D x y z) → (β : E x y z α) → F x y z α β → Set g) → Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ g)
  ∃₆ G = ∃ λ a → ∃ λ b → ∃ λ c → ∃ λ d → ∃ λ e → ∃ λ f → G a b c d e f

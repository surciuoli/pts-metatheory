open import Data.List as List renaming (map to mapL) hiding ([_])
open import Data.List.Membership.Propositional
open import Data.Product renaming (map to mapP)
open import Data.Empty
open import Data.Sum
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST
open import Relation.Binary.Construct.Closure.ReflexiveTransitive  
open import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Relation.Nullary
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional.Properties
open import Level
open import Relation.Binary.Construct.Union

open import Stoughton.Var

module PTS {𝒞 𝒱 : Set} (isVar : IsVar 𝒱) (𝒜 : 𝒞 → 𝒞 → Set) (ℛ : 𝒞 → 𝒞 → 𝒞 → Set) where

  _≟_ = IsVar._≟_ isVar
  
  open import Stoughton.Chi (IsVar.encode isVar) (IsVar.decode isVar) (IsVar.inverse isVar)
  open import Stoughton.Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 isVar 
  open import Stoughton.SubstitutionLemmas 𝒞 isVar
  open import Stoughton.Alpha 𝒞 isVar
  open import Beta 𝒞 isVar
  open import Context 𝒱 Λ _≟_
  open import CxtClosure 𝒞 isVar _▹β_ as Red
  open import Definitions 𝒞 isVar
  open import BetaConversion 𝒞 isVar
  open import BetaReduction 𝒞 isVar
  
  lemma∉′∷ : {x y : 𝒱}{Γ : List 𝒱} → x ∉ y ∷ Γ → x ∉ Γ 
  lemma∉′∷ h a = h (Any.there a)

  lemma∉′∷≢ : {x y : 𝒱}{Γ : List 𝒱} → x ∉ y ∷ Γ → x ≢ y
  lemma∉′∷≢ {x} {y} x∉y::Γ with x ≟ y
  lemma∉′∷≢ {x} {.x} x∉x::Γ | yes refl = ⊥-elim (x∉x::Γ (Any.here refl))
  lemma∉′∷≢ {x} {y} _ | no x≢y = x≢y

  lemma∈‚≢ : {z y : 𝒱}{Γ : List 𝒱} → z ∈ y ∷ Γ → z ≢ y → z ∈ Γ
  lemma∈‚≢ (here z=y) z≢y = ⊥-elim (z≢y z=y)
  lemma∈‚≢ (there z∈Γ) _ = z∈Γ

  lemma-z≢x : ∀ {x z Γ} → z ∈ Γ → x ∉ Γ → z ≢ x
  lemma-z≢x {x} {z} x∈Γ z∉Γ with z ≟ x
  lemma-z≢x {x} {.x} x∈Γ x∉Γ | yes refl = ⊥-elim (x∉Γ x∈Γ)
  ... | no z≢x = z≢x

  infix 3 _ok 
  infix 3 _⊢_∶_ 

  data _ok : Cxt → Set 
  data _⊢_∶_ Cxt : Λ → Λ → Set 
  
  data _ok where 
    ⊢nil : [] ok 
    ⊢cons : ∀ {Γ x s A} → Γ ok → x ∉ dom Γ → Γ ⊢ A ∶ c s → Γ ‚ x ∶ A ok 

  data _⊢_∶_ Γ where 
    ⊢var : ∀ {x A}
         → Γ ok
         → (x , A) ∈ Γ
         → Γ ⊢ v x ∶ A
    ⊢sort : ∀ {s₁ s₂}
          → Γ ok
          → 𝒜 s₁ s₂
          → Γ ⊢ c s₁ ∶ c s₂
    ⊢prod : ∀ {x s₁ s₂ s₃ A B}
          → ℛ s₁ s₂ s₃
          → Γ ⊢ A ∶ c s₁
          → (∀ y → y ∉ dom Γ → Γ ‚ y ∶ A ⊢ B [ x := v y ] ∶ c s₂)
          → Γ ⊢ Π[ x ∶ A ] B ∶ c s₃           
    ⊢abs : ∀ {x y s A B M}
         → (∀ z → z ∉ dom Γ → Γ ‚ z ∶ A ⊢ M [ x := v z ] ∶ B [ y := v z ])
         → Γ ⊢ Π[ y ∶ A ] B ∶ c s
         → Γ ⊢ λ[ x ∶ A ] M ∶ Π[ y ∶ A ] B        
    ⊢app : ∀ {x s M N A B}
         → Γ ⊢ M ∶ Π[ x ∶ A ] B
         → Γ ⊢ N ∶ A
         → Γ ⊢ B [ x := N ] ∶ c s
         → Γ ⊢ M · N ∶ B [ x := N ]
    ⊢conv : ∀ {s M A B}
          → Γ ⊢ M ∶ A
          → A ≃β B
          → Γ ⊢ B ∶ c s
          → Γ ⊢ M ∶ B

  inCxtInDom : ∀ {x A Γ} → (x , A) ∈ Γ → x ∈ dom Γ
  inCxtInDom (here refl) = here refl
  inCxtInDom (there x,A∈Γ) = there (inCxtInDom x,A∈Γ)

  freeCxt : ∀ {Γ y A w} → Γ ok → (y , A) ∈ Γ → w * A → w ∈ dom Γ
  freeAsg : ∀ {Γ M A w} → Γ ⊢ M ∶ A → w * M · A → w ∈ dom Γ
  
  freeCxt ⊢nil () _
  freeCxt (⊢cons {A = A} Γok _ Γ⊢A:s) (here refl) x*A = there (freeAsg Γ⊢A:s (∈-++⁺ˡ x*A))
  freeCxt (⊢cons Γok _ _) (there y∈Γ) x*Γy = there (freeCxt Γok y∈Γ x*Γy)

  freeAsg {Γ} {v x} (⊢var Γok x,A∈Γ) w*xΓx with ∈-++⁻ (x ∷ []) w*xΓx
  freeAsg {Γ} {v .w} {A} {w} (⊢var Γok w,A∈Γ) w*wΓw | inj₁ (here refl) = inCxtInDom w,A∈Γ
  freeAsg {Γ} {v x} (⊢var Γok x,A∈Γ) w*xΓx | inj₂ w*Γx = freeCxt Γok x,A∈Γ w*Γx
  freeAsg {Γ} {w = w} (⊢abs {x} {y} {s} {A} {B} {M} h Γ⊢Π[x:A]B:s) w*λxAMΠyAB with proj₁ (appList (fv (λ[ x ∶ A ] M))) w*λxAMΠyAB
  ... | inj₁ w*λxAM with proj₁ (appList (fv A)) w*λxAM          
  ... | inj₁ w*A = freeAsg Γ⊢Π[x:A]B:s (∈-++⁺ˡ (∈-++⁺ˡ w*A))
  ... | inj₂ w*M-x with proj₁ delList w*M-x
  ... | x≢w , w*M = lemma∈‚≢ w∈Γ,z:A (sym≢ z≢w)    
    where
    z : 𝒱
    z = X' (w ∷ dom Γ)
    z∉Γ : z ∉ dom Γ
    z∉Γ =  lemma∉′∷ (Xpfresh (w ∷ dom Γ))
    z≢w : z ≢ w
    z≢w = lemma∉′∷≢ (Xpfresh (w ∷ dom Γ))
    w∈fvw[x=z] : w ∈ fv ((ι ‚ x := v z) w)
    w∈fvw[x=z] with x ≟ w 
    ... | yes x=w = ⊥-elim (x≢w (PE.sym x=w))
    ... | no _ = here refl
    w*M[x=z] : w * M ∙ ι ‚ x := v z
    w*M[x=z] = proj₂ (noCapture {M = M}) (w , w*M , w∈fvw[x=z])
    w∈Γ,z:A : w ∈ z ∷ dom Γ 
    w∈Γ,z:A = freeAsg (h z z∉Γ) (∈-++⁺ˡ w*M[x=z])
  freeAsg {Γ} {w = w} (⊢abs {x} {y} {s} {A} {B} {M} h Γ⊢Π[x:A]B:s) w*λxMΠyB | inj₂ w*ΠxAB with ∈-++⁻ (fv A) w*ΠxAB
  ... | inj₁ w*A = freeAsg Γ⊢Π[x:A]B:s (∈-++⁺ˡ (∈-++⁺ˡ w*A))
  ... | inj₂ w*B-y with proj₁ delList w*B-y
  ... | y≢w , w*B = lemma∈‚≢ w∈Γ,z:A (sym≢ z≢w)    
    where
    z : 𝒱
    z = X' (w ∷ dom Γ)
    z∉Γ : z ∉ dom Γ
    z∉Γ =  lemma∉′∷ (Xpfresh (w ∷ dom Γ))
    z≢w : z ≢ w
    z≢w = lemma∉′∷≢ (Xpfresh (w ∷ dom Γ))
    w∈fvw[y=z] : w * (ι ‚ y := v z) w
    w∈fvw[y=z] with y ≟ w 
    ... | yes y=w = ⊥-elim (y≢w (PE.sym y=w))
    ... | no _ = here refl
    w*B[y=z] : w * B [ y := v z ]
    w*B[y=z] = lemmafreeσ←ₗ {M = B} (w , w*B , w∈fvw[y=z])
    w∈Γ,z:A : w ∈ z ∷ dom Γ 
    w∈Γ,z:A = freeAsg (h z z∉Γ) (∈-++⁺ʳ (fv (M [ x := v z ])) w*B[y=z])
  freeAsg (⊢app {z} {_} {M} {N} {A} {B} M:ΠxAB N:A _) w*MN·B[x=N] with proj₁ (appList (fv M ++ fv N)) w*MN·B[x=N]
  ... | inj₁ w*MN with proj₁ (appList (fv M)) w*MN
  ... | inj₁ w*M = freeAsg M:ΠxAB (∈-++⁺ˡ w*M)
  ... | inj₂ w*N = freeAsg N:A (∈-++⁺ˡ w*N)
  freeAsg (⊢app {x} {M} {N} {A} {B} M:ΠxAB N:A Γ⊢[N/x]B:s) w*MN·B[x=N] | inj₂ w*B[x=N] = freeAsg Γ⊢[N/x]B:s (∈-++⁺ˡ w*B[x=N])
  freeAsg (⊢conv {_} {M} {A} {B} Γ⊢M:A _ Γ⊢B:s) x*MB with ∈-++⁻ (fv M) x*MB 
  ... | inj₁ x*M  = freeAsg Γ⊢M:A (∈-++⁺ˡ x*M)
  ... | inj₂ x*B = freeAsg Γ⊢B:s (∈-++⁺ˡ x*B)
  freeAsg {Γ} {w = z} (⊢prod {x} {_} {_} {_} {A} {B} _ Γ⊢A:U h) z*ΠxAB·𝒰 with ∈-++⁻ (fv A ++ (fv B - x)) z*ΠxAB·𝒰 
  ... | inj₁ z*ΠxAB with ∈-++⁻ (fv A) z*ΠxAB
  ... | inj₁ z*A = freeAsg Γ⊢A:U (∈-++⁺ˡ z*A)
  ... | inj₂ z*B-x = lemma∈‚≢ z∈Γ,y:A (sym≢ y≢z)
    where
    x≢z : x ≢ z
    x≢z = sym≢ (∈-→≢ {xs = fv B} z*B-x)
    z*B : z * B
    z*B = ∈-→∈ z*B-x
    y : 𝒱
    y = X' (z ∷ dom Γ)
    y∉Γ : y ∉ dom Γ
    y∉Γ =  lemma∉′∷ (Xpfresh (z ∷ dom Γ))
    y≢z : y ≢ z
    y≢z = lemma∉′∷≢ (Xpfresh (z ∷ dom Γ))
    z∈fvz[x=y] : z * (ι ‚ x := v y) z
    z∈fvz[x=y] with x ≟ z 
    ... | yes x=z = ⊥-elim (x≢z x=z)
    ... | no _ = here refl
    z*B[x=y] : z * B [ x := v y ]
    z*B[x=y] = lemmafreeσ←ₗ {M = B} (z , z*B , z∈fvz[x=y])
    z∈Γ,y:A : z ∈ y ∷ dom Γ 
    z∈Γ,y:A = freeAsg (h y y∉Γ) (∈-++⁺ˡ z*B[x=y])
  freeAsg {Γ} {w = x} (⊢prod {y} {_} {A} {B} _ h _) x*ΠyAB·𝒰 | inj₂ ()  

  counter-reciproc : ∀ {A B : Set} → (A → B) → ¬ B → ¬ A
  counter-reciproc A→B ¬B = λ A → ⊥-elim (¬B (A→B A))

  freshCxt : ∀ {Γ y A w} → Γ ok → w ∉ dom Γ → (y , A) ∈ Γ → w # A
  freshCxt Γok w∉Γ y∈Γ = counter-reciproc (freeCxt Γok y∈Γ) w∉Γ

  freshAsg : ∀ {Γ M A w} → w ∉ dom Γ → Γ ⊢ M ∶ A → w # M · A
  freshAsg w∉Γ Γ⊢M:A = counter-reciproc (freeAsg Γ⊢M:A) w∉Γ

  validCxt : ∀ {Γ M A} → Γ ⊢ M ∶ A → Γ ok
  validCxt (⊢sort Γok _) = Γok
  validCxt (⊢var Γok _) = Γok
  validCxt (⊢abs _ t) = validCxt t
  validCxt (⊢app t _ _) = validCxt t
  validCxt (⊢conv t _ _) = validCxt t
  validCxt (⊢prod _ Γ⊢A:U _) = validCxt Γ⊢A:U
  
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

  -- TODO: Rename to genPi (or rename genLam to genAbs) and complete missing cases (var, sort and app).
  genProd : ∀ {Γ x A B C} → Γ ⊢ Π[ x ∶ A ] B ∶ C
        → ∃₃ λ s₁ s₂ s₃
        → ℛ s₁ s₂ s₃
        × Γ ⊢ A ∶ c s₁        
        × (∀ y → y ∉ dom Γ → Γ ‚ y ∶ A ⊢ B [ x := v y ] ∶ c s₂)
        × C ≃β c s₃
  genProd (⊢prod {s₁ = s₁} {s₂} {s₃} Rs₁s₂s₃ h₁ h₂) = s₁ , s₂ , s₃ , Rs₁s₂s₃ , h₁ , h₂ , Eq.reflexive (_∼α_ ∪ _→β_)        
  genProd (⊢conv Γ⊢Π[x:A]B:C C=D _) with genProd Γ⊢Π[x:A]B:C
  ... | s₁ , s₂ , s₃ , Rs₁s₂s₃ , h₁ , h₂ , C=𝒰 =
    s₁ , s₂ , s₃ , Rs₁s₂s₃ , h₁ , h₂ , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C=D) C=𝒰 

  genLam : ∀ {Γ x A M C} → Γ ⊢ λ[ x ∶ A ] M ∶ C
         → ∃₃ λ s x' B 
         → (∀ y → y ∉ dom Γ → Γ ‚ y ∶ A ⊢ M [ x := v y ] ∶ B [ x' := v y ])
         × Γ ⊢ Π[ x' ∶ A ] B ∶ c s
         × C ≃β Π[ x' ∶ A ] B
  genLam (⊢abs {x} {x'} {s} {A} {B} ∀y∉Γ→Γ,y:A⊢M[x=y]:B[x'=y] Γ⊢Π[x':A]B:s) =
    s , x' , B , ∀y∉Γ→Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[x':A]B:s , Eq.reflexive (_∼α_ ∪ _→β_)
  genLam (⊢conv Γ⊢λ[x:A]M:C C≃D _) with genLam Γ⊢λ[x:A]M:C
  ... | s , x' , B , ∀y∉Γ→Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[x':A]B:s , D≃Π[x':A]B =
    s , x' , B , ∀y∉Γ→Γ,y:A⊢M[x=y]:B[x'=y] , Γ⊢Π[x':A]B:s , transitive (_∼α_ ∪ _→β_) (Eq.symmetric (_∼α_ ∪ _→β_) C≃D) D≃Π[x':A]B


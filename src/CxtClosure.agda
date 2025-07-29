open import Relation.Binary
open import Level

import Stoughton.Syntax as Syntax
open import Stoughton.Var

-- rename to CxtClosure
module CxtClosure (𝒞 : Set) {𝒱} (var : IsVar 𝒱) (_▹_ : Rel (Syntax.Λ 𝒞 𝒱 (IsVar._≟_ var)) 0ℓ) where

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
  open import Data.Sum
  
  private
    _≟_ = IsVar._≟_ var
  
  open Syntax 𝒞 𝒱 _≟_
  open import Stoughton.Substitution 𝒞 var
  open import Stoughton.SubstitutionLemmas 𝒞 var
  open import Stoughton.Alpha 𝒞 var
  open import Definitions 𝒞 var
  open import Stoughton.Chi (IsVar.encode var) (IsVar.decode var) (IsVar.inverse var)

  -- Rename to CxtClosure
  infix 3 _→C_
  data _→C_ : Λ → Λ → Set where
    →cxt : ∀ {M N} → M ▹ N → M →C N    
    →λL : ∀ {x M A A'} → A →C A' → λ[ x ∶ A ] M →C λ[ x ∶ A' ] M
    →λR : ∀ {x M M' A} → M →C M' → λ[ x ∶ A ] M →C λ[ x ∶ A ] M'    
    →ΠL  : ∀ {x A A' B} → A →C A' → Π[ x ∶ A ] B →C Π[ x ∶ A' ] B
    →ΠR  : ∀ {x A B B'} → B →C B' → Π[ x ∶ A ] B →C Π[ x ∶ A ] B'    
    →·L : ∀ {M N P} → M →C N → M · P →C N · P
    →·R : ∀ {M N P} → M →C N → P · M →C P · N 

  module PreservesFreshness (pres# : Preserves# _▹_) where

    pres* : AntiPreserves* _▹_
    pres* = pres#⇒antipres* {_▹_} pres#

    lemma*→C⁻¹ : AntiPreserves* _→C_
    lemma*→C⁻¹ x*N (→cxt M▹N) = pres* x*N M▹N
    lemma*→C⁻¹ {x} {M · N'} {N · .N'} x*NN' (→·L M→CN) with ∈-++⁻ (fv N) x*NN'
    ... | inj₁ x*N  = ∈-++⁺ˡ (lemma*→C⁻¹ x*N M→CN)
    ... | inj₂ x*N' = ∈-++⁺ʳ (fv M) x*N'
    lemma*→C⁻¹ {x} {N' · M} {.N' · N} x*N'N (→·R M→CN) with ∈-++⁻ (fv N') x*N'N
    ... | inj₁ x*N' = ∈-++⁺ˡ x*N'
    ... | inj₂ x*N  = ∈-++⁺ʳ (fv N') (lemma*→C⁻¹ x*N M→CN)
    lemma*→C⁻¹ {x} {λ[ y ∶ A ] M} {λ[ y ∶ A ] N} x*λy:AN (→λR M→CN) with ∈-++⁻ (fv A) x*λy:AN
    ... | inj₁ x*A   = ∈-++⁺ˡ x*A
    ... | inj₂ x*N-y = ∈-++⁺ʳ (fv A) (lemma∈-≢ (lemma*→C⁻¹ (∈-→∈ x*N-y) M→CN) (sym≢ (∈-→≢ {xs = fv N} x*N-y)))
    lemma*→C⁻¹ {x} {λ[ y ∶ A ] M} {λ[ y ∶ B ] M} x*λy:BM (→λL A→CB) with ∈-++⁻ (fv B) x*λy:BM
    ... | inj₁ x*B   = ∈-++⁺ˡ (lemma*→C⁻¹ x*B A→CB)
    ... | inj₂ x*M-y = ∈-++⁺ʳ (fv A) x*M-y
    lemma*→C⁻¹ {x} {Π[ y ∶ A ] M} {Π[ y ∶ A ] N} x*Πy:AN (→ΠR M→CN) with ∈-++⁻ (fv A) x*Πy:AN
    ... | inj₁ x*A   = ∈-++⁺ˡ x*A
    ... | inj₂ x*N-y = ∈-++⁺ʳ (fv A) (lemma∈-≢ (lemma*→C⁻¹ (∈-→∈ x*N-y) M→CN) (sym≢ (∈-→≢ {xs = fv N} x*N-y)))
    lemma*→C⁻¹ {x} {Π[ y ∶ A ] M} {Π[ y ∶ B ] M} x*Πy:BM (→ΠL A→CB) with ∈-++⁻ (fv B) x*Πy:BM
    ... | inj₁ x*B   = ∈-++⁺ˡ (lemma*→C⁻¹ x*B A→CB)
    ... | inj₂ x*M-y = ∈-++⁺ʳ (fv A) x*M-y

    lemma#⇂→C : ∀ {x M N σ} → x #⇂ (σ , fv M) → M →C N → x #⇂ (σ , fv N)
    lemma#⇂→C {x} {M} {N} h M→N y y*N =  h y (lemma*→C⁻¹ y*N M→N)

    ∈→C- : ∀ {x y M N} → x ∈ fv N - y → M →C N → x ∈ fv M - y
    ∈→C- {z} {x} {M} {N} z∈fvN-x M→N = lemma∈-≢ z∉fvM (sym≢ (∈-→≢ {xs = fv N} z∈fvN-x))
      where
      z∉fvN : z ∈ fv N
      z∉fvN = ∈-→∈ z∈fvN-x
      z∉fvM : z ∈ fv M
      z∉fvM = lemma*→C⁻¹ z∉fvN M→N

    ∉→C- : ∀ {x y M N} → x ∉ fv M - y → M →C N → x ∉ fv N - y
    ∉→C- x∉vfM-y M→N x∈fvN-y = ⊥-elim (x∉vfM-y (∈→C- x∈fvN-y M→N))

    lemma#→C : Preserves# _→C_
    lemma#→C x#M M→N x*N = ⊥-elim (x#M (lemma*→C⁻¹ x*N M→N))

  module CompatSubst (pres : Preserves# _▹_) (compat : Compat∙ _▹_) where
    open PreservesFreshness pres

    compat→C∙ : Compat∙ _→C_
    compat→C∙ (→cxt M▹N) with compat M▹N
    ... | P , Mσ▹P , P∼Nσ = P , →cxt Mσ▹P , P∼Nσ
    compat→C∙ {λ[ x ∶ A ] M} {λ[ .x ∶ .A ] N} {σ} (→λR M→N) with compat→C∙ M→N
    ... | P , M→P , P∼N = λ[ y ∶ A ∙ σ ] P , →λR M→P , ∼τ (lemma∼λ ∼ρ P∼N) aux
      where
      y : 𝒱
      y = X (σ , fv M - x)
      y#σ⇂fvN-x : y #⇂ (σ , fv N - x)
      y#σ⇂fvN-x z z∈fvN-x = Xfresh σ (fv M - x) z (∈→C- z∈fvN-x M→N)
      aux : λ[ y ∶ A ∙ σ ](N ∙ σ ‚ x := v y) ∼α λ[ x ∶ A ] N ∙ σ
      aux = ∼σ (corollary4-2 {x} {y} {N} {A} y#σ⇂fvN-x)
    compat→C∙ {λ[ x ∶ A ] M} {λ[ .x ∶ A' ] M'} {σ} (→λL A→B) with compat→C∙ A→B
    ... | C , Aσ→C , C∼Bσ = λ[ y ∶ C ](M ∙ σ ‚ x := v y) , →λL Aσ→C , (lemma∼λ C∼Bσ ∼ρ)
      where
      y : 𝒱
      y = X (σ , fv M - x)
    compat→C∙ {Π[ x ∶ A ] M} {Π[ .x ∶ .A ] N} {σ} (→ΠR M→N) with compat→C∙ M→N
    ... | P , M→P , P∼N = Π[ y ∶ A ∙ σ ] P , →ΠR M→P , ∼τ (lemma∼Π ∼ρ P∼N) aux
      where
      y : 𝒱
      y = X (σ , fv M - x)
      y#σ⇂fvN-x : y #⇂ (σ , fv N - x)
      y#σ⇂fvN-x z z∈fvN-x = Xfresh σ (fv M - x) z (∈→C- z∈fvN-x M→N)
      aux : Π[ y ∶ A ∙ σ ](N ∙ σ ‚ x := v y) ∼α Π[ x ∶ A ] N ∙ σ
      aux = ∼σ (corollary4-2Π {x} {y} {N} {A} y#σ⇂fvN-x)
    compat→C∙ {Π[ x ∶ A ] M} {Π[ .x ∶ A' ] M'} {σ} (→ΠL A→B) with compat→C∙ A→B
    ... | C , Aσ→C , C∼Bσ = Π[ y ∶ C ](M ∙ σ ‚ x := v y) , →ΠL Aσ→C , (lemma∼Π C∼Bσ ∼ρ)
      where
      y : 𝒱
      y = X (σ , fv M - x)      
    compat→C∙ {M · N} {_} {σ} (→·L M→N) with compat→C∙ M→N
    ... | P , M→P , P∼N = P · (N ∙ σ) , →·L M→P , ∼· P∼N ∼ρ
    compat→C∙ {M · N} {_} {σ} (→·R M→N) with compat→C∙ M→N
    ... | P , M→P , P∼N = (M ∙ σ) · P , →·R M→P , ∼· ∼ρ P∼N 
    
  module CommutesAlpha (pres : Preserves# _▹_) (compat : Compat∙ _▹_) (comm : Comm∼α _▹_) where
    open PreservesFreshness pres
    open CompatSubst pres compat

    commut→Cα : Comm∼α _→C_
    commut→Cα M∼N (→cxt N▹P) with comm M∼N N▹P
    ... | Q , M▹Q , Q∼P = Q , →cxt M▹Q , Q∼P
    commut→Cα (∼· {M} {M′} {N} {N′} M~M′ N~N′) (→·L M′→M″) with commut→Cα M~M′ M′→M″
    ... | P , M→P , P∼M″ = P · N , →·L M→P , ∼· P∼M″ N~N′
    commut→Cα {M · N} {M′ · N′} {.M′ · N″} (∼· M~M′ N~N′) (→·R N′→N″) with commut→Cα N~N′ N′→N″
    ... | P , N→P , P∼N″ = M · P , →·R N→P , ∼· M~M′ P∼N″
    commut→Cα {λ[ x ∶ A ] M} {λ[ y ∶ B ] N} {λ[ .y ∶ .B ] P} λxM∼λyN@(∼λ {y = z} A∼B z#λxM z#λyN M[z/x]~N[z/y]) (→λR N→P) =
      λ[ x ∶ A ] R′ , →λR (proj₁ (proj₂ r)) , ∼τ λxR∼λyP[y/x] (∼σ (corollary4-2' x#λyP))
      where
      q : Σ[ Q ∈ Λ ](N [ y := v x ] →C Q × Q ∼α P [ y := v x ])
      q = compat→C∙ N→P
      Q : Λ
      Q = proj₁ q
      x#λyN : x ∉ fv N - y 
      x#λyN = ∼α⇒∉- λxM∼λyN 
      open PreR ≈-preorder∼
      M∼N[x/y] : M ∼α N [ y := v x ]
      M∼N[x/y] = begin 
        M
        ∼⟨ lemma∙ι ⟩
        M ∙ ι
        ≈⟨ sym (lemma≺+ι {x} {z} {M} z#λxM) ⟩ 
        M [ x := v z ] [ z := v x ]
        ≈⟨ cong₂ _∙_ M[z/x]~N[z/y] refl ⟩ 
        N [ y := v z ] [ z := v x ]
        ≈⟨ sym (composRenUpd {y} {z} {N} z#λyN) ⟩ 
        N [ y := v x ]
        ∎
      r : Σ[ R ∈ Λ ](M →C R × R ∼α Q)
      r = commut→Cα M∼N[x/y] (proj₁ (proj₂ q))
      R′ : Λ
      R′ = proj₁ r
      λxR∼λyP[y/x] : λ[ x ∶ A ] R′ ∼α λ[ x ∶ B ](P [ y := v x ])
      λxR∼λyP[y/x] = lemma∼λ A∼B (∼τ (proj₂ (proj₂ r)) (proj₂ (proj₂ q)))
      x#λyP : x ∉ fv P - y 
      x#λyP = ∉→C- x#λyN N→P
    commut→Cα {λ[ x ∶ A ] M} {λ[ y ∶ B ] N} {λ[ .y ∶ C ] .N} λxM∼λyN@(∼λ A∼B z#ƛxM z#ƛyN M[z/x]~N[z/y]) (→λL B→C) with commut→Cα A∼B B→C
    ... | D , A→D , B∼D = λ[ x ∶ D ] M , →λL A→D , ∼λ B∼D z#ƛxM z#ƛyN M[z/x]~N[z/y]
    commut→Cα {Π[ x ∶ A ] M} {Π[ y ∶ B ] N} {Π[ .y ∶ .B ] P} ΠxM∼ΠyN@(∼Π {y = z} A∼B z#ΠxM z#ΠyN M[z/x]~N[z/y]) (→ΠR N→P) =
      Π[ x ∶ A ] R′ , →ΠR (proj₁ (proj₂ r)) , ∼τ ΠxR∼ΠyP[y/x] (∼σ (corollary4-2'Π x#ΠyP))
      where
      q : Σ[ Q ∈ Λ ](N [ y := v x ] →C Q × Q ∼α P [ y := v x ])
      q = compat→C∙ N→P
      Q : Λ
      Q = proj₁ q
      x#ΠyN : x ∉ fv N - y 
      x#ΠyN = ∼α⇒∉-Π ΠxM∼ΠyN 
      open PreR ≈-preorder∼
      M∼N[x/y] : M ∼α N [ y := v x ]
      M∼N[x/y] = begin 
        M
        ∼⟨ lemma∙ι ⟩
        M ∙ ι
        ≈⟨ sym (lemma≺+ι {x} {z} {M} z#ΠxM) ⟩ 
        M [ x := v z ] [ z := v x ]
        ≈⟨ cong₂ _∙_ M[z/x]~N[z/y] refl ⟩ 
        N [ y := v z ] [ z := v x ]
        ≈⟨ sym (composRenUpd {y} {z} {N} z#ΠyN) ⟩ 
        N [ y := v x ]
        ∎
      r : Σ[ R ∈ Λ ](M →C R × R ∼α Q)
      r = commut→Cα M∼N[x/y] (proj₁ (proj₂ q))
      R′ : Λ
      R′ = proj₁ r
      ΠxR∼ΠyP[y/x] : Π[ x ∶ A ] R′ ∼α Π[ x ∶ B ](P [ y := v x ])
      ΠxR∼ΠyP[y/x] = lemma∼Π A∼B (∼τ (proj₂ (proj₂ r)) (proj₂ (proj₂ q)))
      x#ΠyP : x ∉ fv P - y 
      x#ΠyP = ∉→C- x#ΠyN N→P
    commut→Cα {Π[ x ∶ A ] M} {Π[ y ∶ B ] N} {Π[ .y ∶ C ] .N} ΠxM∼ΠyN@(∼Π A∼B z#ƛxM z#ƛyN M[z/x]~N[z/y]) (→ΠL B→C) with commut→Cα A∼B B→C
    ... | D , A→D , B∼D = Π[ x ∶ D ] M , →ΠL A→D , ∼Π B∼D z#ƛxM z#ƛyN M[z/x]~N[z/y]


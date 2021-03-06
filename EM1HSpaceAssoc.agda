{-# OPTIONS --without-K --rewriting #-}

open import Base
open import HSpace
open import EM1HSpace
open import EilenbergMacLane1Type
open import EilenbergMacLane1 using (EM₁-level₁)
open import TwoSemiCategoryType
open import GroupType
open import FundamentalCategory
open import Functor
open import DualCategory
open import SuspensionType

module EM1HSpaceAssoc where

module EM₁HSpaceAssoc {i} (G : AbGroup i) where

  private
    module G = AbGroup G
  open EM₁HSpace G public
  private
    module H-⊙EM₁ = HSpaceStructure H-⊙EM₁

  mult-loop-mult : (g : G.El) (y z : EM₁ G.grp)
    → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)
  mult-loop-mult g y z =
    EM₁-prop-elim {P = λ y → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)}
                  {{λ y → has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _}}
                  base' y
    where
    base' : mult-loop g (mult embase z) == ap (λ x' → mult x' z) (mult-loop g embase)
    base' =
      admit {-
      mult-loop g z
        =⟨ ! (app=-β (mult-loop g) z) ⟩
      app= (λ= (mult-loop g)) z
        =⟨ ap (λ s → app= s z) (! (MultRec.emloop-β g)) ⟩
      app= (ap mult (emloop g)) z
        =⟨ ∘-ap (λ f → f z) mult (emloop g) ⟩
      ap (λ x' → mult x' z) (emloop g) =∎
      -}

  H-⊙EM₁-assoc : (x y z : EM₁ G.grp) → mult (mult x y) z == mult x (mult y z)
  H-⊙EM₁-assoc x y z =
    EM₁-set-elim {P = λ x → mult (mult x y) z == mult x (mult y z)}
                 {{λ x → has-level-apply (EM₁-level₁ G.grp) _ _}}
                 idp
                 (comp' x y z)
                 x
    where
      abstract
        comp' : (x y z : EM₁ G.grp) (g : G.El)
          → idp == idp [ (λ x → mult (mult x y) z == mult x (mult y z)) ↓ emloop g ]
        comp' x y z g =
          admit {-
          ↓-='-in $
          idp ∙' ap (λ x → mult x (mult y z)) (emloop g)
            =⟨ ∙'-unit-l _ ⟩
          ap (λ x → mult x (mult y z)) (emloop g)
            =⟨ ap-∘ (λ f → f (mult y z)) mult (emloop g) ⟩
          app= (ap mult (emloop g)) (mult y z)
            =⟨ ap (λ s → app= s (mult y z)) (MultRec.emloop-β g) ⟩
          app= (λ= (mult-loop g)) (mult y z)
            =⟨ app=-β (mult-loop g) (mult y z) ⟩
          mult-loop g (mult y z)
            =⟨ mult-loop-mult g y z ⟩
          ap (λ x' → mult x' z) (mult-loop g y)
            =⟨ ap (ap (λ x' → mult x' z)) (! (app=-β (mult-loop g) y)) ⟩
          ap (λ x' → mult x' z) (app= (λ= (mult-loop g)) y)
            =⟨ ∘-ap (λ x' → mult x' z) (λ f → f y) (λ= (mult-loop g)) ⟩
          ap (λ f → mult (f y) z) (λ= (mult-loop g))
            =⟨ ap (ap (λ f → mult (f y) z)) (! (MultRec.emloop-β g)) ⟩
          ap (λ f → mult (f y) z) (ap mult (emloop g))
            =⟨ ∘-ap (λ f → mult (f y) z) mult (emloop g) ⟩
          ap (λ x → mult (mult x y) z) (emloop g)
            =⟨ ! (∙-unit-r _) ⟩
          ap (λ x → mult (mult x y) z) (emloop g) ∙ idp =∎
          -}

  H-EM₁-assoc-coh-unit-r : coh-unit-r H-⊙EM₁ H-⊙EM₁-assoc
  H-EM₁-assoc-coh-unit-r =
    EM₁-prop-elim {P = λ x → ∀ y → P x y} {{λ x → Π-level (P-level x)}}
      (EM₁-prop-elim {P = P embase} {{P-level embase}} idp)
    where
    P : EM₁ G.grp → EM₁ G.grp → Type i
    P = coh-unit-r-eq H-⊙EM₁ H-⊙EM₁-assoc
    P-level : ∀ x y → has-level (S ⟨-2⟩) (P x y)
    P-level x y = has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _

  H-EM₁-assoc-coh-unit-l-r-pentagon : coh-unit-l-r-pentagon H-⊙EM₁ H-⊙EM₁-assoc
  H-EM₁-assoc-coh-unit-l-r-pentagon =
    coh-unit-r-to-unit-l-r-pentagon H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-coh-unit-r

  import Pi2HSuspCompose {{admit}} {{admit}} H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-coh-unit-l-r-pentagon as Pi2EMSuspCompose
  open Pi2EMSuspCompose -- hiding (comp-functor) public

  abstract
    H-EM₁-assoc-pentagon : coh-assoc-pentagon H-⊙EM₁ H-⊙EM₁-assoc
    H-EM₁-assoc-pentagon w x y z =
      EM₁-prop-elim {P = λ w' → P w' x y z} {{λ w' → P-level w' x y z}}
        (EM₁-prop-elim {P = λ x' → P embase x' y z} {{λ x' → P-level embase x' y z}} idp x)
        w
      where
      P : (w x y z : EM₁ G.grp) → Type i
      P = coh-assoc-pentagon-eq H-⊙EM₁ H-⊙EM₁-assoc
      P-level : ∀ w x y z → has-level (S ⟨-2⟩) (P w x y z)
      P-level w x y z = has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _

  EM₁-2-semi-category : TwoSemiCategory lzero i
  EM₁-2-semi-category = HSpace-2-semi-category H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-pentagon

  comp-functor :
    TwoSemiFunctor
      EM₁-2-semi-category
      (dual-cat (=ₜ-fundamental-cat (Susp (EM₁ G.grp))))
  comp-functor =
    record
    { F₀ = λ _ → [ north ]
    ; F₁ = λ x → [ η x ]
    ; pres-comp = comp
    ; pres-comp-coh = comp-coh
    }
    -- this is *exactly* the same as
    --   `Pi2EMSuspCompose.comp-functor H-EM₁-assoc-pentagon`
    -- inlined but Agda chokes on this shorter definition

{-# OPTIONS --without-K --rewriting #-}

open import Base
open import TwoSemiCategoryType
open import Functor
-- open import FunctorInverse
-- open import GroupToCategory

module FundamentalCategory where

module _ {i} (A : Type i) where

  2-type-fundamental-cat : {{_ : has-level (S (S (S (S ⟨-2⟩)))) A}} → TwoSemiCategory i i
  2-type-fundamental-cat =
    record
    { El = A
    ; Arr = _==_
    ; Arr-level = λ _ _ → admit
    ; two-semi-cat-struct = record
      { comp = _∙_
      ; assoc = λ a b c → ∙-assoc a b c
      ; pentagon-identity = admit -- ∙-assoc-pentagon
      }
    }

  =ₜ-fundamental-cat : TwoSemiCategory i i
  =ₜ-fundamental-cat =
    record
    { El = Trunc (S (S (S (S ⟨-2⟩)))) A
    ; Arr = _=ₜ_
    ; Arr-level = admit -- =ₜ-level
    ; two-semi-cat-struct = record
      { comp = λ {ta} p q → _∙ₜ_ {ta = ta} p q
      ; assoc = λ {ta} p q r → ∙ₜ-assoc {ta = ta} p q r
      ; pentagon-identity = λ {ta} p q r s → admit -- ∙ₜ-assoc-pentagon {ta = ta} p q r s
      }
    }

{-
module _ {i} (A : Type i) where

  =ₜ-equiv-semi-cat-functor
    : TwoSemiFunctor
        (2-type-fundamental-cat (Trunc 2 A))
        (=ₜ-fundamental-cat A)
  =ₜ-equiv-semi-cat-functor =
    record
    { F₀ = idf (Trunc 2 A)
    ; F₁ = λ {ta} {tb} f → –> (=ₜ-equiv ta tb) f
    ; pres-comp = –>-=ₜ-equiv-pres-∙
      -- TODO: The following line takes a really long time to check
      -- Can we optimize this somehow?
    ; pres-comp-coh = λ {ta} p q r → –>-=ₜ-equiv-pres-∙-coh {ta = ta} p q r
    }
    -}

{-
module _ {i} (C : Type i) (c₀ : C) {{C-level : has-level 1 C}} where

  open import lib.groups.LoopSpace

  fundamental-group-to-fundamental-groupoid
    : TwoSemiFunctor (group-to-cat (Ω^S-group 0 ⊙[ C , c₀ ]))
                                (2-type-fundamental-cat C {{raise-level 1 C-level}})
  fundamental-group-to-fundamental-groupoid =
    record
    { F₀ = λ _ → c₀
    ; F₁ = λ p → p
    ; pres-comp = λ p q → idp
    ; pres-comp-coh = λ p q r → prop-path (has-level-apply (has-level-apply C-level _ _) _ _) _ _
    }

module _ {i j} (A : Type i) (B : Type j) {{B-level : has-level 2 B}} where

  open import lib.two-semi-categories.FunCategory

  private

    app=-pres-comp : ∀ {f g h : A → B} (α : f == g) (β : g == h) → app= (α ∙ β) == (λ a → app= α a ∙ app= β a)
    app=-pres-comp α β = λ= (λ a → ap-∙ (λ f → f a) α β)

    abstract
      app=-pres-comp-coh : ∀ {f g h i : A → B} (α : f == g) (β : g == h) (γ : h == i)
        → app=-pres-comp (α ∙ β) γ ∙
          ap (λ s a → s a ∙ app= γ a) (app=-pres-comp α β) ∙
          λ= (λ a → ∙-assoc (app= α a) (app= β a) (app= γ a))
          ==
          ap app= (∙-assoc α β γ) ∙
          app=-pres-comp α (β ∙ γ) ∙
          ap (λ s a → app= α a ∙ s a) (app=-pres-comp β γ)
      app=-pres-comp-coh {f} idp idp γ =
        (app=-pres-comp idp γ ◃∙
         ap (λ s a → s a ∙ app= γ a) (app=-pres-comp idp idp) ◃∙
         λ= (λ a → idp) ◃∎)
          =↯=⟨ 2 & 1 & (_ ∎∎) & ! (λ=-η idp) ⟩
        (app=-pres-comp idp γ ◃∙
         ap (λ s a → s a ∙ app= γ a) (app=-pres-comp idp idp) ◃∎)
          =↯=⟨ 1 & 1 & app=-pres-comp idp γ ◃∎ &
               λ=-ap (λ a t → t ∙ app= γ a) (λ a → ap-∙ (λ f → f a) (idp {a = f}) idp) ⟩
        (app=-pres-comp idp γ ◃∙
         app=-pres-comp idp γ ◃∎)
          =↯=⟨ 1 & 1 & ap (λ s a → s a) (app=-pres-comp idp γ) ◃∎ &
               ! (ap-idf (app=-pres-comp idp γ)) ⟩
        (app=-pres-comp idp γ ◃∙
         ap (λ s a → s a) (app=-pres-comp idp γ) ◃∎) ↯∎

  app=-functor : TwoSemiFunctor (2-type-fundamental-cat (A → B))
                                (fun-cat A (2-type-fundamental-cat B))
  app=-functor =
    record
    { F₀ = idf (A → B)
    ; F₁ = app=
    ; pres-comp = app=-pres-comp
    ; pres-comp-coh = app=-pres-comp-coh
    }

  λ=-functor : TwoSemiFunctor (fun-cat A (2-type-fundamental-cat B))
                              (2-type-fundamental-cat (A → B))
  λ=-functor =
    functor-inverse app=-functor
      (idf-is-equiv _)
      (λ f g → snd app=-equiv)
-}

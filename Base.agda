{-# OPTIONS --without-K --rewriting #-}

module Base where

open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i

infix 30 _==_
data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Path = _==_

{-# BUILTIN EQUALITY _==_ #-}

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Type i} → A → A → Type i

{-# BUILTIN REWRITE _↦_ #-}

postulate
  admit : ∀ {i} {A : Type i} → A

record ⊤ : Type lzero where
  instance constructor unit

Unit = ⊤

{-# BUILTIN UNIT ⊤ #-}

data ℕ : Type lzero where
  O : ℕ
  S : (n : ℕ) → ℕ

Nat = ℕ

{-# BUILTIN NATURAL ℕ #-}

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

module _ {i} {A : Type i} where
  infixr 80 _∙_ _∙'_

  ! : {x y : A} → (x == y → y == x)
  ! idp = idp

  _∙_ : {x y z : A}
    → (x == y → y == z → x == z)
  idp ∙ q = q

  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp _ _ = idp

  ∙'-unit-l : {x y : A} (q : x == y) → idp ∙' q == q
  ∙'-unit-l idp = idp

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

module _ {i} {A : Type i} where

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (lmax i j)
Π A P = (x : A) → P x

infixr 60 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) → (A → B)
cst b = λ _ → b

infixr 80 _∘_

_∘_ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → (B a → Type k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)

-- Application
infixr 0 _$_
_$_ : ∀ {i j} {A : Type i} {B : A → Type j} → (∀ x → B x) → (∀ x → B x)
f $ x = f x

idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x

ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf idp = idp

data TLevel : Type lzero where
  ⟨-2⟩ : TLevel
  S : (n : TLevel) → TLevel

ℕ₋₂ = TLevel

infixl 80 _+2+_
_+2+_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
⟨-2⟩ +2+ n = n
S m +2+ n = S (m +2+ n)

⟨_⟩₋₂ : ℕ → ℕ₋₂
⟨ O ⟩₋₂ = ⟨-2⟩
⟨ S n ⟩₋₂ = S ⟨ n ⟩₋₂

⟨_⟩ : ℕ → ℕ₋₂
⟨ n ⟩ = S (S ⟨ n ⟩₋₂)

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

infix 30 PathOver
syntax PathOver B p u v = u == v [ B ↓ p ]

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  infixr 80 _∙ᵈ_ _∙'ᵈ_ _▹_

  _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙ᵈ_ {p = idp} {p' = idp} q r = q ∙ r

  ∙ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} idp f₁₂ f₂₃ = idp

  _∙ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → p ∙ᵈ q == p' ∙ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (λ r → r ∙ f) α ]
  _∙ᵈᵣ_ {α = idp} idp q = idp

  _∙ᵈₗ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {f : a₁ == a₂} {f' : a₁ == a₂}
    {α : f == f'}
    {q : b₁ == b₂ [ B ↓ f ]} {q' : b₁ == b₂ [ B ↓ f' ]}
    (p : b₀ == b₁ [ B ↓ e ])
    → (β : q == q' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → p ∙ᵈ q == p ∙ᵈ q' [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (λ r → e ∙ r) α ]
  _∙ᵈₗ_ {α = idp} q idp = idp

  _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙' p') ])
  _∙'ᵈ_ {p = idp} {p' = idp} q r = q ∙' r

  _▹_ = _∙'ᵈ_

module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ ap f p ]
  ↓-ap-in {p = idp} idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ↓-cst-in : {x y : A} {p : x == y} {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in {p = idp} q = q

  ↓-cst-in-∙ : {x y z : A} (p : x == y) (q : y == z) {u v w : B}
    (p' : u == v) (q' : v == w)
    → ↓-cst-in {p = p ∙ q} (p' ∙ q')
      == ↓-cst-in {p = p} p' ∙ᵈ ↓-cst-in {p = q} q'
  ↓-cst-in-∙ idp idp idp idp = idp

  ↓-cst-in2 : {a a' : A} {b b' : B}
    {p₀ p₁ : a == a'} {q₀ q₁ : b == b'} {q : p₀ == p₁}
    → q₀ == q₁
    → (↓-cst-in {p = p₀} q₀ == ↓-cst-in {p = p₁} q₁ [ (λ p → b == b' [ (λ _ → B) ↓ p ]) ↓ q ] )
  ↓-cst-in2 {p₀ = idp} {p₁ = .idp} {q = idp} k = k

apd=cst-in : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  {a a' : A} {p : a == a'} {q : f a == f a'}
  → apd f p == ↓-cst-in q → ap f p == q
apd=cst-in {p = idp} x = x

↓-idf=cst-in' : ∀ {i} {A : Type i} {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
  → u == p ∙' v
  → (u == v [ (λ x → x == a) ↓ p ])
↓-idf=cst-in' {p = idp} q = q ∙ ∙'-unit-l _

infix 60 ⊙[_,_]

record Ptd (i : ULevel) : Type (lsucc i) where
  constructor ⊙[_,_]
  field
    de⊙ : Type i
    pt : de⊙
open Ptd public

-- pointed [Σ]
⊙Σ : ∀ {i j} (X : Ptd i) → (de⊙ X → Ptd j) → Ptd (lmax i j)
⊙Σ ⊙[ A , a₀ ] Y = ⊙[ Σ A (de⊙ ∘ Y) , (a₀ , pt (Y a₀)) ]

infixr 0 _⊙→_
_⊙→_ : ∀ {i j} → Ptd i → Ptd j → Type (lmax i j)
⊙[ A , a₀ ] ⊙→ ⊙[ B , b₀ ] = Σ (A → B) (λ f → f a₀ == b₀)

_⊙×_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙× Y = ⊙Σ X (λ _ → Y)

⊙∘-pt : ∀ {i j} {A : Type i} {B : Type j}
  {a₁ a₂ : A} (f : A → B) {b : B}
  → a₁ == a₂ → f a₂ == b → f a₁ == b
⊙∘-pt f p q = ap f p ∙ q

infixr 80 _⊙∘_
_⊙∘_ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y) → X ⊙→ Z
(g , gpt) ⊙∘ (f , fpt) = (g ∘ f) , ⊙∘-pt g fpt gpt

⊙×-inl : ∀ {i j} (X : Ptd i) (Y : Ptd j) → X ⊙→ X ⊙× Y
⊙×-inl X Y = (λ x → x , pt Y) , idp

⊙×-inr : ∀ {i j} (X : Ptd i) (Y : Ptd j) → Y ⊙→ X ⊙× Y
⊙×-inr X Y = (λ y → pt X , y) , idp

⊙idf : ∀ {i} (X : Ptd i) → X ⊙→ X
⊙idf X = (λ x → x) , idp

infixr 30 _∼_ _⊙∼_
_∼_ : ∀ {i j} {A : Type i} {B : A → Type j}
  (f g : (a : A) → B a) → Type (lmax i j)
f ∼ g = ∀ x → f x == g x

_⊙∼_ : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  (f g : X ⊙→ Y) → Type (lmax i j)
_⊙∼_ {X = X} {Y = Y} (f , f-pt) (g , g-pt) =
  Σ (f ∼ g) λ p → f-pt == g-pt [ (_== pt Y) ↓ p (pt X) ]

module _ {i} where

  {- Definition of contractible types and truncation levels -}

  -- We define `has-level' as a record, so that it does not unfold when
  -- applied to (S n), in order for instance arguments to work correctly
  -- (idea by Dan Licata)
  record has-level (n : ℕ₋₂) (A : Type i) : Type i

  has-level-aux : ℕ₋₂ → (Type i → Type i)
  has-level-aux ⟨-2⟩ A = Σ A (λ x → ((y : A) → x == y))
  has-level-aux (S n) A = (x y : A) → has-level n (x == y)

  record has-level n A where
    -- Agda notices that the record is recursive, so we need to specify that we want eta-equality
    inductive
    eta-equality
    constructor has-level-in
    field
      has-level-apply : has-level-aux n A
  open has-level public

  is-contr = has-level ⟨-2⟩
  -- is-prop = has-level -1
  -- is-set  = has-level 0

module _ {i} where

  postulate  -- HIT
    Trunc : (n : ℕ₋₂) (A : Type i) → Type i
    [_] : {n : ℕ₋₂} {A : Type i} → A → Trunc n A
    instance Trunc-level : {n : ℕ₋₂} {A : Type i} → has-level n (Trunc n A)

  module TruncElim {n : ℕ₋₂} {A : Type i} {j} {P : Trunc n A → Type j}
    {{p : (x : Trunc n A) → has-level n (P x)}} (d : (a : A) → P [ a ]) where

    postulate  -- HIT
      f : Π (Trunc n A) P
      [_]-β : ∀ a → f [ a ] ↦ d a
    {-# REWRITE [_]-β #-}

open TruncElim public renaming (f to Trunc-elim)

module TruncRec {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {{p : has-level n B}}
  (d : A → B) where

  private
    module M = TruncElim {{λ x → p}} d

  f : Trunc n A → B
  f = M.f

open TruncRec public renaming (f to Trunc-rec)

module _ {i} {A : Type i} where

  [_]₁ : A → Trunc (S (S (S ⟨-2⟩))) A
  [_]₁ a = [_] {n = S (S (S ⟨-2⟩))} a

module _ {i} (A : Type i) where
  SubtypeProp : ∀ j → Type (lmax i (lsucc j))
  SubtypeProp j = Σ (A → Type j) (λ P → ∀ a → has-level (S ⟨-2⟩) (P a))

module SubtypeProp {i j} {A : Type i} (P : SubtypeProp A j) where
  prop = fst P
  level = snd P

module _ {i j} {A : Type i} (P : SubtypeProp A j) where
  private
    module P = SubtypeProp P

  Subtype : Type (lmax i j)
  Subtype = Σ A P.prop

has-level-prop : ∀ {i} → ℕ₋₂ → SubtypeProp (Type i) i
has-level-prop n = has-level n , admit -- λ _ → has-level-is-prop

_-Type_ : (n : ℕ₋₂) (i : ULevel) → Type (lsucc i)
n -Type i = Subtype (has-level-prop {i} n)

Π-level : ∀ {i j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
  → ((x : A) → has-level n (B x)) → has-level n (Π A B)
Π-level p = admit

module _ {i j} {A : Type i} {P : A → Type j} {f g : Π A P} (h : f ∼ g) where

  λ= : f == g
  λ= = admit

module _ {i j} {A : Type i} {P : A → Type j} where

  app= : ∀ {f g : Π A P} (p : f == g) → f ∼ g
  app= p x = ap (λ u → u x) p

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  hfiber : (y : B) → Type (lmax i j)
  hfiber y = Σ A (λ x → f x == y)

Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} → ((A → B) → (Trunc n A → Trunc n B))
Trunc-fmap f = Trunc-rec ([_] ∘ f)

Trunc-fmap2 : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → ((A → B → C) → (Trunc n A → Trunc n B → Trunc n C))
Trunc-fmap2 f = Trunc-rec {{admit}} (λ a → Trunc-fmap (f a))

module _ {i} {n : ℕ₋₂} {A : Type i} where

  private
    Trunc= : (a b : Trunc (S n) A) → n -Type i
    Trunc= = Trunc-elim {{admit}} (λ a → Trunc-elim {{admit}} ((λ b → (Trunc n (a == b) , Trunc-level))))

  {- t is for truncated -}
  _=ₜ_ : (a b : Trunc (S n) A) → Type i
  _=ₜ_ a b = fst (Trunc= a b)

  {- concatenation in _=ₜ_ -}
  _∙ₜ_ : {ta tb tc : Trunc (S n) A}
    → ta =ₜ tb → tb =ₜ tc → ta =ₜ tc
  _∙ₜ_ {ta = ta} {tb = tb} {tc = tc} =
    Trunc-elim {P = λ ta → C ta tb tc}
      {{λ ta → level ta tb tc}}
      (λ a → Trunc-elim {P = λ tb → C [ a ] tb tc}
        {{λ tb → level [ a ] tb tc}}
        (λ b → Trunc-elim {P = λ tc → C [ a ] [ b ] tc}
          {{λ tc → level [ a ] [ b ] tc}}
          (λ c → Trunc-fmap2 _∙_)
        tc)
      tb)
    ta
    where
    C : (ta tb tc : Trunc (S n) A) → Type i
    C ta tb tc = ta =ₜ tb → tb =ₜ tc → ta =ₜ tc
    level : (ta tb tc : Trunc (S n) A) → has-level (S n) (C ta tb tc)
    level ta tb tc = admit {-raise-level _ $
      Π-level (λ _ → Π-level (λ _ → =ₜ-level ta tc))-}

  ∙ₜ-assoc : {ta tb tc td : Trunc (S n) A}
    (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td)
    → _∙ₜ_ {ta} (_∙ₜ_ {ta} tp tq) tr
      == _∙ₜ_ {ta} tp (_∙ₜ_ {tb} tq tr)
  ∙ₜ-assoc {ta = ta} {tb = tb} {tc = tc} {td = td} =
    Trunc-elim {P = λ ta → C ta tb tc td}
      {{λ ta → C-level ta tb tc td}}
      (λ a → Trunc-elim {P = λ tb → C [ a ] tb tc td}
        {{λ tb → C-level [ a ] tb tc td}}
        (λ b → Trunc-elim {P = λ tc → C [ a ] [ b ] tc td}
          {{λ tc → C-level [ a ] [ b ] tc td}}
          (λ c → Trunc-elim {P = λ td → C [ a ] [ b ] [ c ] td}
            {{λ td → C-level [ a ] [ b ] [ c ] td}}
            (λ d tp tq tr → Trunc-elim
              {P = λ tp → D [ a ] [ b ] [ c ] [ d ] tp tq tr}
              {{λ tp → D-level [ a ] [ b ] [ c ] [ d ] tp tq tr}}
              (λ p → Trunc-elim
                {P = λ tq → D [ a ] [ b ] [ c ] [ d ] [ p ] tq tr}
                {{λ tq → D-level [ a ] [ b ] [ c ] [ d ] [ p ] tq tr}}
                (λ q → Trunc-elim
                  {P = λ tr → D [ a ] [ b ] [ c ] [ d ] [ p ] [ q ] tr}
                  {{λ tr → D-level [ a ] [ b ] [ c ] [ d ] [ p ] [ q ] tr}}
                  (λ r → ap [_] (∙-assoc p q r))
                  tr)
                tq)
              tp)
            td)
          tc)
        tb)
      ta
    where
    D : (ta tb tc td : Trunc (S n) A)
      → ta =ₜ tb → tb =ₜ tc → tc =ₜ td
      → Type i
    D ta tb tc td tp tq tr =
         _∙ₜ_ {ta} (_∙ₜ_ {ta} tp tq) tr
      == _∙ₜ_ {ta} tp (_∙ₜ_ {tb} tq tr)
    C : (ta tb tc td : Trunc (S n) A) → Type i
    C ta tb tc td = ∀ tp tq tr → D ta tb tc td tp tq tr
    D-level : (ta tb tc td : Trunc (S n) A)
      (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td)
      → has-level n (D ta tb tc td tp tq tr)
    D-level ta tb tc td tp tq tr = admit -- =-preserves-level (=ₜ-level ta td)
    C-level : (ta tb tc td : Trunc (S n) A) → has-level (S n) (C ta tb tc td)
    C-level ta tb tc td =
      admit
      -- raise-level _ $
      -- Π-level $ λ tp →
      -- Π-level $ λ tq →
      -- Π-level $ λ tr →
      -- D-level ta tb tc td tp tq tr

module Verse.Core where

open import Verse.Prelude

-- ** Core Verse calculus

data Primop : Type where
  gt add ♯map : Primop

Var = String

mutual
  Values = List Value

  data Value : Type where
    𝕧 : Var → Value
    𝕜 : ℕ → Value
    ♯ : Primop → Value
    ⟨_⟩ : Values → Value
    `ƛ_⇒_ : Var → ≠Expr → Value
  -- data Value : Type where
  --   𝕧 : Var → Value
  --   𝕜 : ℕ → Value
  --   ♯ : Primop → Value
  --   ⟨_⟩ : Values → Value
  --   ƛ_⇒_ : Var → Expr → Value

  data Expr : Type where
    `_ : Value → Expr
    _`⨾_ : Expr → ≠Expr → Expr
    `∃_⇒_ : Var → ≠Expr → Expr
    fail : Expr
    _`∣_ : ≠Expr → ≠Expr → Expr
    _·_ : Value → Value → Expr
    `one⦅_⦆ `all⦅_⦆ : ≠Expr → Expr
    _`＝_ : Value → ≠Expr → Expr
  -- data Expr : Type where
  --   `_ : Value → Expr
  --   _⨾_ : ＝Expr → Expr → Expr
  --   ∃_⇒_ : Var → Expr → Expr
  --   fail : Expr
  --   _∣_ : Expr → Expr → Expr
  --   _·_ : Value → Value → Expr
  --   one⦅_⦆ all⦅_⦆ : Expr → Expr

  ≠_ : Pred₀ Expr
  ≠_ = λ where
    (_ `＝ _) → ⊥
    -- (e `⨾ _) → ≠ e
    _ → ⊤

  ≠Expr = ∃ ≠_

  -- data ＝Expr : Type where
  --   _＝_ : Value → Expr → ＝Expr
  --   ≠_ : Expr → ＝Expr

infixr 2 `∃_⇒_ ∃_⇒_ `ƛ_⇒_ ƛ_⇒_
infixr 3 _`∣_ _∣_
infixr 4 _`⨾_ _⨾_
infix  5 _`＝_ _＝_ _＝`_
-- infixr 2 ∃_⇒_ ƛ_⇒_
-- infixr 3 _∣_
-- infixr 4 _⨾_
-- infix  5 _＝_ _＝`_
-- pattern _＝`_ v v′ = v ＝ ` v′

ƛ_⇒_ : Var → (e : Expr) ⦃ _ : ≠ e ⦄ → Value
ƛ x ⇒ e = `ƛ x ⇒ (e , it)

_⨾_ : (e e′ : Expr) ⦃ _ : ≠ e′ ⦄ → Expr
e ⨾ e′ = e `⨾ (e′ , it)

∃_⇒_ : Var → (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
∃ x ⇒ e = `∃ x ⇒ (e , it)

_∣_ : (e e′ : Expr) ⦃ _ : ≠ e ⦄ ⦃ _ : ≠ e′ ⦄ → Expr
e ∣ e′ = (e , it) `∣ (e′ , it)

one⦅_⦆ all⦅_⦆ : (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
one⦅ e ⦆ = `one⦅ e , it ⦆
all⦅ e ⦆ = `all⦅ e , it ⦆

_＝_ : Value → (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
v ＝ e = v `＝ (e , it)

_＝`_ : Value → Value → Expr
v ＝` v′ = v `＝ (` v′ , it)

pattern `𝕧 x = ` 𝕧 x
pattern `𝕜 x = ` 𝕜 x
pattern 𝕜0 = 𝕜 0; pattern 𝕜1 = 𝕜 1; pattern 𝕜2 = 𝕜 2; pattern 𝕜3 = 𝕜 3
pattern `⟨_⟩ x = ` ⟨ x ⟩
pattern ⟨⟩ = ⟨ [] ⟩
pattern `⟨⟩ = ` ⟨⟩

_ : Expr
_ = ∃ "x" ⇒ (∃ "y" ⇒ `⟨ ⟦ 𝕜2    , 𝕧 "y" ⟧ ⟩) ⨾
            (∃ "z" ⇒ `⟨ ⟦ 𝕧 "y" , 𝕜3    ⟧ ⟩) ⨾
            `𝕧 "x"

module Verse.Helpers where

open import Verse.Prelude
open import Verse.Core

-- ** syntactic categories of terms

isConstant isScalar isTup isHeap isHead : Pred₀ Value
isConstant = λ where
  (𝕜 _) → ⊤
  _ → ⊥
isScalar = λ where
  (𝕧 _) → ⊤
  (𝕜 _) → ⊤
  (♯ _) → ⊤
  _ → ⊥
isTup = λ where
  ⟨ _ ⟩ → ⊤
  _ → ⊥
isHeap = λ where
  ⟨ _ ⟩ → ⊤
  (`ƛ _ ⇒ _) → ⊤
  _ → ⊥
-- isHead = isHeap Unary.∪ isConstant
isHead = λ where
  ⟨ _ ⟩ → ⊤
  (`ƛ _ ⇒ _) → ⊤
  (𝕜 _) → ⊤
  _ → ⊥

isConstant? = Decidable¹ isConstant ∋ λ where
  (𝕜 _) → yes tt
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
  ⟨ _ ⟩ → no λ ()
  (`ƛ _ ⇒ _) → no λ ()
  -- (ƛ _ ⇒ _) → no λ ()
isScalar? = Decidable¹ isScalar ∋ λ where
  (𝕧 _) → yes tt
  (𝕜 _) → yes tt
  (♯ _) → yes tt
  ⟨ _ ⟩ → no λ ()
  (`ƛ _ ⇒ _) → no λ ()
  -- (ƛ _ ⇒ _) → no λ ()
isTup? = Decidable¹ isTup ∋ λ where
  ⟨ _ ⟩ → yes tt
  (𝕜 _) → no λ ()
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
  (`ƛ _ ⇒ _) → no λ ()
  -- (ƛ _ ⇒ _) → no λ ()
isHeap? = Decidable¹ isHeap ∋ λ where
  ⟨ _ ⟩ → yes tt
  (`ƛ _ ⇒ _) → yes tt
  -- (ƛ _ ⇒ _) → yes tt
  (𝕜 _) → no λ ()
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()
isHead? = Decidable¹ isHead ∋ λ where
  ⟨ _ ⟩ → yes tt
  (`ƛ _ ⇒ _) → yes tt
  -- (ƛ _ ⇒ _) → yes tt
  (𝕜 _) → yes tt
  (𝕧 _) → no λ ()
  (♯ _) → no λ ()

-- ** utilities

variable
  e e′ e₁ e₂ eu : Expr
  -- eu eu′ : ＝Expr
  v v₁ v₂ v₁′ v₂′ : Value
  vs : Values
  s s′ : Value
  hnf hnf₁ hnf₂ : Value
  x y : Var
  k₁ k₂ n : ℕ

eu≠_ : Pred₀ Expr
eu≠_ = λ where
  (𝕧 _ `＝ (` _ , _)) → ⊥
  _ → ⊤

≠[] : Pred₀ (List A)
≠[] = λ where
  [] → ⊥
  (_ ∷ _) → ⊤

mutual
  ∣⁺_ : (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
  ∣⁺_ = λ where
    (v ∷ []) → ` v
    (v ∷ vs@(_ ∷ _)) → ` v ∣ ∣⁺ vs

  instance
    ∣⁺-≠[] : ⦃ _ : ≠[] vs ⦄ → ≠ (∣⁺ vs)
    ∣⁺-≠[] {_ ∷ []} = tt
    ∣⁺-≠[] {_ ∷ _ ∷ _} = tt
-- ∣⁺_ : (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
-- ∣⁺_ = λ where
--   (v ∷ []) → ` v
--   (v ∷ vs@(_ ∷ _)) → ` v ∣ ∣⁺ vs

mutual
  enum-∣ : Var → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
  enum-∣ x vs = go 0 vs
    where mutual
      go : ℕ → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
      go i = let x＝i = 𝕧 x ＝` 𝕜 i in λ where
        (v ∷ []) → x＝i ⨾ ` v
        (v ∷ vs@(_ ∷ _)) → x＝i ⨾ ` v ∣ go (suc i) vs

      instance
        go-≠[] : ∀ {vs : Values} ⦃ _ : ≠[] vs ⦄ → ≠ (go n vs)
        go-≠[] {vs = _ ∷ []}    = tt
        go-≠[] {vs = _ ∷ _ ∷ _} = tt

  instance
    enum-∣-≠[] : ⦃ _ : ≠[] vs ⦄ → ≠ (enum-∣ x vs)
    enum-∣-≠[] {_ ∷ []} = tt
    enum-∣-≠[] {_ ∷ _ ∷ _} = tt
-- enum-∣ : Var → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
-- enum-∣ x vs = go 0 vs
--   where
--     go : ℕ → (vs : Values) ⦃ _ : ≠[] vs ⦄ → Expr
--     go i = let x＝i = 𝕧 x ＝` 𝕜 i in λ where
--       (v ∷ []) → x＝i ⨾ ` v
--       (v ∷ vs@(_ ∷ _)) → x＝i ⨾ ` v ∣ go (suc i) vs


-- ** free variables

record HasVars (A : Type) : Type where
  field fv : A → List Var
  fvs : List A → List Var
  fvs = concatMap fv
open HasVars ⦃...⦄ public

freeIn : ⦃ _ : HasVars A ⦄ → A → Var
freeIn a = "$" Str.++ Str.concat (fv a)

mutual instance
  hv : HasVars Var
  hv .fv x = x ∷ []

  hv× : ⦃ HasVars A ⦄ → ⦃ ∀ {a} → HasVars (P a) ⦄ → HasVars (Σ A P)
  hv× .fv (a , b) = fv a ++ fv b

  hv≠ : HasVars (≠ e)
  hv≠ .fv _ = []

  {-# TERMINATING #-}
  hve : HasVars Expr
  hve .fv = λ where
    (` _) → []
    (e `⨾ e′) → fv (e , e′)
    (`∃ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)
    fail → []
    (e `∣ e′) → fv (e , e′)
    (v · v′) → fv (v , v′)
    `one⦅ e ⦆ → fv e
    `all⦅ e ⦆ → fv e
    (v `＝ e) → fv (v , e)
  -- {-# TERMINATING #-}
  -- hve : HasVars Expr
  -- hve .fv = λ where
  --   (` _) → []
  --   (e ⨾ e′) → fv (e , e′)
  --   (∃ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)
  --   fail → []
  --   (e ∣ e′) → fv (e , e′)
  --   (v · v′) → fv (v , v′)
  --   one⦅ e ⦆ → fv e
  --   all⦅ e ⦆ → fv e

  -- hv＝e : HasVars ＝Expr
  -- hv＝e .fv = λ where
  --   (v ＝ e) → fv (v , e)
  --   (≠ e) → fv e

  hvv : HasVars Value
  hvv .fv = λ where
    (𝕧 x) → x ∷ []
    (𝕜 _) → []
    (♯ _) → []
    ⟨ vs ⟩ → fvs vs
    (`ƛ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)
    -- (ƛ x ⇒ e) → filter (¬? ∘ (_≟ x)) (fv e)

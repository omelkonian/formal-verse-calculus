module Verse.Context where

open import Verse.Prelude
open import Verse.Core
open import Verse.Helpers

∣-free : Pred₀ Expr
∣-free = λ where
  (_ `∣ _) → ⊥
  (e `⨾ (e′ , _)) → ∣-free e × ∣-free e′
  (`∃ _ ⇒ (e , _)) → ∣-free e
  `one⦅ e , _ ⦆ → ∣-free e
  `all⦅ e , _ ⦆ → ∣-free e
  (_ `＝ (e , _)) → ∣-free e
  _ → ⊤

data EP : Type where
  ∗ ？ : EP
variable ep : EP

⟦_⟧ᵉᵖ : EP → Pred₀ Expr
⟦_⟧ᵉᵖ = λ where
  ∗ → const ⊤
  ？ → ≠_

mutual
  data CX : EP → Type where
    ∙ : CX ∗
    _＝∙_ : Value → ≠CX ep → CX ？
    _∙⨾_ : CX ep → ≠Expr → CX ep
    _⨾∙_ : (ce : Expr) ⦃ _ : ∣-free ce ⦄ → ≠→∙CX ep → CX ep
    ∃_⇒∙_ : Var → ≠CX ep → CX ？

  ≠ᵉᵖ_ ≠→∙_ : Pred₀ (CX ep)
  ≠ᵉᵖ_ = λ where
    (_ ＝∙ _) → ⊥
    _ → ⊤
  ≠→∙_ {ep = ep} = λ where
    (_ ＝∙ _) → ⊥
    ∙ → ep ≡ ？
    _ → ⊤

  ≠CX ≠→∙CX : EP → Type
  ≠CX ep = Σ (CX ep) ≠ᵉᵖ_
  ≠→∙CX ep = Σ (CX ep) ≠→∙_

variable cx cx′ : CX ep

≠∙_ : Pred₀ (CX ep)
≠∙_ = λ where
  ∙ → ⊥
  _ → ⊤

weakenCX : ⟦ ？ ⟧ᵉᵖ e → ⟦ ep ⟧ᵉᵖ e
weakenCX {ep = ∗} = const tt
weakenCX {ep = ？} = id

mutual
  _[_] : (cx : CX ep) → (e : Expr) ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ → Expr
  _[_] ∙ e = e
  _[_] (_＝∙_ {ep} x (cx , ≠cx)) e
    = x `＝ (cx [ e ] , cx-≠ ⦃ ≠cx ⦄)
    where instance _ = weakenCX {ep = ep} it
  _[_] (cx ∙⨾ e′) e
      = cx [ e ] `⨾ e′
  _[_] (ce ⨾∙ (cx , ≠cx)) e
    = ce `⨾ cx [ e ] , cx≠ ≠cx
  _[_] (∃_⇒∙_ {ep} x (cx , ≠cx)) e
    = `∃ x ⇒ (cx [ e ] , cx-≠ ⦃ ≠cx ⦄)
    where instance _ = weakenCX {ep = ep} it

  cx≠′ : {cx : CX ep} ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ ⦃ _ : ≠ᵉᵖ cx ⦄
       → (≠∙ cx) ⊎ (≠ e)
       → ≠ (cx [ e ])
  cx≠′ {cx = ∙} (inj₂ ≠e) = ≠e
  cx≠′ {cx = cx ∙⨾ x} p = tt
  cx≠′ {cx = ce ⨾∙ x} p = tt
  cx≠′ {cx = ∃ x ⇒∙ x₁} p = tt

  cx≠ : {cx : CX ep} ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ → ≠→∙ cx → ≠ (cx [ e ])
  cx≠ {cx = cx ∙⨾ x} p = tt
  cx≠ {cx = ce ⨾∙ x} p = tt
  cx≠ {cx = ∃ x ⇒∙ x₁} p = tt

  cx-≠ : {cx : CX ep} ⦃ _ : ≠ᵉᵖ cx ⦄
        → ⦃ _ : ⟦ ep ⟧ᵉᵖ e ⦄ ⦃ _ : ≠ e ⦄
        → ≠ (cx [ e ])
  cx-≠ {cx = cx} ⦃ _ ⦄ ⦃ _ ⦄ ⦃ ≠e ⦄ with cx
  ... | ∙        = ≠e
  ... | _   ∙⨾ _ = tt
  ... | _   ⨾∙ _ = tt
  ... | ∃ _ ⇒∙ _ = tt

-- mutual
--   data ∅Expr : Type where
--     `_ : Value → ∅Expr
--     _⨾_ : ＝∅Expr → ∅Expr → ∅Expr
--     one⦅_⦆ all⦅_⦆ : ∅Expr → ∅Expr
--     _⦅_⦆ : Primop → Value → ∅Expr
--     ∃_⇒_ : Var → ∅Expr → ∅Expr
--   data ＝∅Expr : Type where
--     _＝_ : Value → ∅Expr → ＝∅Expr
--     ≠_ : ∅Expr → ＝∅Expr

-- mutual
--   data CX : Type where
--     ∙ : CX
--     _∙⨾_ : ＝CX → Expr → CX
--     _⨾∙_ : ＝∅Expr → CX → CX
--     ∃_⇒∙_ : Var → CX → CX

--   data ＝CX : Type where
--     ≠_ : CX → ＝CX
--     _＝∙_ : Value → CX → ＝CX

-- variable cx cx′ : CX

-- _≠∙ : Pred₀ CX
-- _≠∙ = λ where ∙ → ⊥; _ → ⊤

-- mutual
--   ∅→ : ∅Expr → Expr
--   ∅→ = λ where
--     (` v) → (` v)
--     (e ⨾ e′) → ∅→＝ e ⨾ ∅→ e′
--     one⦅ e ⦆ → ∅→ e
--     all⦅ e ⦆ → ∅→ e
--     (op ⦅ v ⦆) → ♯ op · ⟨ v ∷ [] ⟩
--     (∃ x ⇒ e) → ∃ x ⇒ ∅→ e

--   ∅→＝ : ＝∅Expr → ＝Expr
--   ∅→＝ = λ where
--     (v ＝ e) → v ＝ ∅→ e
--     (≠ e) → ≠ (∅→ e)

-- mutual
--   _[_] : CX → Expr → Expr
--   ∙ [ e ] = e
--   (cx ∙⨾ e′) [ e ] = cx ＝[ e ] ⨾ e′
--   (ce ⨾∙ cx) [ e ] = ∅→＝ ce ⨾ cx [ e ]
--   (∃ x ⇒∙ cx) [ e ] = ∃ x ⇒ cx [ e ]

--   _＝[_] : ＝CX → Expr → ＝Expr
--   (≠ cx) ＝[ e ] = ≠ (cx [ e ])
--   (v ＝∙ cx) ＝[ e ] = v ＝ (cx [ e ])

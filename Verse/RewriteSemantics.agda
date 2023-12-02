module Verse.RewriteSemantics where

open import Verse.Prelude
open import Verse.Core
open import Verse.Helpers
open import Verse.Context

infix 0 _—→_
data _—→_ : Rel Expr 0ℓ where

  U-SCALAR : ⦃ _ : ≠ e ⦄ ⦃ _ : isConstant s ⦄ →
    s ＝` s ⨾ e —→ e

  U-TUP : ⦃ _ : ≠ e ⦄ →
    ⟨ ⟦ v₁ , v₂ ⟧ ⟩ ＝` ⟨ ⟦ v₁′ , v₂′ ⟧ ⟩ ⨾ e —→ v₁ ＝` v₁′ ⨾ v₂ ＝` v₂′ ⨾ e

  U-FAIL : ⦃ _ : isHead hnf₁ ⦄ ⦃ _ : isHead hnf₂ ⦄ →
    ∙ ¬ (∃ λ s → (hnf₁ ≡ 𝕜 s) × (hnf₂ ≡ 𝕜 s)) -- no U-SCALAR match
    ∙ ¬ (isTup hnf₁ × isTup hnf₂) -- no U-TUP match
      ─────────────────────
      hnf₁ ＝` hnf₂ —→ fail

  -- Application: 𝓐

  APP-BETA : ⦃ _ : ≠ e ⦄ →
    x ∉ fv v
    ────────
    (ƛ x ⇒ e) · v —→ ∃ x ⇒ 𝕧 x ＝` v ⨾ e

  APP-TUP₀ :
    ⟨⟩ · v —→ fail

  APP-TUP : ⦃ _ : ≠[] vs ⦄ →
    x ∉ fv v
    ────────
    ⟨ vs ⟩ · v —→ ∃ x ⇒ 𝕧 x ＝` v ⨾ enum-∣ x vs

  APP-ADD :
    (♯ add) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ `𝕜 (k₁ + k₂)

  APP-GT : {auto∶ k₁ > k₂} →
    (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ `𝕜 k₁

  APP-GT-FAIL : {auto∶ k₁ ≤ k₂} →
    (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ —→ fail

  -- Normalization: 𝓝

  NORM-VAL : ⦃ _ : ≠ e ⦄ →
    ` v ⨾ e —→ e

  NORM-SEQ-ASSOC : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    (eu ⨾ e₁) ⨾ e₂ —→ eu ⨾ (e₁ ⨾ e₂)

  NORM-SEQ-SWAP₁ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
    eu ⨾ (𝕧 x ＝` v ⨾ e) —→ 𝕧 x ＝` v ⨾ (eu ⨾ e)

  -- NORM-SEQ-SWAP₂ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
  --   eu ⨾ (𝕧 x ＝` s ⨾ e) —→ 𝕧 x ＝` s ⨾ (eu ⨾ e)

  NORM-EQ-SWAP : ⦃ _ : isHead hnf ⦄ →
    hnf ＝` 𝕧 x —→ 𝕧 x ＝` hnf

  NORM-SEQ-DEFR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    x ∉ fv e₂
    ─────────
    (∃ x ⇒ e₁) ⨾ e₂ —→ ∃ x ⇒ (e₁ ⨾ e₂)

  NORM-SEQ-DEFL : ⦃ _ : ≠ e ⦄ →
    x ∉ fv eu
    ─────────
    eu ⨾ (∃ x ⇒ e) —→ ∃ x ⇒ (eu ⨾ e)

  NORM-DEFR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    y ∉ fv (v , e₂)
    ───────────────
    v ＝ (∃ y ⇒ e₁) ⨾ e₂ —→ ∃ y ⇒ v ＝ e₁ ⨾ e₂

  NORM-SEQR : ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄ →
    v ＝ (eu ⨾ e₁) ⨾ e₂ —→ eu ⨾ v ＝ e₁ ⨾ e₂

  -- one

  ONE-FAIL :
    one⦅ fail ⦆ —→ fail

  ONE-CHOICE : ⦃ _ : ≠ e₂ ⦄ →
    one⦅ ` v₁ ∣ e₂ ⦆ —→ ` v₁

  ONE-VALUE :
    one⦅ ` v ⦆ —→ ` v

  -- all

  ALL-FAIL :
    all⦅ fail ⦆ —→ `⟨⟩

  ALL-CHOICE : ⦃ _ : ≠[] vs ⦄ →
    all⦅ ∣⁺ vs ⦆ —→ `⟨ vs ⟩

  -- choice

  CHOOSE : {cx : CX ep} ⦃ _ : ≠ᵉᵖ cx ⦄ ⦃ _ : ≠∙ cx ⦄ ⦃ _ : ≠ e₁ ⦄ ⦃ _ : ≠ e₂ ⦄
    ⦃ _ : ⟦ ep ⟧ᵉᵖ e₁ ⦄ ⦃ _ : ⟦ ep ⟧ᵉᵖ e₂ ⦄
    ⦃ _ : ⟦ ep ⟧ᵉᵖ (e₁ ∣ e₂) ⦄
    →
    cx [ e₁ ∣ e₂ ] —→ _`∣_ ((cx [ e₁ ]) , cx-≠ {ep = ep}) ((cx [ e₂ ]) , (cx-≠ {ep = ep})) -- _∣_ (cx [ e₁ ]) (cx [ e₂ ])

-- _—↛⟨U-SCALAR⟩_ _—↛⟨U-TUP⟩_ : Rel₀ Value
-- _—↛⟨U-SCALAR⟩_ = λ where
--   (𝕜 s) (𝕜 s′) → s ≡ s′
--   _ _ → ⊥
-- v —↛⟨U-TUP⟩ v′ = isTup v × isTup v′

-- _—↛⟨U-SCALAR⟩?_ : Decidable² _—↛⟨U-SCALAR⟩_
-- _—↛⟨U-SCALAR⟩?_ = λ where
--   (𝕜 s) → λ where
--     (𝕜 s′) → s ≟ s′
--     (𝕧 _) → no λ ()
--     (♯ _) → no λ ()
--     ⟨ _ ⟩ → no λ ()
--     (ƛ _ ⇒ _) → no λ ()
--   (𝕧 _) _ → no λ ()
--   (♯ _) _ → no λ ()
--   ⟨ _ ⟩ _ → no λ ()
--   (ƛ _ ⇒ _) _ → no λ ()

-- _—↛⟨U-TUP⟩?_ : Decidable² _—↛⟨U-TUP⟩_
-- v —↛⟨U-TUP⟩? v′
--   with isTup? v
-- ... | no ¬tv = no (¬tv ∘ proj₁)
-- ... | yes tv
--   with isTup? v′
-- ... | no ¬tv′ = no (¬tv′ ∘ proj₂)
-- ... | yes tv′ = yes (tv , tv′)

-- mutual
--   infix 0 _—→_ _≠—→≠_

--   data _≠—→≠_ : Rel₀ Expr where

--     U-SCALAR : ⦃ _ : isConstant s ⦄ →
--       s ＝` s ⨾ e
--       ≠—→≠
--       e

--     U-TUP :
--       ⟨ ⟦ v₁ , v₂ ⟧ ⟩ ＝` ⟨ ⟦ v₁′ , v₂′ ⟧ ⟩ ⨾ e
--       ≠—→≠
--       (v₁ ＝` v₁′ ⨾ v₂ ＝` v₂′ ⨾ e)

--     -- Application: 𝓐

--     APP-BETA :
--       x ∉ fv v
--       ────────
--       ((ƛ x ⇒ e) · v) ≠—→≠ (∃ x ⇒ 𝕧 x ＝` v ⨾ e)

--     APP-TUP₀ :
--       (⟨⟩ · v) ≠—→≠ fail

--     APP-TUP : ⦃ _ : ≠[] vs ⦄ →
--       x ∉ fv v
--       ────────
--       ⟨ vs ⟩ · v ≠—→≠ ∃ x ⇒ 𝕧 x ＝` v ⨾ enum-∣ x vs

--     APP-ADD :
--       (♯ add) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ `𝕜 (k₁ + k₂)

--     APP-GT : {auto∶ k₁ > k₂} →
--       (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ `𝕜 k₁

--     APP-GT-FAIL : {auto∶ k₁ ≤ k₂} →
--       (♯ gt) · ⟨ ⟦ 𝕜 k₁ , 𝕜 k₂ ⟧ ⟩ ≠—→≠ fail

--     -- Normalization: 𝓝

--     NORM-VAL :
--       ≠ (` v) ⨾ e ≠—→≠ e

--     NORM-SEQ-ASSOC :
--       ≠ (eu ⨾ e₁) ⨾ e₂ ≠—→≠ eu ⨾ (≠ e₁ ⨾ e₂)

--     NORM-SEQ-SWAP₁ :
--       eu ⨾ (𝕧 x ＝` v ⨾ e) ≠—→≠ 𝕧 x ＝` v ⨾ (eu ⨾ e)

--     -- NORM-SEQ-SWAP₂ : ⦃ _ : ≠ e ⦄ ⦃ _ : eu≠ eu ⦄ →
--     --   eu ⨾ (𝕧 x ＝` s ⨾ e) —→ 𝕧 x ＝` s ⨾ (eu ⨾ e)

--     NORM-SEQ-DEFR :
--       x ∉ fv e₂
--       ─────────
--       ≠ (∃ x ⇒ e₁) ⨾ e₂ ≠—→≠ ∃ x ⇒ (≠ e₁ ⨾ e₂)

--     NORM-SEQ-DEFL :
--       x ∉ fv eu
--       ─────────
--       eu ⨾ (∃ x ⇒ e) ≠—→≠ ∃ x ⇒ (eu ⨾ e)

--     NORM-DEFR :
--       y ∉ fv (v , e₂)
--       ───────────────
--       v ＝ (∃ y ⇒ e₁) ⨾ e₂ ≠—→≠ ∃ y ⇒ v ＝ e₁ ⨾ e₂

--     NORM-SEQR :
--       v ＝ (eu ⨾ e₁) ⨾ e₂ ≠—→≠ eu ⨾ v ＝ e₁ ⨾ e₂

--     -- one

--     ONE-FAIL :
--       one⦅ fail ⦆ ≠—→≠ fail

--     ONE-CHOICE :
--       one⦅ ` v₁ ∣ e₂ ⦆ ≠—→≠ ` v₁

--     ONE-VALUE :
--       one⦅ ` v ⦆ ≠—→≠ ` v

--     -- all

--     ALL-FAIL :
--       all⦅ fail ⦆ ≠—→≠ `⟨⟩

--     ALL-CHOICE : ⦃ _ : ≠[] vs ⦄ →
--       all⦅ ∣⁺ vs ⦆ ≠—→≠ `⟨ vs ⟩

--     -- choice

--     CHOOSE : ⦃ _ : cx ≠∙ ⦄ →
--       -- cx [ e₁ ∣ e₂ ] ≠—→≠ cx [ e₁ ] ∣ cx [ e₂ ]
--       e ≡ cx [ e₁ ∣ e₂ ]
--       ────────────────────────────
--       e ≠—→≠ cx [ e₁ ] ∣ cx [ e₂ ]

--   data _—→_ : Rel₀ ＝Expr where

--     ≠_ :
--       e ≠—→≠ e′
--       ──────────
--       ≠ e —→ ≠ e′

--     U-FAIL : ⦃ _ : isHead hnf₁ ⦄ ⦃ _ : isHead hnf₂ ⦄
--       → hnf₁ —↛⟨U-SCALAR⟩ hnf₂
--       → hnf₁ —↛⟨U-TUP⟩ hnf₂
--         ──────────────────────
--         hnf₁ ＝` hnf₂ —→ ≠ fail


_ : 𝕜2 ＝` 𝕜3 —→ fail
_ = U-FAIL (λ where (_ , refl , ())) proj₁

-- _—→?_ : Decidable² _—→_
-- e —→? e′ = {!e e′!}

`if_then_else_ : (e₁ e₂ e₃ : Expr) ⦃ _ : ≠ e₂ ⦄ ⦃ _ : ≠ e₃ ⦄ → Expr
`if e₁ then e₂ else e₃ =
  let y = freeIn (e₁ , e₂ , e₃)
      x = freeIn y
  in
  ∃ y ⇒ 𝕧 y ＝ one⦅ e₁ ⨾ ` (ƛ x ⇒ e₂) ∣ (` (ƛ x ⇒ e₃)) ⦆
      ⨾ (𝕧 y) · ⟨⟩
-- `if_then_else_ : Op₃ Expr
-- `if e₁ then e₂ else e₃ =
--   let y = freeIn (e₁ , e₂ , e₃)
--       x = freeIn y
--   in
--   ∃ y ⇒ 𝕧 y ＝ one⦅ ≠ e₁ ⨾ ` (ƛ x ⇒ e₂) ∣ (` (ƛ x ⇒ e₃)) ⦆
--       ⨾ (𝕧 y) · ⟨⟩

for_ : (e : Expr) ⦃ _ : ≠ e ⦄ → Expr
for e = all⦅ e ⦆
-- pattern for_ e = all⦅ e ⦆

for_do⦅_⦆ : (e₁ e₂ : Expr) ⦃ _ : ≠ e₂ ⦄ → Expr
for e₁ do⦅ e₂ ⦆ =
  let y = freeIn (e₁ , e₂)
      x = freeIn y
      z = freeIn x
  in
  ∃ y ⇒ 𝕧 y ＝ all⦅ e₁ ⨾ ` (ƛ x ⇒ e₂) ⦆
      ⨾ ( (♯ ♯map) · ⟨ ⟦ (ƛ z ⇒ 𝕧 z · ⟨⟩) , 𝕧 y ⟧ ⟩)
-- for_do⦅_⦆ : Op₂ Expr
-- for e₁ do⦅ e₂ ⦆ =
--   let y = freeIn (e₁ , e₂)
--       x = freeIn y
--       z = freeIn x
--   in
--   ∃ y ⇒ 𝕧 y ＝ all⦅ ≠ e₁ ⨾ ` (ƛ x ⇒ e₂) ⦆
--       ⨾ ( (♯ ♯map) · ⟨ ⟦ (ƛ z ⇒ 𝕧 z · ⟨⟩) , 𝕧 y ⟧ ⟩)

open ReflexiveTransitiveClosure _—→_ public
  using (_—↠_; begin_; _—→⟨_⟩_; _—↠⟨_⟩_; _∎)

module _ ⦃ _ : ≠ e ⦄ where
  _ : ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e —↠ e
  _ =
    begin
      ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e
    —→⟨ U-TUP ⟩
      𝕜2 ＝` 𝕜2 ⨾ 𝕜3 ＝` 𝕜3 ⨾ e
    —→⟨ U-SCALAR ⟩
      𝕜3 ＝` 𝕜3 ⨾ e
    —→⟨ U-SCALAR ⟩
      e
    ∎
-- module _ {e} where
--   _ : ≠ (⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e) —↠ ≠ e
--   _ =
--     begin
--       ≠ (⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ＝` ⟨ ⟦ 𝕜2 , 𝕜3 ⟧ ⟩ ⨾ e)
--     —→⟨ ≠ U-TUP ⟩
--       ≠ (𝕜2 ＝` 𝕜2 ⨾ 𝕜3 ＝` 𝕜3 ⨾ e)
--     —→⟨ ≠ U-SCALAR ⟩
--       ≠ (𝕜3 ＝` 𝕜3 ⨾ e)
--     —→⟨ ≠ U-SCALAR ⟩
--       ≠ e
--     ∎

-- pattern _`+_ x y = ♯ add · ⟨ x ∷ y ∷ [] ⟩

-- -- private module _ {x y z : Value} where
-- --   _ : ≠ (x `+ (? ∣ ?)) —↠ ≠ ((x `+ y) ∣ (x `+ z))
-- --   _ =
-- --     begin
-- --       ≠ (x + (y ∣ z))
-- --     —→⟨ ? ⟩
-- --       ≠ (x + y ∣ x + z)
-- --     ∎

-- progress : ∀ e → Dec $ ∃ (e ≠—→≠_)
-- progress (` x) = no λ where (e′ , CHOOSE eq) → {!!}
-- progress (eu ⨾ e) = {!!}
-- progress (∃ x ⇒ e) = {!!}
-- progress (fail) = no λ where (_ , e→) → {!e→!}
-- progress (e ∣ e′) = {!!}
-- progress (v · v′) = {!!}
-- progress (one⦅ e ⦆) = {!!}
-- progress (for e) = {!!}

-- progress＝ : ∀ eu → Dec $ ∃ (eu —→_)
-- progress＝ (v ＝` v′)
--   with isHead? v
-- ... | no ¬hdv = no λ where (_ , U-FAIL ⦃ hdv ⦄ _ _) → ¬hdv hdv
-- ... | yes hdv
--   with isHead? v′
-- ... | no ¬hdv′ = no λ where (_ , U-FAIL ⦃ _ ⦄ ⦃ hdv′ ⦄ _ _) → ¬hdv′ hdv′
-- ... | yes hdv′
--   with v —↛⟨U-SCALAR⟩? v′
-- ... | no ¬p = no λ where (_ , U-FAIL p _) → ¬p p
-- ... | yes ¬U-SCALAR
--   with v —↛⟨U-TUP⟩? v′
-- ... | no ¬p = no λ where (_ , U-FAIL _ p) → ¬p p
-- ... | yes ¬U-TUP
--     = yes (≠ fail , U-FAIL ⦃ hdv ⦄ ⦃ hdv′ ⦄ ¬U-SCALAR ¬U-TUP)
-- progress＝ (v ＝ (x ⨾ e)) = no λ ()
-- progress＝ (v ＝ (∃ x ⇒ e)) = no λ ()
-- progress＝ (v ＝ fail) =  no λ ()
-- progress＝ (v ＝ (e ∣ e₁)) = no λ ()
-- progress＝ (v ＝ (x · x₁)) = no λ ()
-- progress＝ (v ＝ one⦅ e ⦆) = no λ ()
-- progress＝ (v ＝ (for e)) = no λ ()
-- progress＝ (≠ e) with progress e
-- ... | yes (_ , e→) = yes (-, ≠ e→)
-- ... | no ¬p = no λ where (_ , ≠ e→) → ¬p (-, e→)

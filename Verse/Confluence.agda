{-# OPTIONS --allow-unsolved-metas #-}
module Verse.Confluence where

open import Verse.Prelude
open import Verse.Core
open import Verse.Helpers
open import Verse.Context
open import Verse.RewriteSemantics

confluence : WellFounded _—→_
confluence = acc ∘ _←—_
  where
    absurd₁ : ∀ {y v v′} → ¬ (y —→ v ＝ `𝕧 v′)
    absurd₁ (NORM-EQ-SWAP ⦃ () ⦄)

    _←—_ : ∀ e e′ → e′ —→ e → Acc _—→_ e′
    _←—_ = {!!}
    -- ((.(𝕧 _) ＝ .(` v′)) ←— (v′ ＝ .(`𝕧 _))) NORM-EQ-SWAP
    --   = acc λ y y→ → ⊥-elim $ absurd₁ y→
    -- ((v ＝ e) ←— (≠ e′)) ()
    -- ((≠ .fail) ←— (v ＝ .(` _))) (U-FAIL x x₁) = acc λ _ y→ → {!(_ ←— _)!}
    -- ((≠ e)   ←— (≠ e′))    p = {!p!}

-- confluence : WellFounded _≠—→≠_
-- confluence = acc ∘ _←—_
--   where
--     _←—_ : ∀ e e′ → e′ ≠—→≠ e → Acc _≠—→≠_ e′
--     (e ←— e′) p = {!!}

-- confluence′ : WellFounded _—→_
-- confluence′ = acc ∘ _←—_
--   where
--     _←—_ : ∀ e e′ → e′ —→ e → Acc _—→_ e′
--     ((≠ e) ←— (≠ e′)) (≠ p) = {!!}
--     (.(≠ fail) ←— .(_ ＝` _)) (U-FAIL x x₁) = {!!}

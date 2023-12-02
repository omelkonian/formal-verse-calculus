module Verse.Prelude where

open import Prelude.Init public
  hiding ([_])
open SetAsType public
open L.Mem public
open import Prelude.General public
open import Prelude.InferenceRules public
open import Prelude.Closures public
open import Prelude.Decidable public
open import Prelude.DecEq public
  hiding (_≠_)
open import Prelude.Ord public
open import Prelude.Nary public
open import Prelude.Lists.Indexed public

variable A B : Type; P : Pred₀ A

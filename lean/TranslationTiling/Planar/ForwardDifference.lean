/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in third_party/openai-math.LICENSE.
Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Function.Iterate

namespace TranslationTiling

universe uA

namespace Planar

def forwardDiff {A : Type uA} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : A :=
  f (n + 1) - f n

@[simp] theorem forwardDiff_apply {A : Type uA} [AddCommGroup A]
    (f : ℤ → A) (n : ℤ) : forwardDiff f n = f (n + 1) - f n := rfl

end Planar

end TranslationTiling

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Tactic.NormNum

/-!
# A2 chamber-normalization counterexample

The rank-two arithmetic showing why a regular cocharacter must be chosen in
the chamber determined by the fixed Borel before selecting a sign.
-/

namespace RiemannResearch.E8

/-- For a literal arbitrary-cocharacter reading, the A2 positive-root
pairings are nonzero while neither sign is positive on both simple roots. -/
theorem a2Coroot_sign_normalization_counterexample :
    (2 : ℤ) ≠ 0 ∧ (-1 : ℤ) ≠ 0 ∧ 2 + (-1 : ℤ) ≠ 0 ∧
      ¬ (((0 : ℤ) < 2 ∧ (0 : ℤ) < -1) ∨
        ((0 : ℤ) < -2 ∧ (0 : ℤ) < 1)) := by
  norm_num

end RiemannResearch.E8

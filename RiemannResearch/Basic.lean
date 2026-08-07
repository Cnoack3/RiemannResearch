/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Basic project sanity checks
-/

/-- A minimal arithmetic check that confirms mathlib tactics are available. -/
theorem sanity_check : (2 : ℕ) + 2 = 4 := by
  norm_num

namespace Nat

/-- Concurrency branch B: zero is a left identity for natural-number addition. -/
theorem zero_add_concurrency_b (n : ℕ) : 0 + n = n := by
  exact Nat.zero_add n

end Nat

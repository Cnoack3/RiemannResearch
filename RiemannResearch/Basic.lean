import Mathlib

/-
Copyright (c) 2026 Cnoack3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
/-!
# Basic project sanity checks
-/

/-- A minimal arithmetic check that confirms mathlib tactics are available. -/
theorem sanity_check : (2 : ℕ) + 2 = 4 := by
  norm_num

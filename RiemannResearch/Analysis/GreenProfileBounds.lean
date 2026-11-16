import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Signed Green root and relative profile bounds
Source: user-provided "Exact-Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, Theorem 3.1 and agenda A1/A2. The signed root bound and the
relative-energy criterion strengthen its scalar estimates. The actual arithmetic
providers are separate hypotheses, not consequences of these inequalities.
-/

namespace RiemannResearch.Analysis.GreenProfileBounds

/-- The Green root controls the energy with its sign retained. -/
theorem energy_le_signed_root {q r a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hroot : (q - r) ^ 2 ≤ a * q) : q ≤ 2 * r + a := by
  by_cases hq0 : q = 0
  · subst q
    have hr : r = 0 := by nlinarith [sq_nonneg r]
    simp [hr, ha]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    by_contra! hn
    have hp := mul_pos hqpos (show 0 < q - 2 * r - a by linarith)
    nlinarith [sq_nonneg r]

/-- A relative profile - error bound and only an upper signed - moment bound
give bounded optimized energy. Neither term is required to converge to zero. -/
theorem energy_le_of_relative_profile {q r tau m C a B : ℝ}
    (hq : 0 ≤ q) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hid : r = q + tau) (htau : tau ^ 2 ≤ a * q)
    (herr : (r - m) ^ 2 ≤ C * q) (hm : m ≤ B) :
    q ≤ 2 * B + 2 * C + 2 * a := by
  rw [hid] at herr
  have hh : (q - m) ^ 2 ≤ (2 * C + 2 * a) * q := by
    nlinarith [sq_nonneg ((q - m) + 2 * tau)]
  have hb := energy_le_signed_root hq (by positivity : 0 ≤ 2 * C + 2 * a) hh
  linarith

/-- The exact square completion behind the signed root bound. -/
theorem root_square_identity (q r a : ℝ) :
    q * (2 * r + a - q) = a * q - (q - r) ^ 2 + r ^ 2 := by ring

end RiemannResearch.Analysis.GreenProfileBounds

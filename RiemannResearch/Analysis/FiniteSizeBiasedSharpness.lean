/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.FiniteSizeBiasedExponential

namespace RiemannResearch.Analysis.FiniteSizeBiasedExponential

/-- For the law with mass `p` at `z` and mass `1-p` at zero, all the tilts
through `A` are at most one. Its scaled second moment is exactly `1/A`.
The mean tends to zero as the positive atom tends to infinity. -/
theorem two_atom_reciprocal_sharp {A z : ℝ} (hA : 0 < A) (hz : 1 ≤ z) :
    let m := Real.exp (-(A * z))
    let p := m / z
    0 < p ∧ p ≤ 1 ∧ p * z = m ∧
      (p * z ^ 2) / (m * Real.log (1 / m)) = 1 / A ∧
      ∀ a : ℝ, a ≤ A → p * z * Real.exp (a * z) ≤ 1 := by
  dsimp only
  let m := Real.exp (-(A * z))
  let p := m / z
  have hzpos := zero_lt_one.trans_le hz
  have hM : 0 < m := Real.exp_pos _
  have hMle : m ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hA.le hzpos.le))
  have hfirst : p * z = m := div_mul_cancel₀ m hzpos.ne'
  have hlog : Real.log (1 / m) = A * z := by
    rw [Real.log_div one_ne_zero hM.ne', Real.log_one]
    dsimp only [m]
    rw [Real.log_exp]
    ring
  refine ⟨div_pos hM hzpos, (div_le_iff₀ hzpos).mpr (by simpa using hMle.trans hz),
    hfirst, ?_, ?_⟩
  · change p * z ^ 2 / (m * Real.log (1 / m)) = 1 / A
    rw [pow_two, ← mul_assoc, hfirst, hlog]
    field_simp [hA.ne', hzpos.ne', hM.ne'] <;> ring
  · intro a ha
    change p * z * Real.exp (a * z) ≤ 1
    rw [hfirst]
    change Real.exp (-(A * z)) * Real.exp (a * z) ≤ 1
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_right ha hzpos.le])

end RiemannResearch.Analysis.FiniteSizeBiasedExponential

import Mathlib.Data.Complex.Basic

/-!
# Critical-line points for Mellin transforms

The critical-line parametrization and its elementary properties are shared by
Mellin frequency kernels and compact-frequency mixtures.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.MellinFrequency

def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

theorem criticalPoint_ne_zero (t : ℝ) : criticalPoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

end RiemannResearch.RH.Pareto.MellinFrequency

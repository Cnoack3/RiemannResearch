import RiemannResearch.RH.BurnolCayleyJensen
import RiemannResearch.RH.BurnolCriticalLine

/-!
# Critical-line boundary coordinates for the Cayley zeta function

The unit-circle boundary modulus is exactly the critical-line zeta modulus.
This is a pointwise geometric bridge, not an assertion of convergence of
boundary logarithmic integrals. See Burnol, Theorem 1.3,
https://arxiv.org/abs/math/9910055.
-/

noncomputable section
namespace RiemannResearch.RH.Burnol

/-- The finite critical line parametrizes the unit circle minus one. -/
def criticalCirclePoint (t : ℝ) : ℂ := diskCoordinate (criticalPoint t)

theorem criticalCirclePoint_norm (t : ℝ) : ‖criticalCirclePoint t‖ = 1 := by
  unfold criticalCirclePoint diskCoordinate
  rw [norm_div, criticalPoint_sub_one_norm]
  exact div_self (norm_ne_zero_iff.mpr (criticalPoint_ne_zero t))

theorem criticalCirclePoint_ne_one (t : ℝ) : criticalCirclePoint t ≠ 1 := by
  intro h
  have hs := criticalPoint_ne_zero t
  change (criticalPoint t - 1) / criticalPoint t = 1 at h
  have hh := (div_eq_iff hs).mp h
  have : (1 : ℂ) = 0 := by linear_combination -hh
  exact one_ne_zero this

theorem cayley_criticalCirclePoint (t : ℝ) :
    cayley (criticalCirclePoint t) = criticalPoint t :=
  cayley_diskCoordinate (criticalPoint_ne_zero t)

theorem diskZeta_criticalCirclePoint (t : ℝ) :
    diskZeta (criticalCirclePoint t) =
      criticalCirclePoint t * riemannZeta (criticalPoint t) := by
  rw [diskZeta, cayley_criticalCirclePoint,
    regularZetaRatio_eq (by simp [criticalPoint]) (criticalPoint_ne_one t)]
  rfl

theorem diskZeta_criticalCirclePoint_norm (t : ℝ) :
    ‖diskZeta (criticalCirclePoint t)‖ = ‖riemannZeta (criticalPoint t)‖ := by
  rw [diskZeta_criticalCirclePoint, norm_mul, criticalCirclePoint_norm, one_mul]

theorem criticalLogDensity_boundary (t : ℝ) :
    criticalLogDensity t =
      Real.log ‖diskZeta (criticalCirclePoint t)‖ / (1 / 4 + t ^ 2) := by
  rw [diskZeta_criticalCirclePoint_norm]
  rfl

end RiemannResearch.RH.Burnol

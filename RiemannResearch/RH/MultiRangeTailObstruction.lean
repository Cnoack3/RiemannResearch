import RiemannResearch.RH.ConditionalMeanTailObstruction

/-!
# Explicit tail-only polynomial obstruction

The eventual lower bound in section 10, equation (10.3), of
`RH_Multi_Range_Divisor_Corrections_2026-09-18.md`.
The hypothetical zeta zero is a theorem hypothesis; no such zero, RH,
or subpolynomial approximation family is asserted to exist.
-/
noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro

/-- Keep the compulsory head mass out of the weighted tail estimate. -/
theorem exact_head_tail_scaled_obstruction_eventually
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ conditionalHeadClass N,
      (1 / 4 : ℝ) ≤ (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
        (N : ℝ) ^ (1 - 2 * s.re) *
          (conditionalMeanSquare g - (N : ℝ) / ((N : ℝ) + 2)) := by
  filter_upwards [mellinSecond_prefix_eventually s hs, eventually_ge_atTop 1] with N hp hN
  intro g hg
  have h := hp.trans (exact_head_tail_dual_obstruction s hs hs1 hz N hg)
  exact h.trans (mul_le_mul_of_nonneg_right (dualTail_le s hs N hN)
    (sub_nonneg.mpr (conditionalMeanSquare_ge_head_mass N hg)))

/-- Equation (10.3), with its explicit constant and the actual remaining tail energy. -/
theorem exact_head_tail_polynomial_obstruction_eventually
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ conditionalHeadClass N,
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1) ≤
          conditionalMeanSquare g - (N : ℝ) / ((N : ℝ) + 2) := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hB : 0 < ‖s * (s + 1)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hs0 hsadd))
  filter_upwards [exact_head_tail_scaled_obstruction_eventually s hs hs1 hz,
    eventually_ge_atTop 1] with N hob hN
  intro g hg
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1) = 1 := by
    rw [← Real.rpow_add hnR]
    convert Real.rpow_zero (N : ℝ) using 1
    congr 1
    ring
  have hc : (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) = (1 / 4 : ℝ) := by
    field_simp [ne_of_gt hd, ne_of_gt hB]
    ring
  have he : ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re)) *
      (((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1)) = (1 / 4 : ℝ) := by
    calc
      _ = ((3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
          ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2))) *
          ((N : ℝ) ^ (1 - 2 * s.re) * (N : ℝ) ^ (2 * s.re - 1)) := by ring
      _ = _ := by rw [hc, hpow, mul_one]
  have hcoef : 0 < (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
      (N : ℝ) ^ (1 - 2 * s.re) := by positivity
  by_contra hnot
  have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hcoef
  rw [he] at hbad
  exact not_lt_of_ge (hob g hg) hbad

/-- The same explicit lower bound survives taking the genuine legal infimum. -/
theorem conditionalHeadMinimum_tail_polynomial_obstruction_eventually
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / ((N : ℝ) + 2) +
        ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
          (N : ℝ) ^ (2 * s.re - 1) ≤ conditionalHeadMinimum N := by
  filter_upwards [exact_head_tail_polynomial_obstruction_eventually s hs hs1 hz] with N hN
  apply le_csInf (conditionalHeadEnergies_nonempty N)
  rintro x ⟨g, hg, rfl⟩
  have h := hN g hg
  linarith

end RiemannResearch.RH.Pareto

import RiemannResearch.RH.QAbsoluteChargeMass
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.QMellinTransfer
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution

/-! # The Dirichlet series of the physical floor charges

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, §8;
the integral representation is Abel summation (Mathlib's
`LSeries_eq_mul_integral`). This verifies the series on its actual domain
of absolute convergence used in the paper, including the boundary Re(s)=2.
M. Balazard, Prop. 9, https://doi.org/10.1007/978-3-030-61887-2_3,
further proves absolute convergence for Re(s)>3/2.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators LSeries.notation Asymptotics
namespace RiemannResearch.RH.PrimeTreeChargeDirichlet
open ZetaTwoHilbert QMellinTransfer QPrimeSubtreeBudget

/-- The coefficient of the floor at conductor n, with the project anchor. -/
def charges (f : QHilbert) (n : ℕ) : ℂ := (charge f n : ℂ)

private def increments (f : QHilbert) (n : ℕ) : ℂ :=
  (qSequence f n : ℂ) - (qSequence f (n - 1) : ℂ)

private theorem sum_increments (f : QHilbert) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, increments f k = (qSequence f n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp [increments]

private theorem increments_convolution (f : QHilbert) :
    charges f ⍟ (1 : ℕ → ℂ) = increments f := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [increments]
  · simp only [LSeries.convolution_def, Pi.one_apply, mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun i _ => charges f i)]
    unfold charges charge increments
    exact_mod_cast Pareto.sum_mobiusDifference (qSequence f) n (Nat.pos_of_ne_zero hn)

theorem charge_summable (f : QHilbert) (s : ℂ) (hs : 2 ≤ s.re) :
    LSeriesSummable (charges f) s := by
  apply LSeriesSummable.of_re_le_re (s := (2 : ℂ)) (by simpa using hs)
  unfold LSeriesSummable
  rw [← summable_norm_iff]
  apply (Pareto.qSequence_mobiusDifference_absolute_mass f).congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, charges, charge, Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]

private theorem sum_increments_bigO (f : QHilbert) :
    (fun n => ∑ k ∈ Finset.Icc 1 n, increments f k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1, ?_⟩
  have he := (qSequence_div_nat_tendsto_zero f).norm
  have hb := he.eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hv hn
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp] at hv
  rw [sum_increments, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one,
    Real.norm_eq_abs, abs_of_pos hp]
  exact ((div_lt_iff₀ hp).mp hv).le

/-- The exact zeta product and the continued numerator use the same anchored
charges, for every physical Hilbert vector. -/
theorem charge_product (f : QHilbert) (s : ℂ) (hs : 2 ≤ s.re) :
    LSeries (charges f) s * riemannZeta s = s * qMellin f s := by
  have hs1 : 1 < s.re := by linarith
  have hc := charge_summable f s hs
  have h1 := LSeriesSummable_one_iff.mpr hs1
  have hΔ : LSeriesSummable (increments f) s := increments_convolution f ▸ hc.convolution h1
  rw [← LSeries_one_eq_riemannZeta hs1, ← LSeries_convolution' hc h1, increments_convolution,
    LSeries_eq_mul_integral _ (show 0 ≤ (1 : ℝ) by norm_num) hs1 hΔ (sum_increments_bigO f),
    qMellin_eq_step_integral]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [sum_increments, show -(s + 1) = -s - 1 by ring]

theorem charge_series (f : QHilbert) (s : ℂ) (hs : 2 ≤ s.re) :
    LSeriesHasSum (charges f) s (s * qMellin f s / riemannZeta s) := by
  have hZ := riemannZeta_ne_zero_of_one_lt_re (show 1 < s.re by linarith)
  have he := (eq_div_iff hZ).mpr (charge_product f s hs)
  exact he ▸ (charge_summable f s hs).LSeriesHasSum

end RiemannResearch.RH.PrimeTreeChargeDirichlet

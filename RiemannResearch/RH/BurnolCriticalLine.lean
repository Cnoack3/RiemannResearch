import RiemannResearch.RH.BurnolZeroProductConvergence
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The actual BSY critical-line integrand

The normalization is that of Burnol, Theorem 1.3,
https://arxiv.org/abs/math/9910055, and Bui--Lester--Milinovich (1.1),
https://arxiv.org/abs/1306.0856.  The results here prove local integrability
including at critical-line zeros.  They do not assume a zero-free critical
line.  Global integrability and the zero-sum identity are separate assertions.
-/

noncomputable section
open Complex MeasureTheory
open scoped Topology

namespace RiemannResearch.RH.Burnol

/-- The usual parametrization of the critical line. -/
def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + t * I

@[simp] theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

@[simp] theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by
  simp [criticalPoint]

theorem criticalPoint_injective : Function.Injective criticalPoint := by
  intro a b h
  simpa only [criticalPoint_im] using congrArg Complex.im h

theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

theorem criticalPoint_ne_zero (t : ℝ) : criticalPoint t ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

/-- The pole-canceling ratio has modulus one on the critical line. -/
theorem criticalPoint_sub_one_norm (t : ℝ) :
    ‖criticalPoint t - 1‖ = ‖criticalPoint t‖ := by
  have he : criticalPoint t - 1 = -star (criticalPoint t) := by
    apply Complex.ext <;> simp [criticalPoint] <;> ring
  rw [he, norm_neg, norm_star]

theorem criticalPoleRatio_norm (t : ℝ) :
    ‖(criticalPoint t - 1) / criticalPoint t‖ = 1 := by
  rw [norm_div, criticalPoint_sub_one_norm,
    div_self (norm_ne_zero_iff.mpr (criticalPoint_ne_zero t))]

/-- Exact boundary normalization, valid even at zeros of zeta. -/
theorem critical_regularized_norm (t : ℝ) :
    ‖((criticalPoint t - 1) / criticalPoint t) * riemannZeta (criticalPoint t)‖ =
      ‖riemannZeta (criticalPoint t)‖ := by
  rw [norm_mul, criticalPoleRatio_norm, one_mul]

@[simp] theorem criticalPoint_neg (t : ℝ) :
    criticalPoint (-t) = star (criticalPoint t) := by
  simp [criticalPoint]

theorem criticalZeta_norm_even (t : ℝ) :
    ‖riemannZeta (criticalPoint (-t))‖ = ‖riemannZeta (criticalPoint t)‖ := by
  rw [criticalPoint_neg]
  change ‖riemannZeta ((starRingEnd ℂ) (criticalPoint t))‖ = _
  rw [riemannZeta_conj, norm_conj]

/-- Real analyticity of zeta along the critical line, including its zeros. -/
theorem analyticAt_criticalZeta (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => riemannZeta (criticalPoint u)) t := by
  have hz : AnalyticAt ℂ riemannZeta (criticalPoint t) := by
    have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
      intro z hz
      exact (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds (criticalPoint_ne_one t))
  have hp : AnalyticAt ℝ criticalPoint t := by
    change AnalyticAt ℝ (fun u : ℝ => (1 / 2 : ℂ) + Complex.ofRealCLM u * I) t
    exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact hz.restrictScalars.comp hp

/-- Logarithmic zero singularities are integrable on every finite interval. -/
theorem intervalIntegrable_criticalLog (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖riemannZeta (criticalPoint t)‖)
      volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t ht
  exact (analyticAt_criticalZeta t).meromorphicAt

/-- The BSY density before its factor `1 / (2π)`. -/
def criticalLogDensity (t : ℝ) : ℝ :=
  Real.log ‖riemannZeta (criticalPoint t)‖ / (1 / 4 + t ^ 2)

theorem criticalLogDensity_even (t : ℝ) :
    criticalLogDensity (-t) = criticalLogDensity t := by
  simp only [criticalLogDensity, criticalZeta_norm_even, neg_sq]

theorem criticalWeight_continuous :
    Continuous (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro t
    positivity

/-- The weighted density has an honest integral on each compact interval. -/
theorem intervalIntegrable_criticalLogDensity (a b : ℝ) :
    IntervalIntegrable criticalLogDensity volume a b := by
  change IntervalIntegrable (fun t : ℝ =>
    Real.log ‖riemannZeta (criticalPoint t)‖ / (1 / 4 + t ^ 2)) volume a b
  simp_rw [div_eq_mul_inv]
  exact (intervalIntegrable_criticalLog a b).mul_continuousOn
    criticalWeight_continuous.continuousOn

/-- A finite critical-line integral; unlike the global Bochner integral, this
does not require an as-yet-unproved global-integrability provider. -/
def criticalLogCutoff (T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in -T..T, criticalLogDensity t

/-- Exact finite-interval additivity through any chosen intermediate height. -/
theorem criticalLogDensity_integral_split (a b c : ℝ) :
    (∫ t in a..c, criticalLogDensity t) =
      (∫ t in a..b, criticalLogDensity t) +
      ∫ t in b..c, criticalLogDensity t := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_criticalLogDensity a b)
    (intervalIntegrable_criticalLogDensity b c)).symm

/-- Every bounded ordinate window contains only finitely many critical zeros. -/
theorem finite_criticalZeros_window (a b : ℝ) :
    {t : ℝ | a < t ∧ t ≤ b ∧ riemannZeta (criticalPoint t) = 0}.Finite := by
  have hf := Zeta23.ZetaSeam.finite_window_holds a b
  have hp := Set.Finite.preimage criticalPoint_injective.injOn hf
  apply hp.subset
  intro t ht
  exact ⟨⟨ht.2.2, by norm_num, by norm_num⟩,
    by simpa only [criticalPoint_im] using ht.1,
    by simpa only [criticalPoint_im] using ht.2.1⟩

/-- The zero ordinates have measure zero, without any simplicity hypothesis. -/
theorem countable_criticalZeros :
    {t : ℝ | riemannZeta (criticalPoint t) = 0}.Countable := by
  have hc : (⋃ n : ℕ, {t : ℝ | -(n : ℝ) < t ∧ t ≤ n ∧
      riemannZeta (criticalPoint t) = 0}).Countable :=
    Set.countable_iUnion fun n => (finite_criticalZeros_window (-(n : ℝ)) n).countable
  apply hc.mono
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_, ?_, ht⟩
  · linarith [neg_abs_le t]
  · linarith [le_abs_self t]

theorem criticalZeta_ne_zero_ae :
    ∀ᵐ t : ℝ, riemannZeta (criticalPoint t) ≠ 0 := by
  simpa only [Set.mem_setOf_eq] using countable_criticalZeros.ae_notMem volume

/-- Exact pole-factor separation holds almost everywhere; pointwise separation
at zeros would be false with the totalized value `Real.log 0 = 0`. -/
theorem critical_regularization_log_ae :
    (fun t : ℝ => Real.log ‖(criticalPoint t - 1) * riemannZeta (criticalPoint t)‖)
      =ᵐ[volume] (fun t => Real.log ‖riemannZeta (criticalPoint t)‖ +
        Real.log ‖criticalPoint t - 1‖) := by
  filter_upwards [criticalZeta_ne_zero_ae] with t ht
  rw [norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (criticalPoint_ne_one t)))
    (norm_ne_zero_iff.mpr ht)]
  ring

end RiemannResearch.RH.Burnol

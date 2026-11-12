import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.RH.QParetoSquareRootCompactness
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.Analysis.PositiveCompressionSharp

/-!
# Complete finite-head certificates for the actual Pareto forcing

The normal equation is the existing matched-projection theorem. Finite heads
approximate the reciprocal multiplier in operator norm, with the entire
infinite tail retained. A trial solve is certified by its residual; no
cofinal smallness assumption is proved here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open QFiniteSupportDualCriterion

/-- The positive contraction also satisfies D² ≤ D as a quadratic form. -/
theorem reciprocalD_norm_sq_le_inner (f : QHilbert) :
    ‖reciprocalD f‖^2 ≤ inner ℝ f (reciprocalD f) := by
  rw [qNorm_sq, reciprocalD_inner_tsum]
  apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
    (QParetoMetric.reciprocal_energy_summable f)
  intro n
  rw [reciprocalD_apply, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

/-- A finite-rank reciprocal multiplier on the common raw Hilbert carrier. -/
def reciprocalHead (N : ℕ) : QHilbert →L[ℝ] QHilbert :=
  reciprocalD.comp (finiteHeadCLM N)

theorem reciprocalHead_compact (N : ℕ) : IsCompactOperator (reciprocalHead N) :=
  (finiteHeadCLM_compact N).clm_comp reciprocalD

theorem reciprocalHead_error (N : ℕ) (f : QHilbert) :
    ‖reciprocalD f - reciprocalHead N f‖ ≤ ‖f‖ / ((N : ℝ)+1) := by
  change ‖reciprocalD f - reciprocalD (finiteHeadCLM N f)‖ ≤ _
  rw [finiteHeadCLM_apply, ← map_sub]
  have hh (n : ℕ) (hn : n < N) :
      reciprocalD (f - finiteHead N f) n = 0 := by
    rw [reciprocalD_apply]
    change (f n - finiteHead N f n) / ((n:ℝ)+1) = 0
    rw [finiteHead_apply_of_lt N f n hn, sub_self, zero_div]
  have hb := reciprocalD_head_tail_bound (f-finiteHead N f) N
  have hz : (∑ n ∈ Finset.range N, (reciprocalD (f-finiteHead N f) n)^2) = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [hh n (Finset.mem_range.mp hn)]; norm_num
  rw [hz, zero_add] at hb
  have ht : ‖f-finiteHead N f‖^2 ≤ ‖f‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (finiteHead_remainder_norm_le N f)
  have he : ‖reciprocalD (f-finiteHead N f)‖^2 ≤ (‖f‖/((N:ℝ)+1))^2 := by
    rw [div_pow]
    exact hb.trans (div_le_div_of_nonneg_right ht (sq_nonneg _))
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp he

theorem reciprocalHead_opNorm_error (N : ℕ) :
    ‖reciprocalD-reciprocalHead N‖ ≤ 1/((N:ℝ)+1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro f
  simpa only [sub_apply, one_div_mul_eq_div] using reciprocalHead_error N f

theorem reciprocalHead_tendsto : Tendsto reciprocalHead atTop (𝓝 reciprocalD) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm, norm_sub_rev]
  apply (reciprocalHead_opNorm_error n).trans_lt
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
  have he : 1 < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem reciprocalD_compact : IsCompactOperator reciprocalD :=
  isCompactOperator_of_tendsto reciprocalHead_tendsto
    (Eventually.of_forall reciprocalHead_compact)

/-- The tail constant is exact, witnessed by the first omitted coordinate. -/
theorem reciprocalHead_opNorm_error_eq (N : ℕ) :
    ‖reciprocalD-reciprocalHead N‖ = 1/((N:ℝ)+1) := by
  apply le_antisymm (reciprocalHead_opNorm_error N)
  let e : QHilbert := lp.single 2 N (1:ℝ)
  have hen : ‖e‖ = 1 := by simp [e]
  have hh : finiteHeadCLM N e = 0 := by
    rw [finiteHeadCLM_apply]
    apply lp.ext
    funext n
    by_cases hn : n < N
    · rw [finiteHead_apply_of_lt N e n hn]
      simp [e, lp.single_apply, ne_of_lt hn]
    · rw [finiteHead_apply_eq_zero N e n (Nat.le_of_not_gt hn)]
      rfl
  have hDe : reciprocalD e = (1/((N:ℝ)+1)) • e := by
    apply lp.ext
    funext n
    rw [reciprocalD_apply]
    change e n / ((n:ℝ)+1) = (1/((N:ℝ)+1)) * e n
    by_cases hn : n = N
    · subst n
      simp [e, lp.single_apply]
    · simp [e, lp.single_apply, hn]
  have hb := (reciprocalD-reciprocalHead N).le_opNorm e
  have he : (reciprocalD-reciprocalHead N) e = (1/((N:ℝ)+1)) • e := by
    rw [sub_apply, reciprocalHead, ContinuousLinearMap.comp_apply, hh, map_zero, sub_zero, hDe]
  rw [he, hen, mul_one, norm_smul, hen, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤1/((N:ℝ)+1))] at hb
  exact hb

end RiemannResearch.RH.ZetaTwoHilbert

namespace RiemannResearch.RH.QParetoForcingCertificates
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoClosedProjectionComparison
open RiemannResearch.Analysis.PositiveCompressionCertificate

variable (S : Submodule ℝ QHilbert) (T : Submodule ℝ ThresholdHilbert)
variable [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]

def correction (x : QHilbert) : ThresholdHilbert := toPareto (qFit S x-pFit T x)
def forcing (x : QHilbert) : ThresholdHilbert :=
  T.starProjection (reciprocalD (toPareto (x-pFit T x)))

variable (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)

include hsame

theorem correction_mem (x : QHilbert) : correction S T x ∈ T := by
  unfold correction
  rw [toPareto_sub, toPareto_pFit]
  exact T.sub_mem (toPareto_qFit_mem S T hsame x) (T.starProjection_apply_mem _)

theorem correction_equation (x : QHilbert) :
    normalOperator T reciprocalD (correction S T x) = forcing T x :=
  normal_equation_strong S T hsame x

theorem correction_norm_bounds (x : QHilbert) :
    ‖forcing T x‖/2 ≤ ‖correction S T x‖ ∧ ‖correction S T x‖ ≤ ‖forcing T x‖ :=
  solution_norm_bounds T reciprocalD reciprocalD_positive reciprocalD_norm_le _ _
    (correction_mem S T hsame x) (correction_equation S T hsame x)

theorem correction_eq_zero_iff (x : QHilbert) :
    correction S T x = 0 ↔ forcing T x = 0 := by
  constructor
  · intro h
    have he := correction_equation S T hsame x
    rw [h, map_zero] at he
    exact he.symm
  · intro h
    have hb := (correction_norm_bounds S T hsame x).2
    rw [h, norm_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))


/-- The manuscript's sharp factor, for the actual matched projections. -/
theorem correction_sharp_sq (x : QHilbert) :
    8 * ‖correction S T x‖ ^ 2 ≤ ‖toPareto (x-pFit T x)‖ ^ 2 := by
  apply solution_sharp_sq T reciprocalD reciprocalD_norm_sq_le_inner reciprocalD_symmetric
    _ _ (correction_mem S T hsame x) _ (correction_equation S T hsame x)
  rw [toPareto_sub, toPareto_pFit]
  exact Submodule.sub_starProjection_mem_orthogonal (toPareto x)

/-- A certified geometrically convergent solve for the actual correction. -/
theorem correction_richardson_error (x : QHilbert) (n : ℕ) :
    ‖correction S T x - richardsonIterate T reciprocalD (forcing T x) n‖ ≤
      (1/3:ℝ)^n * ‖forcing T x‖ := by
  have h := richardsonIterate_error T reciprocalD reciprocalD_norm_sq_le_inner
    (forcing T x) (correction S T x) (T.starProjection_apply_mem _)
    (correction_mem S T hsame x) (correction_equation S T hsame x) n
  exact h.trans (mul_le_mul_of_nonneg_left
    (correction_norm_bounds S T hsame x).2 (by positivity))

/-- An inexact finite-head solve with its full infinite error budget. -/
theorem finite_head_trial_error (x : QHilbert) (v : ThresholdHilbert)
    (hv : v ∈ T) (N : ℕ) :
    ‖correction S T x-v‖ ≤
      ‖T.starProjection (reciprocalHead N (toPareto (x-pFit T x))) -
        normalOperator T (reciprocalHead N) v‖ +
      ‖toPareto (x-pFit T x)-v‖/((N:ℝ)+1) := by
  have h := truncated_aPosteriori T reciprocalD (reciprocalHead N) reciprocalD_positive
    (1/((N:ℝ)+1))
    (fun f => by simpa only [sub_apply, one_div_mul_eq_div] using reciprocalHead_error N f)
    (correction S T x) (toPareto (x-pFit T x)) v
    (correction_mem S T hsame x) hv (correction_equation S T hsame x)
  simpa only [one_div_mul_eq_div] using h

omit hsame in
/-- Signed complete energy; the residual term is not discarded. -/
theorem forcing_energy (x : QHilbert) (v : ThresholdHilbert) (hv : v ∈ T) :
    ‖forcing T x‖^2 = 2*inner ℝ (reciprocalD (toPareto (x-pFit T x))) v -
      ‖v‖^2 + ‖forcing T x-v‖^2 :=
  forcing_energy_exact T reciprocalD _ v hv

omit hsame in
theorem forcing_operator_compact : IsCompactOperator (T.starProjection.comp reciprocalD) :=
  reciprocalD_compact.clm_comp T.starProjection


omit hsame in
/-- The actual orthogonal forcing is an off-diagonal compression of D. -/
theorem forcing_energy_le_quarter (x : QHilbert) :
    4 * ‖forcing T x‖ ^ 2 ≤ ‖toPareto (x-pFit T x)‖ ^ 2 := by
  apply forcing_sharp_sq T reciprocalD reciprocalD_norm_sq_le_inner
  rw [toPareto_sub, toPareto_pFit]
  exact Submodule.sub_starProjection_mem_orthogonal (toPareto x)

end RiemannResearch.RH.QParetoForcingCertificates

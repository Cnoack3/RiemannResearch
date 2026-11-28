import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.RH.ParetoOrdinateFiniteBands
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! # Weak-star limits of signed pairs of actual zero ordinates

Every ordered pair of occurrence labels is retained. The compactification is
in the unfolded difference variable. With the squared-count normalization,
bounded pair weights with a convergent total mass have a weak-star limit
supported at infinity. The first Pareto projection error fixes its coefficient.
Arias de Reyna and Rodgers, https://arxiv.org/abs/2311.13441, Section 2.1,
use the vague topology for local point statistics.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis ActualZeroOrdinate
open MontgomeryLocalMass MontgomeryPoisson

/-- The signed unfolded difference for two original occurrence labels. -/
def pairGap (T : ℝ) (i j : Copies T) : ℝ :=
  Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i)

private theorem window_indicator_le_cauchy {L q : ℝ} (hL : 0 < L) (hq : q ≤ L) (d : ℝ) :
    (if |L * d| ≤ q then (1 : ℝ) else 0) ≤ 2 * cauchyWeight (-d) := by
  split_ifs with hd
  · rw [abs_mul, abs_of_pos hL] at hd
    have hd1 : |d| ≤ 1 := by
      by_contra! h
      exact (not_lt_of_ge (hd.trans hq)) (by simpa using mul_lt_mul_of_pos_left h hL)
    have hs := pow_le_pow_left₀ (abs_nonneg d) hd1 2
    rw [sq_abs, one_pow] at hs
    rw [cauchyWeight, show (-d)^2 = d^2 by ring,
      show 2 * (4 / (4+d^2)) = 8 / (4+d^2) by ring]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hs]
  · exact mul_nonneg (by norm_num) (cauchyWeight_nonneg _)

/-- A unit physical window bounds each row once the unfolded scale exceeds q. -/
theorem windowCount_cauchy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q T : ℝ, 1 < T → q ≤ Real.log T / (2 * Real.pi) →
      windowCount T q ≤ (Ncount 0 T : ℝ) * (2 * C * Real.log (T+3)) := by
  obtain ⟨C, hC, hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨C, hC, ?_⟩
  intro q T hT hq
  have hL : 0 < Real.log T / (2 * Real.pi) := div_pos (Real.log_pos hT) (by positivity)
  change (∑ i : Copies T, ∑ j : Copies T, if
    |Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i)| ≤ q
    then (1 : ℝ) else 0) ≤ _
  have hr (i : Copies T) :
      (∑ j : Copies T, if |Real.log T / (2 * Real.pi) *
          (copyOrdinate T j - copyOrdinate T i)| ≤ q then (1 : ℝ) else 0) ≤
        2 * C * Real.log (T+3) := by
    calc
      _ ≤ ∑ j : Copies T, 2 * cauchyWeight (copyOrdinate T i - copyOrdinate T j) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [neg_sub] using
          window_indicator_le_cauchy hL hq (copyOrdinate T j - copyOrdinate T i)
      _ ≤ _ := by
        rw [← Finset.mul_sum, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hrow T (zero_le_one.trans hT.le) _) (by norm_num)
  exact (Finset.sum_le_sum (fun i _ => hr i)).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul])

/-- Fixed unfolded windows contain o(N(T)^2) pairs unconditionally, including collisions. -/
theorem windowCount_div_count_sq_tendsto_zero (q : ℝ) :
    Tendsto (fun T => windowCount T q / (Ncount 0 T : ℝ)^2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := windowCount_cauchy_bound
  have hlim := tendsto_height_div_count.const_mul (4*C)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards with T
    apply div_nonneg _ (sq_nonneg _)
    change 0 ≤ ∑ i : Copies T, ∑ j : Copies T,
      if |pairGap T i j| ≤ q then (1 : ℝ) else 0
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split <;> norm_num))
  · filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_count_pos,
      Real.tendsto_log_atTop.eventually_ge_atTop (q * (2 * Real.pi))] with T hT hN hlog
    have hn : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
    have hq : q ≤ Real.log T / (2 * Real.pi) := (le_div_iff₀ (by positivity)).mpr hlog
    have hw := hb q T (by linarith) hq
    have hlt : Real.log (T+3) ≤ 2*T := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < T+3)]
    calc
      windowCount T q / (Ncount 0 T : ℝ)^2 ≤
          ((Ncount 0 T : ℝ) * (2*C*(2*T))) / (Ncount 0 T : ℝ)^2 :=
        div_le_div_of_nonneg_right
          (hw.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlt (by positivity)) hn.le)) (sq_nonneg _)
      _ = 4*C * (T / (Ncount 0 T : ℝ)) := by field_simp [hn.ne']; ring

theorem nearError_tendsto_zero (q : ℝ) :
    Tendsto (fun T => nearError T q) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (windowCount_div_count_sq_tendsto_zero q)
  exact Eventually.of_forall (fun T => by simpa only [Real.norm_eq_abs] using abs_nearError_le T q)

theorem farError_tendsto (q : ℝ) :
    Tendsto (fun T => farError T q) atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 2)) := by
  have h := squaredError_tendsto.sub (nearError_tendsto_zero q)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with T
  rw [squaredError_eq_near_add_far T q]
  ring

/-- Cancellation along a subsequence outside one fixed gap window suffices for RH. -/
theorem rh_iff_farError_liminf_nonpos (q : ℝ) :
    RiemannHypothesis ↔ liminf (fun T => farError T q) atTop ≤ 0 := by
  rw [(farError_tendsto q).liminf_eq, rh_iff_first_site_vacancy_zero]
  have hn : 0 ≤ (1 - IntegerDPP.limitingKernel 0 0) / 2 := by
    rw [← first_site_residual_sq]
    exact sq_nonneg _
  exact ⟨fun h => h.le, fun h => le_antisymm h hn⟩

/-- One right-hand zero forces a positive lower bound outside every fixed gap window. -/
theorem farError_liminf_lower_of_right_zero (q : ℝ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) * ‖(1 - (2 : ℂ) ^ (-s)) / s‖ ^ 2 ≤
      liminf (fun T => farError T q) atTop := by
  rw [(farError_tendsto q).liminf_eq]
  have hfloor := IntegerDPP.mellinVacancyFloor_le_limitingVacancy s hs hs1 hz
  rw [IntegerDPP.limitingVacancy_eq_kernel_complement] at hfloor
  calc
    _ = IntegerDPP.mellinVacancyFloor s / 2 := by
      rw [IntegerDPP.mellinVacancyFloor, IntegerDPP.firstPoint_mellin s hs]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hfloor (by norm_num)

/-- Tests on the one-point compactification of the unfolded gap line. -/
abbrev GapTest := C(OnePoint ℝ, ℝ)

def pairMass (T : ℝ) (w : Copies T → Copies T → ℝ) : ℝ :=
  (∑ i, ∑ j, w i j) / (Ncount 0 T : ℝ)^2

/-- Atomic signed measure represented as a continuous linear functional. -/
def gapFunctional (T : ℝ) (w : Copies T → Copies T → ℝ) : StrongDual ℝ GapTest :=
  ((Ncount 0 T : ℝ)^2)⁻¹ • ∑ i, ∑ j,
    w i j • ContinuousMap.evalCLM ℝ (OnePoint.some (pairGap T i j))

theorem gapFunctional_apply (T : ℝ) (w : Copies T → Copies T → ℝ) (f : GapTest) :
    gapFunctional T w f =
      (∑ i, ∑ j, w i j * f (OnePoint.some (pairGap T i j))) / (Ncount 0 T : ℝ)^2 := by
  simp only [gapFunctional, smul_apply, sum_apply,
    ContinuousMap.evalCLM_apply, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem abs_pair_sum_le (T : ℝ) {v g : Copies T → Copies T → ℝ}
    (h : ∀ i j, |v i j| ≤ g i j) :
    |∑ i, ∑ j, v i j| ≤ ∑ i, ∑ j, g i j := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => h i j))

theorem gapFunctional_norm_le (T : ℝ) (w : Copies T → Copies T → ℝ)
    (hw : ∀ i j, |w i j| ≤ 1) : ‖gapFunctional T w‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, Real.norm_eq_abs, gapFunctional_apply, abs_div,
    abs_of_nonneg (sq_nonneg (Ncount 0 T : ℝ))]
  by_cases hn : (Ncount 0 T : ℝ) = 0
  · simp [hn, norm_nonneg]
  · apply (div_le_iff₀ (sq_pos_of_ne_zero hn)).mpr
    apply (abs_pair_sum_le T (g := fun _ _ => ‖f‖) (fun i j => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw i j) (abs_nonneg _)).trans
        (by simpa only [one_mul, ← Real.norm_eq_abs] using f.norm_coe_le_norm _))).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
    ring

/-- A single Banach–Alaoglu compact set contains all the bounded-weight functionals. -/
theorem gapFunctionals_weakStar_compact :
    ∃ K : Set (WeakDual ℝ GapTest), IsCompact K ∧
      ∀ (T : ℝ) (w : Copies T → Copies T → ℝ), (∀ i j, |w i j| ≤ 1) →
        (gapFunctional T w).toWeakDual ∈ K := by
  refine ⟨WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ GapTest) 1,
    WeakDual.isCompact_closedBall _ _, ?_⟩
  intro T w hw
  simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall,
    dist_zero_right] using gapFunctional_norm_le T w hw

/-- Exact subtraction of the boundary value from every signed summand. -/
theorem gapFunctional_sub_mass (T : ℝ) (w : Copies T → Copies T → ℝ) (f : GapTest) :
    gapFunctional T w f - pairMass T w * f OnePoint.infty =
      (∑ i, ∑ j, w i j * (f (OnePoint.some (pairGap T i j)) - f OnePoint.infty)) /
        (Ncount 0 T : ℝ)^2 := by
  rw [gapFunctional_apply, pairMass, div_mul_eq_mul_div, ← sub_div, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem gap_test_outside (f : GapTest) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ u : ℝ, R < |u| → |f (OnePoint.some u) - f OnePoint.infty| < ε := by
  obtain ⟨s, _, hc, hs⟩ := OnePoint.continuousAt_infty.mp
    (f.continuous.continuousAt (x := OnePoint.infty))
    (Metric.ball (f OnePoint.infty) ε) (Metric.ball_mem_nhds _ hε)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hc.isBounded
  refine ⟨R, fun u hu => ?_⟩
  have hnot : u ∉ s := by
    intro hus
    have hh := hR hus
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hh
    exact (not_le_of_gt hu) hh
  have he := hs hnot
  simpa only [Function.comp_apply, Metric.mem_ball, Real.dist_eq] using he

private theorem gapFunctional_error_le {T R ε : ℝ} (hN : 0 < Ncount 0 T) (hε : 0 ≤ ε)
    (w : Copies T → Copies T → ℝ) (hw : ∀ i j, |w i j| ≤ 1) (f : GapTest)
    (hout : ∀ u : ℝ, R < |u| → |f (OnePoint.some u) - f OnePoint.infty| < ε) :
    |gapFunctional T w f - pairMass T w * f OnePoint.infty| ≤
      (2 * ‖f‖) * (windowCount T R / (Ncount 0 T : ℝ)^2) + ε := by
  let k (i j : Copies T) : ℝ := if |pairGap T i j| ≤ R then 1 else 0
  have he (i j : Copies T) :
      |w i j * (f (OnePoint.some (pairGap T i j)) - f OnePoint.infty)| ≤
        2 * ‖f‖ * k i j + ε := by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right (hw i j) (abs_nonneg _)).trans
    rw [one_mul]
    by_cases h : |pairGap T i j| ≤ R
    · have hf := f.dist_le_two_norm (OnePoint.some (pairGap T i j)) OnePoint.infty
      rw [Real.dist_eq] at hf
      simpa only [k, if_pos h, mul_one] using hf.trans (le_add_of_nonneg_right hε)
    · simpa only [k, if_neg h, mul_zero, zero_add] using (hout _ (lt_of_not_ge h)).le
  have hs : (∑ i : Copies T, ∑ j : Copies T, (2 * ‖f‖ * k i j + ε)) =
      2 * ‖f‖ * windowCount T R + (Ncount 0 T : ℝ)^2 * ε := by
    change _ = 2 * ‖f‖ * (∑ i, ∑ j, k i j) + _
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      card_copies, nsmul_eq_mul]
    ring
  rw [gapFunctional_sub_mass, abs_div, abs_of_nonneg (sq_nonneg (Ncount 0 T : ℝ))]
  apply (div_le_div_of_nonneg_right ((abs_pair_sum_le T he).trans_eq hs) (sq_nonneg _)).trans_eq
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]

/-- Subtracting the constant boundary test leaves a term tending to zero. -/
theorem gapFunctional_centered_tendsto (w : (T : ℝ) → Copies T → Copies T → ℝ)
    (hw : ∀ T i j, |w T i j| ≤ 1) (f : GapTest) :
    Tendsto (fun T => gapFunctional T (w T) f - pairMass T (w T) * f OnePoint.infty)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := gap_test_outside f (half_pos hε)
  have ht := (windowCount_div_count_sq_tendsto_zero R).const_mul (2 * ‖f‖)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const (half_pos hε), eventually_count_pos] with T hb hN
  rw [Real.dist_eq, sub_zero]
  have he := gapFunctional_error_le hN (half_pos hε).le (w T) (hw T) f hR
  linarith only [hb, he]

/-- Weight d at the added point of the unfolded gap line. -/
def gapInfinityAtom (d : ℝ) : WeakDual ℝ GapTest :=
  StrongDual.toWeakDual (d • ContinuousMap.evalCLM ℝ OnePoint.infty : StrongDual ℝ GapTest)

/-- The total signed mass identifies the whole weak-star limit. -/
theorem gapFunctional_weakStar_tendsto (w : (T : ℝ) → Copies T → Copies T → ℝ)
    (hw : ∀ T i j, |w T i j| ≤ 1) {d : ℝ}
    (hm : Tendsto (fun T => pairMass T (w T)) atTop (𝓝 d)) :
    Tendsto (fun T => (gapFunctional T (w T)).toWeakDual) atTop (𝓝 (gapInfinityAtom d)) := by
  have hB : Function.Injective (topDualPairing ℝ GapTest) := by
    intro p q hp
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun l : GapTest →ₗ[ℝ] ℝ => l f) hp
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ GapTest) hB).mpr
  intro f
  change Tendsto (fun T => gapFunctional T (w T) f) atTop (𝓝 (d * f OnePoint.infty))
  simpa only [sub_add_cancel, zero_add] using
    (gapFunctional_centered_tendsto w hw f).add (hm.mul_const (f OnePoint.infty))

/-- Actual residual coefficients for a Hilbert projection, before any gap weighting. -/
def projectionPairWeight (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (T : ℝ) (i j : Copies T) : ℝ :=
  inner ℝ (S.starProjection (cosineRow (copyOrdinate T i)))
    (S.starProjection (cosineRow (copyOrdinate T j)))

private theorem projectionPairWeight_le (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] (T : ℝ) (i j : Copies T) :
    |projectionPairWeight S T i j| ≤ 1 := by
  have hn (t : ℝ) : ‖S.starProjection (cosineRow t)‖ ≤ 1 :=
    (S.norm_starProjection_apply_le _).trans (cosineRow_norm_le_one t)
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul (hn _) (hn _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem pairMass_projection_eq (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (T : ℝ) : pairMass T (projectionPairWeight S T) = ‖S.starProjection (recovery T 0)‖^2 := by
  let r (i : Copies T) := S.starProjection (cosineRow (copyOrdinate T i))
  have hS : S.starProjection (recovery T 0) = (Ncount 0 T : ℝ)⁻¹ • ∑ i, r i := by
    rw [recovery_zero_eq_mean, map_smul, map_sum]
    rfl
  have hi : inner ℝ (∑ i, r i) (∑ j, r j) = ∑ i, ∑ j, inner ℝ (r i) (r j) := by
    rw [sum_inner]
    simp_rw [inner_sum]
  rw [hS, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right, hi]
  change (∑ i, ∑ j, inner ℝ (r i) (r j)) / (Ncount 0 T : ℝ)^2 = _
  ring

/-- The escaped mass for the full legal residual is half the first-site vacancy. -/
theorem residualGap_weakStar_tendsto :
    Tendsto (fun T => (gapFunctional T (projectionPairWeight closedSpaceᗮ T)).toWeakDual)
      atTop (𝓝 (gapInfinityAtom ((1 - IntegerDPP.limitingKernel 0 0) / 2))) := by
  apply gapFunctional_weakStar_tendsto _ (projectionPairWeight_le _)
  simp_rw [pairMass_projection_eq]
  exact squaredError_tendsto

/-- Finite legal projections of any cofinal rank have the identical boundary coefficient. -/
theorem finiteResidualGap_weakStar_tendsto {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T =>
      (gapFunctional T (projectionPairWeight (finiteSpace (rank T))ᗮ T)).toWeakDual)
      atTop (𝓝 (gapInfinityAtom ((1 - IntegerDPP.limitingKernel 0 0) / 2))) := by
  apply gapFunctional_weakStar_tendsto _ (fun T => projectionPairWeight_le _ T)
  simpa only [pairMass_projection_eq, first_site_residual_sq] using
    (moving_residual_tendsto first_recovery_tendsto hr).norm.pow 2

theorem rh_iff_finiteResidualGap_weakStar_zero {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    RiemannHypothesis ↔ Tendsto (fun T =>
      (gapFunctional T (projectionPairWeight (finiteSpace (rank T))ᗮ T)).toWeakDual)
      atTop (𝓝 0) := by
  constructor
  · intro h
    have hz := rh_iff_first_site_vacancy_zero.mp h
    have hzero : gapInfinityAtom 0 = 0 := by
      unfold gapInfinityAtom
      rw [zero_smul]
      rfl
    simpa only [hz, hzero] using finiteResidualGap_weakStar_tendsto hr
  · intro h
    have he := tendsto_nhds_unique (finiteResidualGap_weakStar_tendsto hr) h
    have hc := congrArg (fun p : WeakDual ℝ GapTest =>
      p (ContinuousMap.const (OnePoint ℝ) (1 : ℝ))) he
    apply rh_iff_first_site_vacancy_zero.mpr
    change ((1 - IntegerDPP.limitingKernel 0 0) / 2) * 1 = 0 at hc
    simpa only [mul_one] using hc

/-- Absolute ordered-pair weight outside a fixed unfolded window. -/
def absoluteGapTail (T R : ℝ) (w : Copies T → Copies T → ℝ) : ℝ :=
  (∑ i, ∑ j, if R < |pairGap T i j| then |w i j| else 0) / (Ncount 0 T : ℝ)^2

theorem pairMass_le_window_add_tail (T R : ℝ) (w : Copies T → Copies T → ℝ)
    (hw : ∀ i j, |w i j| ≤ 1) :
    |pairMass T w| ≤ windowCount T R / (Ncount 0 T : ℝ)^2 + absoluteGapTail T R w := by
  rw [pairMass, absoluteGapTail, abs_div, abs_of_nonneg (sq_nonneg (Ncount 0 T : ℝ)), ← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  let g (i j : Copies T) := (if |pairGap T i j| ≤ R then (1 : ℝ) else 0) +
    (if R < |pairGap T i j| then |w i j| else 0)
  apply (abs_pair_sum_le T (g := g) (fun i j => by
    by_cases h : |pairGap T i j| ≤ R
    · simpa [g, h, not_lt_of_ge h] using hw i j
    · simp [g, h, lt_of_not_ge h])).trans_eq
  simp only [g, Finset.sum_add_distrib]
  rfl

/-- A uniform absolute-tail estimate for the finite legal residuals forces RH. -/
theorem rh_of_finiteResidualGap_tight {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ T : ℝ in atTop,
      absoluteGapTail T R (projectionPairWeight (finiteSpace (rank T))ᗮ T) ≤ ε) :
    RiemannHypothesis := by
  let w (T : ℝ) := projectionPairWeight (finiteSpace (rank T))ᗮ T
  have hzero : Tendsto (fun T => pairMass T (w T)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := htight _ (half_pos hε)
    filter_upwards [(windowCount_div_count_sq_tendsto_zero R).eventually_lt_const (half_pos hε),
      hR] with T hwin htail
    rw [Real.dist_eq, sub_zero]
    have h := pairMass_le_window_add_tail T R (w T) (projectionPairWeight_le _ T)
    change absoluteGapTail T R (w T) ≤ ε / 2 at htail
    linarith only [h, hwin, htail]
  have hactual : Tendsto (fun T => pairMass T (w T)) atTop
      (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 2)) := by
    simpa only [w, pairMass_projection_eq, first_site_residual_sq] using
      (moving_residual_tendsto first_recovery_tendsto hr).norm.pow 2
  exact rh_iff_first_site_vacancy_zero.mpr (tendsto_nhds_unique hactual hzero)

/-- Residual pair weight in the two disjoint quarter intervals. -/
def separatedGapWeight (n : ℕ) (T : ℝ) (i j : Copies T) : ℝ :=
  bandWeight ((1/4) * T) ((1/2) * T) (copyOrdinate T i) *
    bandWeight ((3/4) * T) (1 * T) (copyOrdinate T j) *
    projectionPairWeight (finiteSpace n)ᗮ T i j

/-- The separated-interval statistic contributes one sixteenth of the total boundary mass. -/
theorem separatedGap_weakStar_tendsto {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T => (gapFunctional T (separatedGapWeight (rank T) T)).toWeakDual) atTop
      (𝓝 (gapInfinityAtom ((1 - IntegerDPP.limitingKernel 0 0) / 32))) := by
  apply gapFunctional_weakStar_tendsto
  · intro T i j
    unfold separatedGapWeight bandWeight
    split_ifs <;> simp [projectionPairWeight_le]
  · apply (finiteSeparatedGram_tendsto first_recovery_tendsto hr).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact projected_bands_eq_pair_sum (finiteSpace (rank T))ᗮ.starProjection
      (show (1/4 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
      (show (3/4 : ℝ) ≤ 1 by norm_num) le_rfl hT

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.gapFunctional_weakStar_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gapFunctional_weakStar_tendsto

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_finiteResidualGap_weakStar_zero' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_finiteResidualGap_weakStar_zero

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.separatedGap_weakStar_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms separatedGap_weakStar_tendsto

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_of_finiteResidualGap_tight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_of_finiteResidualGap_tight

end RiemannResearch.RH.Pareto.OrdinateCosine

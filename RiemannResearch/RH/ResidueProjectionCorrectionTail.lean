import RiemannResearch.RH.ExactHeadCofinalBounds
import RiemannResearch.RH.ResidueGramMobiusCorrection
import RiemannResearch.RH.ExactHeadCoefficientCounterexample
import RiemannResearch.RH.CanonicalMobiusSignedAverages

/-!
# Exact arithmetic tails representing the canonical coefficient correction

Source: user-provided Pareto projection continuation, 22 September 2026,
equations (35)--(44), for the statements and proof strategy.

Stage n spans g_2,...,g_(n+1). The actual tail used here is
T_(n+1) = 1 - canonicalMobiusHilbert n. Equivalently it is the natural
Möbius residual through n+1 minus (n+1)m_(n+1)g_(n+1); the terminal
Möbius term cancels in that expression. The imported definition retains
the complete infinite Hilbert sequence. Its first n physical values vanish.

Established: each old canonical coefficient correction is an exact pairing
of this arithmetic tail with the projected finite-support Riesz vector;
the pairing equals an entire weighted tail sum; Cauchy--Schwarz retains
both complete norms. The projected dual's moving-tail energy tends to zero.

CONDITIONAL RESEARCH REDUCTIONS: product decay or a common energy bound
at arbitrarily late arithmetic tails forces full canonical projection
convergence and hence RH. A bounded cofinal subsequence suffices. The
required arithmetic bound is not asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative
open GramMobiusCorrection

/-- The actual finite-support Riesz vector for the signed coefficient functional. -/
def coefficientRiesz (d : ℕ) : ThresholdHilbert := -mobiusRieszHilbert d

theorem coefficientRiesz_inner (d : ℕ) (f : ThresholdHilbert) :
    inner ℝ (coefficientRiesz d) f = coefficientCLM d f := by
  simp only [coefficientRiesz, inner_neg_left, mobiusRieszHilbert_inner,
    coefficientCLM, neg_apply]

theorem coefficientRiesz_sequence (d j : ℕ) (hd : 0 < d) :
    hilbertSequence (coefficientRiesz d) j =
      -((j : ℝ) * ((j : ℝ) + 1) * (dualCoeff d j : ℝ)) := by
  change hilbertSequenceLinear (-mobiusRieszHilbert d) j = _
  rw [map_neg]
  change -hilbertSequence (mobiusRieszHilbert d) j = _
  rw [mobiusRieszHilbert_sequence d j hd]

theorem coefficientRiesz_sequence_zero (d j : ℕ) (hd : 0 < d) (hj : d < j) :
    hilbertSequence (coefficientRiesz d) j = 0 := by
  rw [coefficientRiesz_sequence d j hd, dualCoeff_eq_zero_of_lt hd hj]
  simp

/-- The manuscript's T_N, with N=n+1, using the existing arithmetic construction. -/
def tailError (n : ℕ) : ThresholdHilbert := hilbertOne - canonicalMobiusHilbert n

/-- Explicit finite arithmetic formula, before any head or tail restriction. -/
theorem tailError_eq_finite_combination (n : ℕ) :
    tailError n = hilbertOne +
      (∑ d ∈ (Finset.Icc 1 n).attach,
        (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
          normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1) -
      (((n+1 : ℕ) : ℝ) * mobiusReciprocalSum n) •
        normalizedResidueHilbert (n+1) (Nat.succ_pos _) := by
  unfold tailError canonicalMobiusHilbert
  abel

theorem tailError_head (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    hilbertSequence (tailError n) j = 0 := by
  change hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert n) j = 0
  rw [map_sub]
  change hilbertSequence hilbertOne j - hilbertSequence (canonicalMobiusHilbert n) j = 0
  rw [canonicalMobiusHilbert_exact n j hj hjn, hilbertOne_sequence]
  simp [zeroAnchor, ne_of_gt hj]

/-- Physical indices 1,...,n correspond to l2 coordinates 0,...,n-1. -/
theorem tailError_coordinate_zero (n k : ℕ) (hk : k < n) : tailError n k = 0 := by
  have hs := tailError_head n (k+1) (by omega) (by omega)
  rw [hilbertSequence_succ] at hs
  have hw : Real.sqrt (paretoWeight k) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  exact (div_eq_zero_iff.mp hs).resolve_right hw

theorem projection_tailError (n : ℕ) :
    (finiteSpace n).starProjection (tailError n) =
      projection n - canonicalMobiusHilbert n := by
  unfold tailError
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
    (canonicalMobiusHilbert_mem_finiteSpace n)]
  rfl

theorem tailError_projection_residual (n : ℕ) :
    tailError n - (finiteSpace n).starProjection (tailError n) =
      hilbertOne - projection n := by
  rw [projection_tailError]
  unfold tailError
  abel

/-- Optimality gives this exact split; it supplies no uniform bound for tailError. -/
theorem tailError_energy_split (n : ℕ) :
    ‖tailError n‖^2 = ‖hilbertOne - projection n‖^2 +
      ‖(finiteSpace n).starProjection (tailError n)‖^2 := by
  let e := tailError n
  let p := (finiteSpace n).starProjection e
  have ho : inner ℝ (e-p) p = 0 :=
    Submodule.starProjection_inner_eq_zero e p
      ((finiteSpace n).starProjection_apply_mem e)
  have ho' : inner ℝ p (e-p) = 0 := by rw [real_inner_comm]; exact ho
  rw [← tailError_projection_residual n]
  change ‖e‖^2 = ‖e-p‖^2 + ‖p‖^2
  have he : e = (e-p)+p := by abel
  calc
    ‖e‖^2 = inner ℝ ((e-p)+p) ((e-p)+p) := by
      rw [real_inner_self_eq_norm_sq, ← he]
    _ = ‖e-p‖^2 + ‖p‖^2 := by
      rw [inner_add_left, inner_add_right, inner_add_right, ho, ho',
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring

/-- Every old coefficient of the projected arithmetic tail is the actual correction. -/
theorem coefficient_projected_tailError (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    coefficientCLM d ((finiteSpace n).starProjection (tailError n)) =
      correction n d := by
  rw [projection_tailError, map_sub,
    coefficientCLM_eq_mobius_of_exact_head _ n d hd hdn
      (canonicalMobiusHilbert_exact n)]
  change coefficient n d - -(ArithmeticFunction.moebius d : ℝ) = correction n d
  unfold correction
  ring

/-- Self-adjointness transfers the finite coefficient functional onto its projected dual. -/
theorem correction_eq_pairing (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    correction n d =
      inner ℝ ((finiteSpace n).starProjection (coefficientRiesz d)) (tailError n) := by
  rw [← coefficient_projected_tailError n d hd hdn, ← coefficientRiesz_inner,
    ← (finiteSpace n).inner_starProjection_left_eq_right]

/-- Exact tail restriction: there are no omitted head or mixed terms. -/
theorem correction_eq_tail_pairing (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    correction n d = inner ℝ
      (hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) n)
      (hilbertTailShift (tailError n) n) := by
  rw [hilbertTailShift_inner _ _ n (tailError_coordinate_zero n)]
  exact correction_eq_pairing n d hd hdn

/-- Equation (41), expressed as the entire physical Pareto tail beginning at n+1. -/
theorem correction_eq_weighted_tail (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    correction n d = ∑' k : ℕ, positiveWeight (k+n+1) *
      (hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) (k+n+1) *
        hilbertSequence (tailError n) (k+n+1)) := by
  rw [correction_eq_tail_pairing n d hd hdn, hilbertTailShift_inner_weighted]

def projectedDualTailEnergy (n d : ℕ) : ℝ :=
  ‖hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) n‖^2

/-- The complete signed pairing is bounded by two complete, untruncated energies. -/
theorem correction_sq_le_tail_product (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    (correction n d)^2 ≤ ‖tailError n‖^2 * projectedDualTailEnergy n d := by
  rw [correction_eq_pairing n d hd hdn]
  simpa only [projectedDualTailEnergy, mul_comm] using
    hilbertTailShift_inner_sq_le
      ((finiteSpace n).starProjection (coefficientRiesz d)) (tailError n) n
      (tailError_coordinate_zero n)

private theorem tailShift_norm_le (f : ThresholdHilbert) (n : ℕ) :
    ‖hilbertTailShift f n‖ ≤ ‖f‖ := by
  have hs := hilbertTailShift_norm_sq f n
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, (f k)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (hilbertTailShift f n), norm_nonneg f]

private theorem tailShift_norm_le_difference (f g : ThresholdHilbert) (n : ℕ) :
    ‖hilbertTailShift f n‖ ≤ ‖f-g‖ + ‖hilbertTailShift g n‖ := by
  have he : hilbertTailShift f n =
      hilbertTailShift (f-g) n + hilbertTailShift g n := by
    change hilbertTailShiftLinear n f =
      hilbertTailShiftLinear n (f-g) + hilbertTailShiftLinear n g
    rw [map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add (tailShift_norm_le (f-g) n) le_rfl)

/-- Strong projection convergence suffices for the moving dual tail, with no RH premise. -/
theorem projectedDualTailEnergy_tendsto_zero (d : ℕ) :
    Tendsto (fun n => projectedDualTailEnergy n d) atTop (𝓝 0) := by
  let h : ThresholdHilbert := coefficientRiesz d
  let p : ThresholdHilbert := closedSpace.starProjection h
  have hp : Tendsto (fun n => (finiteSpace n).starProjection h) atTop (𝓝 p) :=
    walkProjection_tendsto residueAtom id Function.surjective_id h
  have hdiff : Tendsto (fun n => ‖(finiteSpace n).starProjection h-p‖^2)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (hp.sub_const p).norm.pow 2
  have hfixed := hilbertTailShift_energy_tendsto_zero p
  have hupper : Tendsto (fun n =>
      2 * ‖(finiteSpace n).starProjection h-p‖^2 +
        2 * ‖hilbertTailShift p n‖^2) atTop (𝓝 0) := by
    simpa using (hdiff.const_mul 2).add (hfixed.const_mul 2)
  apply squeeze_zero (fun n => sq_nonneg _) _ hupper
  intro n
  have hb := tailShift_norm_le_difference ((finiteSpace n).starProjection h) p n
  have hn0 := norm_nonneg (hilbertTailShift ((finiteSpace n).starProjection h) n)
  have hn1 := norm_nonneg ((finiteSpace n).starProjection h-p)
  have hn2 := norm_nonneg (hilbertTailShift p n)
  have hb2 := (sq_le_sq₀ hn0 (add_nonneg hn1 hn2)).mpr hb
  change ‖hilbertTailShift ((finiteSpace n).starProjection h) n‖^2 ≤ _
  nlinarith [sq_nonneg (‖(finiteSpace n).starProjection h-p‖ - ‖hilbertTailShift p n‖)]

/-- Conditional research reduction: decay of the actual arithmetic products is OPEN. -/
theorem correction_limits_of_tail_products
    (hprod : ∀ d : ℕ, 1 < d →
      Tendsto (fun n => ‖tailError n‖^2 * projectedDualTailEnergy n d) atTop (𝓝 0)) :
    ∀ d : ℕ, 1 < d → Tendsto (fun n => correction n d) atTop (𝓝 0) := by
  intro d hd
  have hs : Tendsto (fun n => (correction n d)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _)) _ (hprod d hd)
    filter_upwards [eventually_ge_atTop d] with n hn
    exact correction_sq_le_tail_product n d hd hn
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero,
    Real.norm_eq_abs] using ht

/-- Conditional RH endpoint. The dual-tail decay alone does not discharge hprod. -/
theorem riemannHypothesis_of_tail_products
    (hprod : ∀ d : ℕ, 1 < d →
      Tendsto (fun n => ‖tailError n‖^2 * projectedDualTailEnergy n d) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_correction_limits (correction_limits_of_tail_products hprod)

/-- Bounded arithmetic errors at arbitrarily late indices force the actual
canonical projection errors to vanish. No RH-to-density converse is used. -/
theorem projection_norm_tendsto_zero_of_cofinal_bounded_tailError (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ ‖tailError n‖^2 ≤ C) :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) := by
  apply projection_norm_tendsto_zero_iff_mem.mpr
  apply limitEnergy_zero_iff_mem.mp
  exact limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors
    canonicalMobiusHilbert canonicalMobiusHilbert_mem_closedSpace
    canonicalMobiusHilbert_exact C hbound

/-- Conditional research reduction: the cofinal arithmetic bound remains OPEN. -/
theorem riemannHypothesis_of_cofinal_bounded_tailError (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ ‖tailError n‖^2 ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (projection_norm_tendsto_zero_of_cofinal_bounded_tailError C hbound)

/-- Any cofinal sequence of bounded arithmetic errors suffices;
strict monotonicity of the selected indices is unnecessary. -/
theorem projection_norm_tendsto_zero_of_subsequence_bounded_tailError
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop) (C : ℝ)
    (hbound : ∀ k : ℕ, ‖tailError (s k)‖^2 ≤ C) :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) := by
  apply projection_norm_tendsto_zero_of_cofinal_bounded_tailError C
  intro M
  obtain ⟨k, hk⟩ := ((tendsto_atTop.mp hs) M).exists
  exact ⟨s k, hk, hbound k⟩

/-- A sufficient arithmetic bound; no provider of hbound is asserted. -/
theorem riemannHypothesis_of_bounded_tailError (C : ℝ)
    (hbound : ∀ n, ‖tailError n‖^2 ≤ C) : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_bounded_tailError C
    (fun M => ⟨M, le_rfl, hbound M⟩)

private theorem coefficient_normalizedResidue (d m : ℕ) (hd : 1 < d) (hm : 0 < m) :
    coefficientCLM d (normalizedResidueHilbert m hm) = if d = m then 1 else 0 := by
  simp only [coefficientCLM, neg_apply, mobius_normalizedResidue d m hd hm]
  split_ifs <;> norm_num

/-- The terminal coefficient follows from the actual finite arithmetic definition. -/
theorem canonicalMobiusHilbert_terminal_coefficient (n : ℕ) :
    coefficientCLM (n+2) (canonicalMobiusHilbert (n+1)) =
      ((n+2 : ℕ) : ℝ) * mobiusReciprocalSum (n+1) := by
  unfold canonicalMobiusHilbert
  simp only [map_add, map_neg, map_sum, map_smul]
  have hzero :
      (∑ d ∈ (Finset.Icc 1 (n+1)).attach,
        (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
          coefficientCLM (n+2)
            (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [coefficient_normalizedResidue (n+2) d (by omega)
      (Finset.mem_Icc.mp d.property).1]
    have hne : n+2 ≠ (d : ℕ) := by
      have hupper := (Finset.mem_Icc.mp d.property).2
      omega
    simp [hne]
  rw [hzero, coefficient_normalizedResidue (n+2) ((n+1)+1) (by omega) (by omega)]
  simp [show n+1+1 = n+2 by omega]

private theorem finiteSpace_ext_coefficients (n : ℕ)
    {f g : ThresholdHilbert} (hf : f ∈ finiteSpace n) (hg : g ∈ finiteSpace n)
    (he : ∀ i : Fin n,
      coefficientCLM (i.val+2) f = coefficientCLM (i.val+2) g) : f = g := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n f hf
  obtain ⟨b, hb⟩ := finiteSpace_expansion n g hg
  have hab : a = b := by
    funext i
    have hh := he i
    rw [ha, hb, coefficient_finite_sum, coefficient_finite_sum] at hh
    exact hh
  rw [ha, hb, hab]

/-- No reindexing convention is left implicit: all finite coefficients agree. -/
theorem canonicalMobiusHilbert_eq_mobiusSynthesis (n : ℕ) :
    canonicalMobiusHilbert (n+1) = -mobiusSynthesis (n+1) +
      (((n+2 : ℕ) : ℝ) * mobiusReciprocalSum (n+2)) • residueAtom n := by
  have hs : mobiusSynthesis (n+1) ∈ finiteSpace (n+1) := by
    unfold mobiusSynthesis
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have hg : residueAtom n ∈ finiteSpace (n+1) := by
    apply Submodule.subset_span
    exact ⟨Fin.last n, rfl⟩
  have hcoeff (i : Fin (n+1)) :
      coefficientCLM (i.val+2) (mobiusSynthesis (n+1)) =
        (ArithmeticFunction.moebius (i.val+2) : ℝ) := by
    simpa only [mobiusSynthesis, mobiusVector] using
      coefficient_finite_sum (n+1) (mobiusVector (n+1)) i
  apply finiteSpace_ext_coefficients (n+1)
    (canonicalMobiusHilbert_mem_finiteSpace (n+1))
    ((finiteSpace (n+1)).add_mem ((finiteSpace (n+1)).neg_mem hs)
      ((finiteSpace (n+1)).smul_mem _ hg))
  intro i
  rw [map_add, map_neg, map_smul, hcoeff, coefficientCLM_biorthogonal]
  by_cases hi : i.val = n
  · rw [hi, canonicalMobiusHilbert_terminal_coefficient, if_pos rfl]
    have hm : mobiusReciprocalSum (n+2) = mobiusReciprocalSum (n+1) +
        (ArithmeticFunction.moebius (n+2) : ℝ) / ((n+2 : ℕ) : ℝ) := by
      unfold mobiusReciprocalSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hm]
    simp only [smul_eq_mul, mul_one]
    have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hn]
    ring
  · rw [coefficientCLM_eq_mobius_of_exact_head _ (n+1) (i.val+2)
      (by omega) (by omega) (canonicalMobiusHilbert_exact (n+1)), if_neg hi]
    simp

/-- Exact manuscript formula T_N=R_N-N*m_N*g_N, with N=n+2. -/
theorem tailError_eq_mobiusResidual_sub (n : ℕ) :
    tailError (n+1) = mobiusResidual (n+1) -
      (((n+2 : ℕ) : ℝ) * mobiusReciprocalSum (n+2)) • residueAtom n := by
  rw [tailError, canonicalMobiusHilbert_eq_mobiusSynthesis]
  unfold mobiusResidual
  abel

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

import RiemannResearch.Analysis.MontgomerySampledArgumentError
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannResearch.Analysis.FirstHarmonicCounts
import RiemannResearch.Analysis.MontgomerySampledCountError

/-! # Modular probes of the discrepancy and forward neighbor counts

The circle characters of the discrepancy remove integer counts. A separate
first harmonic of the integer count retains its mean up to an explicit error.
The local-count convention is the one in MontgomerySampledArgumentError.
-/

noncomputable section

open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroDiscrepancy DyadicZeroWasserstein

/-- The integer Fourier character on the additive circle, pulled back to the reals. -/
def incrementCharacter (k : ℤ) (s : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * (s : ℂ))

theorem incrementCharacter_int_add (k m : ℤ) (s : ℝ) :
    incrementCharacter k ((m : ℝ) + s) = incrementCharacter k s := by
  unfold incrementCharacter
  push_cast
  have h :
      2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((m : ℂ) + (s : ℂ)) =
        ((k * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (s : ℂ) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The full character of the signed argument increment is exactly the character
of the negative smooth gamma increment, even at zero ordinates. -/
theorem discrepancy_incrementCharacter (k : ℤ) (t u : ℝ) :
    incrementCharacter k (discrepancy u - discrepancy t) =
      incrementCharacter k (-(smoothCount u - smoothCount t)) := by
  let m : ℤ := (Ncount 0 u : ℤ) - (Ncount 0 t : ℤ)
  have h : discrepancy u - discrepancy t =
      (m : ℝ) + -(smoothCount u - smoothCount t) := by
    unfold discrepancy
    dsimp only [m]
    push_cast
    ring
  rw [h, incrementCharacter_int_add]

/-- The count disappears separately in each clipped row, with the repository's
occurrence index and exact gamma convention. -/
theorem clipped_occurrence_incrementCharacter (k : ℤ) (T R : ℝ) (i : Copies T) :
    let t := copyOrdinate T i
    let u := min T (t + R / unfoldingScale T)
    incrementCharacter k (discrepancy u - discrepancy t) =
      incrementCharacter k (-(smoothCount u - smoothCount t)) :=
  discrepancy_incrementCharacter k _ _

/-- Summation over the rows preserves the exact identity and every multiplicity. -/
theorem sampled_incrementCharacter_eq_gamma (k : ℤ) (T R : ℝ) :
    (∑ i : Copies T,
      incrementCharacter k
        (discrepancy (min T (copyOrdinate T i + R / unfoldingScale T)) -
          discrepancy (copyOrdinate T i))) =
    ∑ i : Copies T,
      incrementCharacter k
        (-(smoothCount (min T (copyOrdinate T i + R / unfoldingScale T)) -
          smoothCount (copyOrdinate T i))) := by
  exact Finset.sum_congr rfl (fun i _ => clipped_occurrence_incrementCharacter k T R i)

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.sampled_incrementCharacter_eq_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sampled_incrementCharacter_eq_gamma

private theorem norm_incrementCharacter (k : ℤ) (s : ℝ) :
    ‖incrementCharacter k s‖ = 1 := by
  rw [incrementCharacter, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- At each fixed positive unfolded width the discrepancy-increment phases,
sampled with multiplicity, concentrate at the phase of the negative width. -/
theorem sampled_incrementCharacter_concentrates (k : ℤ) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ =>
      (∑ i : Copies T, ‖incrementCharacter k
        (discrepancy (min T (copyOrdinate T i + R / unfoldingScale T)) -
          discrepancy (copyOrdinate T i)) - incrementCharacter k (-R)‖) /
          unfoldedCutoff T) atTop (𝓝 0) := by
  classical
  let drift := fun (T : ℝ) (i : Copies T) =>
    smoothCount (min T (copyOrdinate T i + R/unfoldingScale T)) - smoothCount (copyOrdinate T i)
  let ψ := fun y : ℝ => incrementCharacter k (-y)
  let e := fun (T : ℝ) (i : Copies T) => ‖ψ (drift T i) - ψ R‖
  have he (T : ℝ) (i : Copies T) : 0 ≤ e T i := norm_nonneg _
  have hψ (y : ℝ) : ‖ψ y‖ = 1 := norm_incrementCharacter k (-y)
  have hglobal (T : ℝ) (i : Copies T) : e T i ≤ 2 := by
    calc
      _ ≤ ‖ψ (drift T i)‖ + ‖ψ R‖ := norm_sub_le _ _
      _ = 2 := by rw [hψ, hψ]; norm_num
  have hcont : Continuous ψ := by unfold ψ incrementCharacter; fun_prop
  have hinterior {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
      ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, δ*T ≤ copyOrdinate T i →
        copyOrdinate T i ≤ (1-δ)*T → e T i ≤ ε := by
    have hcontR : ContinuousAt ψ R := hcont.continuousAt
    obtain ⟨η,hη,hu⟩ := Metric.continuousAt_iff.mp hcontR ε hε
    filter_upwards [eventually_gamma_increment_interior hR hδ (half_pos hη)]
      with T hT i hl hr
    have hd : |drift T i - R| ≤ η/2 := hT i hl hr
    have hdist : dist (drift T i) R < η := by rw [Real.dist_eq]; linarith
    exact (show ‖ψ (drift T i) - ψ R‖ < ε by simpa [dist_eq_norm] using hu hdist).le
  have havg := ordinateRowMean_tendsto_of_interior (f := fun T i => e T i + 1)
    (by refine ⟨1, by norm_num, Eventually.of_forall fun T i => ?_⟩
        simpa only [add_sub_cancel_right, abs_of_nonneg (he T i), one_add_one_eq_two]
          using hglobal T i)
    (by intro δ ε hδ hε
        filter_upwards [hinterior hδ hε] with T hT i hl hr
        simpa only [add_sub_cancel_right, abs_of_nonneg (he T i)] using hT i hl hr)
  have hN : Tendsto (fun T : ℝ => (Ncount 0 T : ℝ) / unfoldedCutoff T) atTop (𝓝 1) :=
    tendsto_count_div_mainTerm
  have h := havg.sub hN
  rw [sub_self] at h
  apply h.congr'
  apply Eventually.of_forall
  intro T
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_copies, nsmul_eq_mul, mul_one, add_div, add_sub_cancel_right]
  apply congrArg (fun y : ℝ => y / unfoldedCutoff T)
  apply Finset.sum_congr rfl
  intro i _
  change ‖incrementCharacter k (-(drift T i)) - ψ R‖ = _
  rw [clipped_occurrence_incrementCharacter k T R i]


open ActualZeroOrdinate FirstHarmonicCounts

/-- The count in the clipped forward window of an actual zero occurrence. -/
def clippedOccurrenceCount (T q : ℝ) (i : Copies T) : ℕ :=
  Ncount (copyOrdinate T i) (min T (copyOrdinate T i + q / unfoldingScale T))

def occurrenceModulus (T : ℝ) : ℕ := (Ncount 0 T + 1) ^ 2
def occurrenceAngle (T : ℝ) : ℝ := 2 * Real.pi / (occurrenceModulus T : ℝ)

/-- Imaginary part of the first circular harmonic, in count units. -/
def occurrenceFirstHarmonic (T q : ℝ) : ℝ :=
  (∑ i : Copies T, Real.sin (occurrenceAngle T * clippedOccurrenceCount T q i) /
    occurrenceAngle T) / unfoldedCutoff T

/-- Uniform in the positive unfolded width, without a row-moment assumption. -/
theorem positiveGapMass_sub_firstHarmonic_bound {T q : ℝ} (hT : 1 < T) (hq : 0 < q) :
    |positiveGapMass T q - occurrenceFirstHarmonic T q| ≤
      ((2 * Real.pi) ^ 2 / 6) / unfoldedCutoff T := by
  classical
  let n : ℝ := Ncount 0 T
  let K := fun i : Copies T => (clippedOccurrenceCount T q i : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hD : 0 < unfoldedCutoff T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hL : 0 < unfoldingScale T := div_pos (Real.log_pos hT) (by positivity)
  have hangle : occurrenceAngle T = 2 * Real.pi / (n + 1) ^ 2 := by
    simp [occurrenceAngle, occurrenceModulus, n]
  have ht : 0 < occurrenceAngle T := by rw [hangle]; positivity
  have hk (i : Copies T) : K i ≤ n := by
    have hi : 0 ≤ copyOrdinate T i := (mem_cutoff.mp i.1.property).2.1.le
    change (Ncount (copyOrdinate T i)
      (min T (copyOrdinate T i + q / unfoldingScale T)) : ℝ) ≤ (Ncount 0 T : ℝ)
    exact_mod_cast (Ncount_mono hi (min_le_left T (copyOrdinate T i + q / unfoldingScale T)))
  have hc : (∑ i : Copies T, K i ^ 3) ≤ (n + 1) ^ 4 := by
    calc
      _ ≤ ∑ _i : Copies T, (n + 1) ^ 3 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (Nat.cast_nonneg _) ((hk i).trans (by linarith)) _
      _ = n * (n + 1) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, n]
      _ ≤ (n + 1) * (n + 1) ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hr := abs_sum_sub_sin_le_third_moment Finset.univ K ht (fun i _ => Nat.cast_nonneg _)
  have hp := positiveGapMass_eq_ordinate_window_counts hT (div_pos hq hL)
  rw [div_mul_cancel₀ _ hL.ne'] at hp
  rw [hp, occurrenceFirstHarmonic, ← sub_div, abs_div, abs_of_pos hD]
  apply div_le_div_of_nonneg_right _ hD.le
  apply hr.trans
  calc
    _ ≤ occurrenceAngle T ^ 2 / 6 * (n + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [hangle]; field_simp [show n + 1 ≠ 0 by positivity]

theorem positiveGapPCC_iff_occurrenceFirstHarmonic :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => occurrenceFirstHarmonic T q)
      atTop (𝓝 (sineGapMass q)) := by
  rw [positiveGapPCC_iff_rationalWidthLimits]
  have he (q : ℚ) (hq : 0 < q) :
      Tendsto (fun T : ℝ => positiveGapMass T q - occurrenceFirstHarmonic T q) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      exact positiveGapMass_sub_firstHarmonic_bound hT (by exact_mod_cast hq)
    · have hD : Tendsto unfoldedCutoff atTop atTop :=
        (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
      exact tendsto_const_nhds.div_atTop hD
  constructor <;> intro h q hq
  · simpa using (h q hq).sub (he q hq)
  · simpa using (he q hq).add (h q hq)

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.sampled_incrementCharacter_concentrates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sampled_incrementCharacter_concentrates

/-- info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_occurrenceFirstHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_occurrenceFirstHarmonic

end RiemannResearch.Analysis.MontgomeryPositiveGap

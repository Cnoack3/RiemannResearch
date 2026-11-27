import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Round
import RiemannResearch.Analysis.MontgomeryAllPairWordLimit
import RiemannResearch.Analysis.MontgomeryEvenFourierTests
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroTriangularIntegral
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity

/-! # Signed Parseval formula for rounded empirical Fourier squares

Source: §4 of the user's Mellin/prime-orbit PCC handoff. Push the real Fourier
weight onto the integer rounding cells. Apply Haar Parseval on the unit circle
separately to the positive and negative cell masses. Every integer cell
and the complete forward atom are retained at each finite height.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace RiemannResearch.Analysis.RoundedFourierCellParseval

/-- Signed mass of the fiber of an integer-valued frequency map. -/
def cellMass (J : ℝ → ℤ) (w : ℝ → ℝ) (k : ℤ) : ℝ :=
  ∫ v in J ⁻¹' {k}, w v

/-- Integration of a bounded multiplier on the cells is its countably
infinite weighted sum. This uses absolute convergence at a fixed height. -/
theorem hasSum_cells {J : ℝ → ℤ} (hJ : Measurable J) {w : ℝ → ℝ}
    (hw : Integrable w) (a : ℤ → ℝ) {B : ℝ} (hb : ∀ k, |a k| ≤ B) :
    HasSum (fun k => cellMass J w k * a k) (∫ v, w v * a (J v)) := by
  let S := fun k : ℤ => J ⁻¹' {k}
  have hm : ∀ k, MeasurableSet (S k) := fun k => hJ (measurableSet_singleton k)
  have hd : Pairwise (fun k l => Disjoint (S k) (S l)) := by
    intro k l h
    exact Disjoint.preimage J (Set.disjoint_singleton.mpr h)
  have hu : (⋃ k, S k) = Set.univ := by
    ext v
    simp [S]
  have ha : Measurable (fun v => a (J v)) := (measurable_of_countable a).comp hJ
  have hint : Integrable (fun v => w v * a (J v)) :=
    hw.mul_bdd ha.aestronglyMeasurable (Filter.Eventually.of_forall fun v => by
      simpa [Real.norm_eq_abs] using hb (J v))
  have hi := hasSum_integral_iUnion hm hd (f := fun v => w v * a (J v))
    (by simpa only [hu, integrableOn_univ] using hint)
  rw [hu, setIntegral_univ] at hi
  have hf (k : ℤ) : cellMass J w k * a k = ∫ v in S k, w v * a (J v) := by
    unfold cellMass
    rw [← integral_mul_const]
    apply setIntegral_congr_fun (hm k)
    intro v hv
    change J v = k at hv
    simp only [hv]
  simpa only [hf] using hi
/-- Fourier series on the unit circle with coefficients
sqrt(max(b_k,0)) times the actual empirical amplitude. -/
def cellWave (b : ℤ → ℝ) (A : ℤ → ℂ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance) :=
  ∑' k, ((Real.sqrt (max (b k) 0) : ℂ) * A k) •
    (@fourierLp (1 : ℝ) inferInstance 2 inferInstance k)

/-- The positive cell masses define an L² series, with squared norm exactly
the untruncated positive weighted squared amplitude. -/
theorem cellWave_parseval {b : ℤ → ℝ} (hb : Summable b) (A : ℤ → ℂ) {B : ℝ}
    (hB : ∀ k, ‖A k‖ ≤ B) :
    Summable (fun k => ((Real.sqrt (max (b k) 0) : ℂ) * A k) •
      (@fourierLp (1 : ℝ) inferInstance 2 inferInstance k)) ∧
    ‖cellWave b A‖ ^ 2 = ∑' k, max (b k) 0 * ‖A k‖ ^ 2 := by
  let c : ℤ → ℂ := fun k => (Real.sqrt (max (b k) 0) : ℂ) * A k
  have hc (k : ℤ) : ‖c k‖ ^ 2 = max (b k) 0 * ‖A k‖ ^ 2 := by
    simp [c, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_max_right _ _)]
  have hsq : Summable (fun k => ‖c k‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ (hb.abs.mul_right (B^2))
    intro k
    rw [hc]
    exact mul_le_mul (max_le (le_abs_self _) (abs_nonneg _))
      (pow_le_pow_left₀ (norm_nonneg _) (hB k) 2) (sq_nonneg _) (abs_nonneg _)
  let h := (@orthonormal_fourier (1 : ℝ) inferInstance).orthogonalFamily
  let x : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨c, (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by simpa using hsq)⟩
  refine ⟨h.summable_of_lp x, ?_⟩
  change ‖h.linearIsometry x‖ ^ 2 = _
  rw [LinearIsometry.norm_map]
  simpa [x, hc] using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

/-- Exact signed energy, with an arbitrary constant forward-atom subtraction. -/
theorem signed_cell_energy {J : ℝ → ℤ} (hJ : Measurable J) {w : ℝ → ℝ}
    (hw : Integrable w) (A : ℤ → ℂ) {B : ℝ} (hB : ∀ k, ‖A k‖ ≤ B) (C : ℝ) :
    (∫ v, w v * (‖A (J v)‖ ^ 2 - C)) =
      ‖cellWave (cellMass J w) A‖ ^ 2 -
      ‖cellWave (fun k => -cellMass J w k) A‖ ^ 2 - C * ∫ v, w v := by
  let b := cellMass J w
  have hsum : HasSum b (∫ v, w v) := by
    simpa [b] using hasSum_cells hJ hw (fun _ => 1) (B := 1) (by simp)
  have hp := (cellWave_parseval hsum.summable A hB).2
  have hn := (cellWave_parseval hsum.summable.neg A hB).2
  let E := fun k : ℤ => ‖A k‖^2
  have hpS : Summable (fun k => max (b k) 0 * E k) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      _ (hsum.summable.abs.mul_right (B^2))
    exact fun k => mul_le_mul (max_le (le_abs_self _) (abs_nonneg _))
      (pow_le_pow_left₀ (norm_nonneg _) (hB k) 2) (sq_nonneg _) (abs_nonneg _)
  have hnS : Summable (fun k => max (-b k) 0 * E k) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      _ (hsum.summable.abs.mul_right (B^2))
    exact fun k => mul_le_mul (max_le (neg_le_abs _) (abs_nonneg _))
      (pow_le_pow_left₀ (norm_nonneg _) (hB k) 2) (sq_nonneg _) (abs_nonneg _)
  have hsigned := (hpS.hasSum.sub hnS.hasSum).sub (hsum.mul_right C)
  have ha (k : ℤ) : |E k - C| ≤ B ^ 2 + |C| := by
    have hEk : |E k| ≤ B ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB k) 2
    exact (abs_sub _ _).trans (add_le_add hEk le_rfl)
  have he := hasSum_cells hJ hw (fun k => E k - C) ha
  have hs : HasSum (fun k => b k * (E k - C))
      (‖cellWave b A‖^2 - ‖cellWave (fun k => -b k) A‖^2 - C * ∫ v, w v) := by
    rw [hp, hn, mul_comm C]
    have heq (k : ℤ) : b k * (E k - C) =
        max (b k) 0 * E k - max (-b k) 0 * E k - b k * C := by
      rcases le_total (b k) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
        ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
        ring
    simpa only [heq] using hsigned
  exact he.unique hs

/-- Unit phases on the actual word coefficients preserve the Haar energy
of each sign, including the phases induced by shifting the height origin. -/
theorem cellWave_gauge_norm_sq {b : ℤ → ℝ} (hb : Summable b) (A η : ℤ → ℂ)
    {B : ℝ} (hB : ∀ k, ‖A k‖ ≤ B) (hη : ∀ k, ‖η k‖ = 1) :
    ‖cellWave b (fun k => η k * A k)‖^2 = ‖cellWave b A‖^2 := by
  have h' : ∀ k, ‖η k * A k‖ ≤ B := by simpa [norm_mul, hη] using hB
  rw [(cellWave_parseval hb _ h').2, (cellWave_parseval hb A hB).2]
  simp [hη]

open Zeta23 ActualZeroOrdinate OrdinateCollisionCertificate ActualZeroCollisionCertificate

/-- Integer word order at each real Fourier frequency. -/
def roundedOrder (T h v : ℝ) : ℤ := round (Real.log T * v / h)

/-- The exact numerator in the rounded all-rank reconstruction. Each Fourier
coefficient in the two Parseval terms uses the actual multiplicity-weighted
zeta zero sum. The signed weight may be any integrable real function. -/
theorem actual_rounded_signed_parseval (T h : ℝ) {w : ℝ → ℝ} (hw : Integrable w) :
    let J := roundedOrder T h
    let A := fun k : ℤ => ordinateSum T ((k : ℝ) * h)
    let C := (occurrenceCollision (copyOrdinate T) : ℝ)
    (∫ v, w v * (Complex.normSq (occurrenceAmplitude (copyOrdinate T) ((J v : ℝ) * h)) - C)) =
      ‖cellWave (cellMass J w) A‖^2 - ‖cellWave (fun k => -cellMass J w k) A‖^2 -
        C * ∫ v, w v := by
  dsimp only
  have hm : Measurable (roundedOrder T h) := by
    unfold roundedOrder
    simp_rw [round_eq]
    exact Int.measurable_floor.comp (((measurable_const.mul measurable_id).div_const h).add_const _)
  simpa only [actual_occurrenceAmplitude, Complex.sq_norm] using signed_cell_energy hm hw
    (fun k : ℤ => ordinateSum T ((k : ℝ) * h))
    (fun k => norm_ordinateSum_le_count T ((k : ℝ) * h)) (occurrenceCollision (copyOrdinate T) : ℝ)

open MontgomeryAllPairWordRounding MontgomeryEvenFourierTests
open scoped FourierTransform SchwartzMap

/-- For an even Schwartz test the full forward-atom correction equals C f(0).
This identifies the repository's normalized rounded positive-gap test with
the signed difference of two genuine Haar L² norms at every finite height. -/
theorem roundedFourierTest_schwartz_parseval (T h : ℝ) (f : 𝓢(ℝ, ℂ))
    (heven : ∀ x, (f (-x)).re = (f x).re) :
    let w := fun v : ℝ => ((𝓕 f) v).re
    let b := cellMass (roundedOrder T h) w
    let A := fun k : ℤ => ordinateSum T ((k : ℝ) * h)
    roundedFourierTest T h w =
      (‖cellWave b A‖^2 - ‖cellWave (fun k => -b k) A‖^2 -
        (occurrenceCollision (copyOrdinate T) : ℝ) * (f 0).re) /
        (2 * (T * Real.log T / (2 * Real.pi))) := by
  have hzero := even_schwartz_cosine_inversion f heven 0
  simp only [zero_mul, mul_zero, Real.cos_zero, mul_one] at hzero
  exact congrArg (fun e : ℝ => e / (2 * (T * Real.log T / (2 * Real.pi))))
    ((actual_rounded_signed_parseval T h (integrable_schwartz_weight f)).trans (by rw [hzero]))

end RiemannResearch.Analysis.RoundedFourierCellParseval

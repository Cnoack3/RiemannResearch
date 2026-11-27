import RiemannResearch.Analysis.OrdinateTriangularIntegral
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import Mathlib.Algebra.Order.Round
import Mathlib.MeasureTheory.Function.Floor

/-!
# Rounding the Fourier frequency for every positive ordinate gap

For the Fourier reconstruction in §4 of the Mellin–prime orbit handoff
(27 November 2026), the exact forward atom counts all pairs at equal heights.
Rounding incurs an error bounded by the diameter times the number of ordered
pairs of distinct occurrence labels. The statements apply at arbitrary finite
height, before taking a pair-correlation limit.
-/

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Zeta23

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open OrdinateCollisionCertificate ActualZeroOrdinate

variable {ι : Type*} [Fintype ι]

/-- Strictly positive ordinate differences, with each occurrence counted. -/
def positiveTestSum (y : ι → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, ∑ j, if y j < y i then f (y i - y j) else 0

/-- Pairing a test with all ordered pairs separates its complete collision atom
and twice its strictly positive-gap pairing, when the test is even. -/
theorem even_pair_sum (y : ι → ℝ) (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x) :
    (∑ i, ∑ j, f (y i - y j)) =
      (occurrenceCollision y : ℝ) * f 0 + 2 * positiveTestSum y f := by
  let P (i j : ι) := if y j < y i then f (y i - y j) else 0
  have hp (i j : ι) : f (y i - y j) =
      (if y i = y j then (1 : ℝ) else 0) * f 0 + P i j + P j i := by
    rcases lt_trichotomy (y i) (y j) with h | h | h
    · have hf : f (y i - y j) = f (y j - y i) := by
        simpa only [neg_sub] using he (y j - y i)
      simp [P, h, h.ne, not_lt.mpr h.le, hf]
    · simp [P, h]
    · simp [P, h, h.ne', not_lt.mpr h.le]
  have hc : (occurrenceCollision y : ℝ) =
      ∑ i, ∑ j, if y i = y j then (1 : ℝ) else 0 := by
    simp [occurrenceCollision]
  have hs : (∑ i, ∑ j, P j i) = ∑ i, ∑ j, P i j := Finset.sum_comm
  simp_rw [hp, Finset.sum_add_distrib]
  rw [hs, hc]
  simp only [Finset.sum_mul, positiveTestSum, P]
  ring

/-- The collision-subtracted Fourier square represents every positive rank. -/
theorem normSq_sub_collision (y : ι → ℝ) (u : ℝ) :
    Complex.normSq (occurrenceAmplitude y u) - (occurrenceCollision y : ℝ) =
      2 * positiveTestSum y (fun d => Real.cos (d * u)) := by
  rw [occurrenceAmplitude_normSq]
  have h := even_pair_sum y (fun d => Real.cos (d * u)) (fun d => by simp)
  simpa only [zero_mul, Real.cos_zero, mul_one, add_sub_cancel_left] using
    congrArg (fun x : ℝ => x - (occurrenceCollision y : ℝ)) h

/-- Quantitative stability of the complete squared Fourier amplitude, with
the identical-label contributions removed from the error constant. -/
theorem normSq_frequency_error (y : ι → ℝ) {T : ℝ}
    (hy : ∀ i j, |y i - y j| ≤ T) (u v : ℝ) :
    |Complex.normSq (occurrenceAmplitude y u) -
        Complex.normSq (occurrenceAmplitude y v)| ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * (T * |u-v|) := by
  let d (i j : ι) := Real.cos ((y i - y j) * u) - Real.cos ((y i - y j) * v)
  have hd (i j : ι) : |d i j| ≤ T * |u-v| := by
    apply (Real.abs_cos_sub_cos_le _ _).trans
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hy i j) (abs_nonneg _)
  have hrow (i : ι) : (∑ j, |d i j|) ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) * (T * |u-v|) := by
    have hs := Finset.sum_erase_add (s := Finset.univ) (f := fun j => |d i j|)
      (Finset.mem_univ i)
    have he : (∑ j ∈ Finset.univ.erase i, |d i j|) = ∑ j, |d i j| := by
      simpa only [d, sub_self, zero_mul, abs_zero, add_zero] using hs
    rw [← he]
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, T * |u-v| := Finset.sum_le_sum fun j _ => hd i j
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp_rw [occurrenceAmplitude_normSq, ← Finset.sum_sub_distrib]
  change |∑ i, ∑ j, d i j| ≤ _
  calc
    _ ≤ ∑ i, |∑ j, d i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |d i j| := Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ((Fintype.card ι - 1 : ℕ) : ℝ) * (T * |u-v|) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp [mul_assoc]

/-- Fourier inversion in cosine-transform form, with an arbitrary measurable
frequency map. This also applies to the step function of rounded frequencies. -/
theorem integrated_normSq_sub_collision (y : ι → ℝ) {w φ : ℝ → ℝ}
    (hw : Integrable w) (hφ : Measurable φ) :
    (∫ v, w v * (Complex.normSq (occurrenceAmplitude y (φ v)) -
      (occurrenceCollision y : ℝ))) =
    2 * positiveTestSum y (fun d => ∫ v, w v * Real.cos (d * φ v)) := by
  let p (i j : ι) (v : ℝ) := if y j < y i then w v * Real.cos ((y i-y j) * φ v) else 0
  have hi (i j : ι) : Integrable (p i j) := by
    dsimp only [p]
    split_ifs
    · apply hw.mul_bdd (Real.continuous_cos.measurable.comp
        (measurable_const.mul hφ)).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.mul_apply] using Real.abs_cos_le_one ((y i-y j) * φ v)
    · exact integrable_zero _ _ _
  have he (v : ℝ) : w v * (Complex.normSq (occurrenceAmplitude y (φ v)) -
      (occurrenceCollision y : ℝ)) = 2 * (∑ i, ∑ j, p i j v) := by
    rw [normSq_sub_collision]
    rw [mul_left_comm, positiveTestSum]
    simp_rw [Finset.mul_sum]
    simp [p, mul_ite]
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hi i j))]
  congr 1
  unfold positiveTestSum
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : y j < y i <;> simp [p, h]

/-- An integrated all-rank estimate before normalization. A physical width
(T) and a frequency error (ε) enter multiplicatively with the L¹ weight. -/
theorem integrated_frequency_error (y : ι → ℝ) {T ε : ℝ}
    (hy : ∀ i j, |y i - y j| ≤ T) (hT : 0 ≤ T) {w φ ψ : ℝ → ℝ}
    (hw : Integrable w) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hε : ∀ v, |φ v - ψ v| ≤ ε) :
    |(∫ v, w v * (Complex.normSq (occurrenceAmplitude y (φ v)) -
          (occurrenceCollision y : ℝ))) -
      (∫ v, w v * (Complex.normSq (occurrenceAmplitude y (ψ v)) -
          (occurrenceCollision y : ℝ)))| ≤
    (∫ v, |w v|) * ((Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * (T * ε)) := by
  let E (θ : ℝ → ℝ) (v : ℝ) := Complex.normSq (occurrenceAmplitude y (θ v)) -
    (occurrenceCollision y : ℝ)
  have hint (θ : ℝ → ℝ) (hθ : Measurable θ) : Integrable (fun v => w v * E θ v) := by
    have he : (fun v => w v * E θ v) = fun v =>
        (∑ i, ∑ j, w v * Real.cos ((y i - y j) * θ v)) -
          w v * (occurrenceCollision y : ℝ) := by
      funext v
      simp only [E, occurrenceAmplitude_normSq, mul_sub, Finset.mul_sum]
    rw [he]
    apply Integrable.sub _ (hw.mul_const _)
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply hw.mul_bdd (Real.continuous_cos.measurable.comp
      (measurable_const.mul hθ)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.mul_apply] using Real.abs_cos_le_one ((y i-y j) * θ v)
  let K := (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * (T * ε)
  have he (v : ℝ) : |E φ v - E ψ v| ≤ K := by
    simpa only [E, sub_sub_sub_cancel_right, K] using
      (normSq_frequency_error y hy (φ v) (ψ v)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hε v) hT) (by positivity))
  change |(∫ v, w v * E φ v) - (∫ v, w v * E ψ v)| ≤ (∫ v, |w v|) * K
  rw [← integral_sub (hint φ hφ) (hint ψ hψ), ← integral_mul_const]
  calc
    _ ≤ ∫ v, |w v * E φ v - w v * E ψ v| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun v => w v * E φ v - w v * E ψ v)
    _ ≤ _ := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (hw.abs.mul_const _) (Filter.Eventually.of_forall fun v => by
        change |w v * E φ v - w v * E ψ v| ≤ |w v| * K
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (he v) (abs_nonneg _))

private theorem nearest_error (u : ℝ) {h : ℝ} (hh : 0 < h) :
    |u - (round (u/h) : ℝ) * h| ≤ h/2 := by
  calc
    _ = |u/h - (round (u/h) : ℝ)| * h := by
      rw [show u - (round (u/h) : ℝ) * h = (u/h - (round (u/h) : ℝ)) * h by
        rw [sub_mul, div_mul_cancel₀ _ hh.ne'], abs_mul, abs_of_pos hh]
    _ ≤ (1/2 : ℝ) * h := mul_le_mul_of_nonneg_right (abs_sub_round _) hh.le
    _ = _ := by ring

/-- Against an integrable real Fourier weight, nearest-frequency rounding
recovers the entire normalized positive-gap statistic, up to the error in
the handoff. The inversion hypothesis specifies the Fourier convention. -/
theorem rounded_positiveTestSum (y : ι → ℝ) {T D h : ℝ}
    (hy : ∀ i j, |y i-y j| ≤ T) (hT : 0 ≤ T) (hD : 0 < D) (hh : 0 < h)
    {w φ f : ℝ → ℝ} (hw : Integrable w) (hφ : Measurable φ)
    (hinv : ∀ d, f d = ∫ v, w v * Real.cos (d * φ v)) :
    |positiveTestSum y f / D -
      (∫ v, w v * (Complex.normSq (occurrenceAmplitude y ((round (φ v / h) : ℝ) * h)) -
        (occurrenceCollision y : ℝ))) / (2*D)| ≤
      (∫ v, |w v|) * (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * h*T / (4*D) := by
  let ψ (v : ℝ) := (round (φ v/h) : ℝ) * h
  have hψ : Measurable ψ := by
    unfold ψ
    simp_rw [round_eq]
    exact ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp ((hφ.div_const h).add_const _))).mul_const h
  have hexact := integrated_normSq_sub_collision y hw hφ
  rw [← funext hinv] at hexact
  have H := integrated_frequency_error y hy hT hw hφ hψ (fun v => nearest_error (φ v) hh)
  rw [hexact] at H
  have hbound := div_le_div_of_nonneg_right H (by positivity : 0 ≤ 2*D)
  let Z := ∫ v, w v * (Complex.normSq (occurrenceAmplitude y (ψ v)) - (occurrenceCollision y : ℝ))
  have hratio (x z : ℝ) : |x / D - z / (2*D)| = |2*x-z|/(2*D) := by
    rw [show x / D - z / (2*D) = (2*x-z)/(2*D) by field_simp]
    rw [abs_div, abs_of_pos (show 0 < 2*D by positivity)]
  calc
    _ = |2*positiveTestSum y f - Z|/(2*D) := hratio _ _
    _ ≤ _ := hbound
    _ = _ := by field_simp; ring

private theorem actual_diameter (T : ℝ) (i j : Copies T) : |copyOrdinate T i - copyOrdinate T j| ≤ T := by
  have hi := (mem_cutoff.mp i.1.property).2
  have hj := (mem_cutoff.mp j.1.property).2
  dsimp only [copyOrdinate]
  exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hj.1, hi.2]⟩

/-- Actual occurrence amplitudes at an arbitrary real frequency and its
nearest multiple of a positive mesh. No distinction of ordinates is assumed. -/
theorem actual_rounded_normSq {T : ℝ} (hT : 0 ≤ T) (u : ℝ) {h : ℝ} (hh : 0 < h) :
    |Complex.normSq (occurrenceAmplitude (copyOrdinate T) u) -
        Complex.normSq (occurrenceAmplitude (copyOrdinate T) ((round (u/h) : ℝ) * h))| ≤
      (Ncount 0 T : ℝ) * ((Ncount 0 T - 1 : ℕ) : ℝ) * (T * (h/2)) := by
  simpa only [card_copies] using (normSq_frequency_error (copyOrdinate T) (actual_diameter T)
    u ((round (u/h) : ℝ) * h)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (nearest_error u hh) hT) (by positivity))

/-- The normalized estimate for the actual zeta occurrences, at the physical
unfolding scale log(T)/(2π). The input is the real cosine inversion identity
for the chosen even test and its integrable Fourier weight. -/
theorem actual_rounded_positiveTest {T h : ℝ} (hT : 1 < T) (hh : 0 < h)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ d, f (Real.log T / (2*Real.pi) * d) =
      ∫ v, w v * Real.cos (d * (Real.log T * v))) :
    let D := T * Real.log T / (2*Real.pi)
    |positiveTestSum (copyOrdinate T) (fun d => f (Real.log T / (2*Real.pi) * d)) / D -
      (∫ v, w v * (Complex.normSq (occurrenceAmplitude (copyOrdinate T)
        ((round (Real.log T * v / h) : ℝ) * h)) -
        (occurrenceCollision (copyOrdinate T) : ℝ))) / (2*D)| ≤
      (∫ v, |w v|) * (Ncount 0 T : ℝ) * ((Ncount 0 T - 1 : ℕ) : ℝ) * h*T / (4*D) := by
  have ht := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  simpa only [card_copies, Pi.mul_apply, id_eq] using rounded_positiveTestSum (copyOrdinate T)
    (actual_diameter T) ht.le (show 0 < T * Real.log T / (2*Real.pi) by positivity) hh
    hw (measurable_const.mul measurable_id) hinv

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding

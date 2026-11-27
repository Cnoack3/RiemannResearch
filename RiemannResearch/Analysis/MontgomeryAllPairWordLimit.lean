import RiemannResearch.Analysis.MontgomeryAllPairWordRounding
import RiemannResearch.Analysis.ActualZeroCountNormalization

/-! # Asymptotic transfer of every positive gap to rounded Fourier frequencies

The mesh and the real Fourier variable may both move with height. The actual
Riemann–von Mangoldt normalization makes the all-pair error vanish for a
mesh at most T⁻³. No asymptotic for the squared Fourier word is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory Zeta23

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding
open OrdinateCollisionCertificate ActualZeroOrdinate

/-- The complete strictly positive-gap statistic of an unfolded test. -/
def actualPositiveTest (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  positiveTestSum (copyOrdinate T) (fun d => f (Real.log T / (2*Real.pi) * d)) /
    (T * Real.log T / (2*Real.pi))

/-- Rounded Fourier-square statistic, subtracting every pair with equal
ordinate, including distinct occurrence labels with equal heights. -/
def roundedFourierTest (T h : ℝ) (w : ℝ → ℝ) : ℝ :=
  (∫ v, w v * (Complex.normSq (occurrenceAmplitude (copyOrdinate T)
    ((round (Real.log T * v / h) : ℝ) * h)) -
    (occurrenceCollision (copyOrdinate T) : ℝ))) /
      (2 * (T * Real.log T / (2*Real.pi)))

/-- A T⁻³ mesh has error O(log T / T), uniformly in its choice and summed
over the complete occurrence list. -/
theorem eventually_rounded_positiveTest_le {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1/T^3)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v)) :
    ∀ᶠ T in atTop, |actualPositiveTest T f - roundedFourierTest T (h T) w| ≤
      ((∫ v, |w v|) / (2*Real.pi)) * (Real.log T / T) := by
  have hcount := tendsto_count_div_mainTerm.eventually
    (eventually_lt_nhds (show (1:ℝ) < 2 by norm_num))
  filter_upwards [hh, hcount, eventually_gt_atTop (1:ℝ)] with T hm hc hT
  let D := T * Real.log T / (2*Real.pi)
  let W := ∫ v, |w v|
  have hW : 0 ≤ W := integral_nonneg fun _ => abs_nonneg _
  have ht := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : (Ncount 0 T : ℝ) ≤ 2*D := ((div_lt_iff₀ hD).mp hc).le
  have hp : ((Ncount 0 T - 1 : ℕ) : ℝ) ≤ 2*D := by
    have : ((Ncount 0 T - 1 : ℕ) : ℝ) ≤ (Ncount 0 T : ℝ) := by exact_mod_cast Nat.sub_le _ _
    exact this.trans hN
  have hinv' (d : ℝ) : f (Real.log T/(2*Real.pi)*d) =
      ∫ v, w v * Real.cos (d * (Real.log T * v)) := by
    rw [hinv]
    congr 1
    funext v
    congr 2
    field_simp
  calc
    _ ≤ W * (Ncount 0 T : ℝ) * ((Ncount 0 T - 1 : ℕ) : ℝ) * h T * T / (4*D) :=
      actual_rounded_positiveTest hT hm.1 hw hinv'
    _ ≤ W * (2*D) * (2*D) * (1/T^3) * T / (4*D) := by
      have hmesh := hm.2
      have hmesh₀ := hm.1.le
      gcongr
    _ = _ := by dsimp only [D, W]; field_simp; ring

/-- Every Fourier statistic on such a mesh has the same limiting values as
the complete unfolded test. The arithmetic value of either limit is separate. -/
theorem actualPositiveTest_sub_rounded_tendsto_zero {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1/T^3)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v)) :
    Tendsto (fun T => actualPositiveTest T f - roundedFourierTest T (h T) w) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  apply squeeze_zero_norm'
  · simpa only [Real.norm_eq_abs] using eventually_rounded_positiveTest_le hh hw hinv
  · simpa using hl.const_mul ((∫ v, |w v|)/(2*Real.pi))

theorem actualPositiveTest_tendsto_iff_rounded {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1/T^3)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v)) (c : ℝ) :
    Tendsto (fun T => actualPositiveTest T f) atTop (𝓝 c) ↔
      Tendsto (fun T => roundedFourierTest T (h T) w) atTop (𝓝 c) := by
  have he := actualPositiveTest_sub_rounded_tendsto_zero hh hw hinv
  constructor
  · intro hc
    simpa only [sub_sub_cancel, sub_zero] using hc.sub he
  · intro hc
    simpa only [sub_add_cancel, zero_add] using he.add hc

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding

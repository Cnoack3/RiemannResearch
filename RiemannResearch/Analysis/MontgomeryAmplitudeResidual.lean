import RiemannResearch.Analysis.MontgomeryAllPairWordLimit
import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.Analysis.MontgomeryPhysicalGapTransfer
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Signed Fourier tests from weighted mean-square amplitude approximations

The comparison is made against the actual finite zero-occurrence Fourier
amplitude at the microscopic frequency. The sign of the Fourier test is
retained in the physical energy; its absolute value weights the
Cauchy–Schwarz estimate. An independently predicted collision mass is
allowed, with its entire correction displayed.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology ENNReal BigOperators

namespace RiemannResearch.Analysis.MontgomeryAmplitudeResidual
open MontgomeryAllPairWordRounding MontgomeryPositiveGap ActualZeroOrdinate
open OrdinateCollisionCertificate ActualZeroCollisionCertificate MontgomeryFormFactor

def spectralPower (w : ℝ → ℝ) (A : ℝ → ℂ) : ℝ := ∫ v, w v * ‖A v‖ ^ 2

def weightedAmplitude (w : ℝ → ℝ) (A : ℝ → ℂ) (v : ℝ) : ℝ :=
  Real.sqrt |w v| * ‖A v‖

/-- Actual zero Fourier sum at frequency log(T) v, repeated by analytic multiplicity. -/
def actualAmplitude (T v : ℝ) : ℂ :=
  occurrenceAmplitude (copyOrdinate T) (Real.log T * v)

private lemma weighted_sq (w : ℝ → ℝ) (A : ℝ → ℂ) (x : ℝ) :
    weightedAmplitude w A x ^ 2 = |w x| * ‖A x‖ ^ 2 := by
  rw [weightedAmplitude, mul_pow, Real.sq_sqrt (abs_nonneg _)]

/-- Finite comparison for a signed weight; the cross-term scale is the
geometric mean of the model energy and residual energy. -/
theorem signed_power_residual_bound {w : ℝ → ℝ} {A B : ℝ → ℂ}
    (hA : Integrable (fun v => w v * ‖A v‖ ^ 2))
    (hB : Integrable (fun v => w v * ‖B v‖ ^ 2))
    (hM : MemLp (weightedAmplitude w B) 2 volume)
    (hE : MemLp (weightedAmplitude w (A - B)) 2 volume) :
    |spectralPower w A - spectralPower w B| ≤
      2 * Real.sqrt (spectralPower (fun v => |w v|) B) *
        Real.sqrt (spectralPower (fun v => |w v|) (A - B)) +
        spectralPower (fun v => |w v|) (A - B) := by
  let U := weightedAmplitude w B
  let V := weightedAmplitude w (A - B)
  have hu (v : ℝ) : 0 ≤ U v := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hv (v : ℝ) : 0 ≤ V v := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := U) (g := V) (Eventually.of_forall hu) (Eventually.of_forall hv)
    (show MemLp U (ENNReal.ofReal (2 : ℝ)) volume by simpa using hM)
    (show MemLp V (ENNReal.ofReal (2 : ℝ)) volume by simpa using hE)
  have hcs' : (∫ v, U v * V v) ≤
      Real.sqrt (spectralPower (fun v => |w v|) B) *
      Real.sqrt (spectralPower (fun v => |w v|) (A - B)) := by
    simpa only [U, V, Real.rpow_two, ← Real.sqrt_eq_rpow, weighted_sq, spectralPower] using hcs
  have hUV : Integrable (fun v => U v * V v) :=
    memLp_one_iff_integrable.mp (hE.mul hM)
  have hVV : Integrable (fun v => V v ^ 2) := hE.integrable_sq
  have hdom (v : ℝ) :
      |w v * ‖A v‖ ^ 2 - w v * ‖B v‖ ^ 2| ≤ 2 * (U v * V v) + V v ^ 2 := by
    have hd := abs_norm_sub_norm_le (A v) (B v)
    have ha : ‖A v‖ ≤ ‖A v-B v‖ + ‖B v‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A v-B v) (B v)
    have hp : |‖A v‖ ^ 2 - ‖B v‖ ^ 2| ≤ ‖A v-B v‖ * (2 * ‖B v‖ + ‖A v-B v‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [mul_comm (‖A v‖ + ‖B v‖)]
      exact mul_le_mul hd (by linarith only [ha]) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    have h0 := mul_le_mul_of_nonneg_left hp (abs_nonneg (w v))
    rw [← mul_sub, abs_mul]
    refine h0.trans_eq ?_
    simp only [U,V,weightedAmplitude, Pi.sub_apply]
    conv_lhs => rw [← Real.sq_sqrt (abs_nonneg (w v))]
    ring
  rw [spectralPower, spectralPower, ← integral_sub hA hB]
  calc
    _ ≤ ∫ v, |w v * ‖A v‖ ^ 2 - w v * ‖B v‖ ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun v => w v * ‖A v‖ ^ 2 - w v * ‖B v‖ ^ 2)
    _ ≤ ∫ v, 2*(U v * V v) + V v^2 :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        ((hUV.const_mul 2).add hVV) (Eventually.of_forall hdom)
    _ = 2 * (∫ v, U v*V v) + spectralPower (fun v => |w v|) (A - B) := by
      rw [integral_add (hUV.const_mul 2) hVV, integral_const_mul]
      simp only [V, weighted_sq, spectralPower]
    _ ≤ _ := by linarith only [hcs']

private lemma actual_integrable (T : ℝ) {w : ℝ → ℝ} (hw : Integrable w) :
    Integrable (fun v => w v * ‖actualAmplitude T v‖ ^ 2) := by
  simp only [actualAmplitude, ← Complex.normSq_eq_norm_sq, occurrenceAmplitude_normSq,
    Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply hw.mul_bdd (by fun_prop)
  exact Eventually.of_forall fun v => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.mul_apply] using
      Real.abs_cos_le_one ((copyOrdinate T i - copyOrdinate T j) * (Real.log T * v))

/-- Give the signed model its own predicted ordered collision mass c. -/
def modelTest (T : ℝ) (w : ℝ → ℝ) (B : ℝ → ℂ) (c : ℝ) : ℝ :=
  (spectralPower w B - c * (∫ v, w v)) / (2 * unfoldedCutoff T)

/-- Exact signed compensation of the forward atom for the true strict-gap
statistic. In particular the collision error disappears for f(0)=0. -/
theorem actual_compensated_power_eq {T : ℝ} (hT : 1 < T)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v))
    (B : ℝ → ℂ) (c : ℝ) :
    2 * unfoldedCutoff T * (actualPositiveTest T f - modelTest T w B c) +
      ((actualCollision T : ℝ) - c) * f 0 =
        spectralPower w (actualAmplitude T) - spectralPower w B := by
  have hf0 : f 0 = ∫ v, w v := by
    simpa only [mul_zero, zero_mul, Real.cos_zero, mul_one] using hinv 0
  have hi := integrated_normSq_sub_collision (copyOrdinate T) hw
    (φ := fun v => Real.log T * v) (measurable_const.mul measurable_id)
  have hinv' (d : ℝ) : (∫ v, w v * Real.cos (d * (Real.log T * v))) =
      f (Real.log T / (2 * Real.pi) * d) := by
    rw [hinv]
    congr 1
    funext v
    congr 2
    field_simp
  simp_rw [hinv', mul_sub, Complex.normSq_eq_norm_sq] at hi
  change (∫ v, w v * ‖actualAmplitude T v‖ ^ 2 - w v * (actualCollision T : ℝ)) = _ at hi
  rw [integral_sub (actual_integrable T hw) (hw.mul_const _), integral_mul_const] at hi
  change spectralPower w (actualAmplitude T) - _ = _ at hi
  have hD : 0 < unfoldedCutoff T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  rw [hf0, modelTest]
  change 2*unfoldedCutoff T * (positiveTestSum _ _ / unfoldedCutoff T - _) + _ = _
  rw [show ∀ x y : ℝ, 2 * unfoldedCutoff T * (x / unfoldedCutoff T - y / (2 * unfoldedCutoff T)) =
      2*x-y from fun x y => by field_simp]
  change spectralPower w (actualAmplitude T) - (∫ v, w v) * (actualCollision T : ℝ) = _ at hi
  linarith only [hi]

/-- A weighted mean-square comparison for the actual physical samples.
The signed collision term remains explicit at absolute pair precision. -/
theorem actual_compensated_residual_bound {T : ℝ} (hT : 1 < T)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v))
    (B : ℝ → ℂ) (c : ℝ)
    (hB : Integrable (fun v => w v * ‖B v‖ ^ 2))
    (hM : MemLp (weightedAmplitude w B) 2 volume)
    (hE : MemLp (weightedAmplitude w (actualAmplitude T - B)) 2 volume) :
    |2 * unfoldedCutoff T * (actualPositiveTest T f - modelTest T w B c) +
      ((actualCollision T : ℝ) - c) * f 0| ≤
      2 * Real.sqrt (spectralPower (fun v => |w v|) B) *
        Real.sqrt (spectralPower (fun v => |w v|) (actualAmplitude T - B)) +
        spectralPower (fun v => |w v|) (actualAmplitude T - B) := by
  rw [actual_compensated_power_eq hT hw hinv]
  exact signed_power_residual_bound (actual_integrable T hw) hB hM hE


/-- At the bulk scale D(T), a model with bounded normalized absolute
energy and vanishing normalized residual energy transfers its signed
test value, provided its signed forward-atom error also vanishes.
When f(0)=0 the last hypothesis holds for every collision prediction. -/
theorem actual_sub_model_tendsto_zero {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v))
    (B : ℝ → ℝ → ℂ) (c : ℝ → ℝ) {e : ℝ}
    (hreg : ∀ᶠ T : ℝ in atTop, Integrable (fun v => w v * ‖B T v‖ ^ 2) ∧
      MemLp (weightedAmplitude w (B T)) 2 volume ∧
      MemLp (weightedAmplitude w (actualAmplitude T - B T)) 2 volume)
    (hM : ∀ᶠ T : ℝ in atTop, spectralPower (fun v => |w v|) (B T) / unfoldedCutoff T ≤ e)
    (hE : Tendsto (fun T => spectralPower (fun v => |w v|) (actualAmplitude T - B T) /
      unfoldedCutoff T) atTop (𝓝 0))
    (hC : Tendsto (fun T => ((actualCollision T : ℝ) - c T) * f 0 / unfoldedCutoff T)
      atTop (𝓝 0)) :
    Tendsto (fun T => actualPositiveTest T f - modelTest T w (B T) (c T)) atTop (𝓝 0) := by
  let E (T : ℝ) := spectralPower (fun v => |w v|) (B T)
  let H (T : ℝ) := spectralPower (fun v => |w v|) (actualAmplitude T - B T)
  let L (T : ℝ) := actualPositiveTest T f - modelTest T w (B T) (c T)
  let J (T : ℝ) := ((actualCollision T : ℝ)-c T)*f 0
  have hbound := (hE.sqrt.const_mul (2 * Real.sqrt e)).add hE
  simp only [Real.sqrt_zero, mul_zero, zero_add] at hbound
  have hcomp : Tendsto (fun T => 2*L T + J T / unfoldedCutoff T) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hreg, hM, eventually_gt_atTop (1 : ℝ)] with T hr hME hT
    have hD : 0 < unfoldedCutoff T :=
      div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
    have hm : 0 ≤ E T := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hh : 0 ≤ H T := integral_nonneg fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hx := actual_compensated_residual_bound hT hw hinv (B T) (c T) hr.1 hr.2.1 hr.2.2
    change |2 * unfoldedCutoff T * L T + J T| ≤ 2*√(E T)*√(H T)+ H T at hx
    rw [Real.norm_eq_abs, show 2*L T + J T / unfoldedCutoff T =
      (2*unfoldedCutoff T*L T + J T)/unfoldedCutoff T by field_simp,
      abs_div, abs_of_pos hD]
    refine (div_le_div_of_nonneg_right hx hD.le).trans ?_
    apply le_trans (b := 2 * √(E T / unfoldedCutoff T) * √(H T / unfoldedCutoff T) +
        H T / unfoldedCutoff T) _ (add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hME) (by norm_num : 0 ≤ (2 : ℝ)))
        (Real.sqrt_nonneg _)) le_rfl)
    apply le_of_eq
    change (2*√(E T)*√(H T)+ H T)/unfoldedCutoff T =
      2*√(E T / unfoldedCutoff T)*√(H T / unfoldedCutoff T)+H T/unfoldedCutoff T
    rw [add_div, Real.sqrt_div hm, Real.sqrt_div hh]
    congr 1
    calc
      _ = 2 * √(E T) * √(H T) / (√(unfoldedCutoff T))^2 := by
        rw [Real.sq_sqrt hD.le]
      _ = _ := by field_simp [(Real.sqrt_pos.2 hD).ne']
  have hz := (hcomp.sub hC).div_const 2
  simp only [sub_zero, zero_div] at hz
  apply hz.congr'
  exact Eventually.of_forall fun T => by
    change (2*L T + J T / unfoldedCutoff T - J T / unfoldedCutoff T) / 2 = L T
    ring

/-- Exact diagonal domination for a nonnegative physical test normalized
at zero. The Fourier density may have either sign. -/
theorem collision_le_actual_power {T : ℝ} (hT : 1 < T)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v))
    (h0 : f 0 = 1) (hpos : ∀ x, 0 < x → 0 ≤ f x) :
    (actualCollision T : ℝ) ≤ spectralPower w (actualAmplitude T) := by
  have hD : 0 < unfoldedCutoff T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have ha : 0 < Real.log T / (2*Real.pi) := div_pos (Real.log_pos hT) (by positivity)
  have hpos' : 0 ≤ actualPositiveTest T f := by
    unfold actualPositiveTest positiveTestSum
    apply div_nonneg _ hD.le
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs with hij
    · exact hpos _ (mul_pos ha (sub_pos.mpr hij))
    · exact le_rfl
  have h := actual_compensated_power_eq hT hw hinv (fun _ => 0) 0
  have hz : spectralPower w (fun _ => 0) = 0 := by simp [spectralPower]
  have hz' : modelTest T w (fun _ => 0) 0 = 0 := by simp [modelTest,hz]
  rw [hz', hz, h0, sub_zero, sub_zero, sub_zero, mul_one] at h
  have hn := mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hD.le) hpos'
  linarith only [h, hn]

/-- An upper bound for the complete forward atom in terms of a model
amplitude and the weighted mean-square approximation error. -/
theorem collision_le_model_plus_residual {T : ℝ} (hT : 1 < T)
    {w f : ℝ → ℝ} (hw : Integrable w)
    (hinv : ∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v))
    (h0 : f 0 = 1) (hpos : ∀ x, 0 < x → 0 ≤ f x) (B : ℝ → ℂ)
    (hB : Integrable (fun v => w v * ‖B v‖ ^ 2))
    (hM : MemLp (weightedAmplitude w B) 2 volume)
    (hE : MemLp (weightedAmplitude w (actualAmplitude T - B)) 2 volume) :
    (actualCollision T : ℝ) ≤ spectralPower w B +
      2 * Real.sqrt (spectralPower (fun v => |w v|) B) *
      Real.sqrt (spectralPower (fun v => |w v|) (actualAmplitude T - B)) +
      spectralPower (fun v => |w v|) (actualAmplitude T - B) := by
  have hab := signed_power_residual_bound (actual_integrable T hw) hB hM hE
  have hupper := (abs_le.mp hab).2
  linarith only [collision_le_actual_power hT hw hinv h0 hpos, hupper]

/-- Unit-scale upper approximation at arbitrarily large heights suffices
for RH and analytic simplicity, without requiring the forward atom as input. -/
theorem global_of_cofinal_amplitude_certificates
    (h : ∃ᶠ T : ℝ in atTop, ∃ (w f : ℝ → ℝ) (B : ℝ → ℂ),
      Integrable w ∧ (∀ x, f x = ∫ v, w v * Real.cos (2 * Real.pi * x * v)) ∧
      f 0 = 1 ∧ (∀ x, 0 < x → 0 ≤ f x) ∧
      Integrable (fun v => w v * ‖B v‖ ^ 2) ∧
      MemLp (weightedAmplitude w B) 2 volume ∧
      MemLp (weightedAmplitude w (actualAmplitude T - B)) 2 volume ∧
      spectralPower w B + 2 * Real.sqrt (spectralPower (fun v => |w v|) B) *
        Real.sqrt (spectralPower (fun v => |w v|) (actualAmplitude T - B)) +
        spectralPower (fun v => |w v|) (actualAmplitude T - B) < (Ncount 0 T : ℝ) + 2) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  apply frequently_collision_lt_count_add_two_iff_global.mp
  apply (h.and_eventually (eventually_gt_atTop (1 : ℝ))).mono
  rintro T ⟨⟨w,f,B,hw,hinv,h0,hpos,hB,hM,hE,hsmall⟩,hT⟩
  have hlt := (collision_le_model_plus_residual hT hw hinv h0 hpos B hB hM hE).trans_lt hsmall
  exact_mod_cast hlt

end RiemannResearch.Analysis.MontgomeryAmplitudeResidual

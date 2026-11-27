import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# The projection step in continuous spectral DPP rigidity

The variable `h` is an unfolded frequency. At intensity one the regular
structure factor of a convolution DPP has the autocorrelation formula below.
The arguments in this module concern Lebesgue integrals of its multiplier.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannResearch.DPPSpectral

/-- The regular, intensity-one structure factor with cycles-per-unit Fourier convention. -/
noncomputable def structureFactor (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  1 - ∫ x, f x * f (x + h)

private theorem translate_ae {p : ℝ → Prop} (hp : ∀ᵐ x, p x) (h : ℝ) :
    ∀ᵐ x, p (x + h) :=
  (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hp

private theorem translate_integrable {f : ℝ → ℝ} (hf : Integrable f) (h : ℝ) :
    Integrable (fun x => f (x + h)) :=
  hf.comp_add_right h

private theorem norm_le_one {f : ℝ → ℝ} (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ᵐ x, ‖f x‖ ≤ (1 : ℝ) := by
  filter_upwards [hb] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- The excess over the zero-frequency defect is exactly half the squared
translation distance. In particular the minimum is attained at zero. -/
theorem twice_structureFactor_sub_zero {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (h : ℝ) :
    2 * (structureFactor f h - structureFactor f 0) =
      ∫ x, (f x - f (x + h)) ^ 2 := by
  have hsq := hf.mul_bdd hf.aestronglyMeasurable (norm_le_one hb)
  have htr := translate_integrable hsq h
  have hcross := hf.mul_bdd (translate_integrable hf h).aestronglyMeasurable
    (translate_ae (norm_le_one hb) h)
  have heq : (∫ x, (f x - f (x + h)) ^ 2) =
      (∫ x, f x * f x) + (∫ x, f (x + h) * f (x + h)) -
        2 * (∫ x, f x * f (x + h)) := by
    calc
      _ = ∫ x, (f x * f x + f (x + h) * f (x + h)) - 2 * (f x * f (x + h)) :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by
        have hi : Integrable (fun x => f x * f x + f (x+h) * f (x+h)) := hsq.add htr
        rw [integral_sub hi (hcross.const_mul 2), integral_add hsq htr,
          integral_const_mul]
  rw [heq, integral_add_right_eq_self (fun x => f x * f x) h]
  simp only [structureFactor, add_zero]
  ring

theorem structureFactor_zero_le {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (h : ℝ) : structureFactor f 0 ≤ structureFactor f h := by
  have hp : 0 ≤ ∫ x, (f x - f (x + h)) ^ 2 := integral_nonneg fun x => sq_nonneg _
  linarith [twice_structureFactor_sub_zero hf hb h]

/-- An intensity-one multiplier with vanishing defect is binary almost everywhere. -/
theorem binary_of_structureFactor_zero {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (hmass : (∫ x, f x) = 1)
    (hzero : structureFactor f 0 = 0) : ∀ᵐ x, f x = 0 ∨ f x = 1 := by
  have hsq := hf.mul_bdd hf.aestronglyMeasurable (norm_le_one hb)
  have hn : ∀ᵐ x, 0 ≤ f x - f x * f x := by
    filter_upwards [hb] with x hx
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hz : (∫ x, f x - f x * f x) = 0 := by
    rw [integral_sub hf hsq, hmass]
    simpa [structureFactor] using hzero
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn (hf.sub hsq)).mp hz
  filter_upwards [hae] with x hx
  change f x - f x * f x = 0 at hx
  have hp : f x * (1 - f x) = 0 := by nlinarith only [hx]
  exact (mul_eq_zero.mp hp).imp id (fun h => by linarith)

/-- At intensity one the regular structure factor is everywhere nonnegative. -/
theorem structureFactor_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (hmass : (∫ x, f x) = 1) (h : ℝ) :
    0 ≤ structureFactor f h := by
  apply le_trans _ (structureFactor_zero_le hf hb h)
  have hsq := hf.mul_bdd hf.aestronglyMeasurable (norm_le_one hb)
  have hle : (∫ x, f x * f x) ≤ ∫ x, f x := by
    apply integral_mono_ae hsq hf
    filter_upwards [hb] with x hx
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  simp only [structureFactor, add_zero]
  linarith

/-- A nonnegative convolution multiplier gives a regular structure factor at most one. -/
theorem structureFactor_le_one {f : ℝ → ℝ} (hf : ∀ᵐ t, 0 ≤ f t) (h : ℝ) :
    structureFactor f h ≤ 1 := by
  unfold structureFactor
  apply sub_le_self
  apply integral_nonneg_of_ae
  filter_upwards [hf, translate_ae hf h] with t ht hh
  exact mul_nonneg ht hh

/-- A single sequence of positive steps controls the right lower slope. -/
theorem rightSlope_liminf_le_of_steps {S : ℝ → ℝ} {h : ℕ → ℝ} {c : ℝ}
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    (hu : ∀ᶠ j in atTop, S (h j) ≤ c * h j) :
    liminf (fun x => ENNReal.ofReal (S x / x)) (𝓝[>] 0) ≤ ENNReal.ofReal c := by
  have hright : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hp⟩
  apply liminf_le_of_frequently_le'
  by_contra hn
  obtain ⟨j, hj, hn'⟩ := (hu.and (hright.eventually (not_frequently.mp hn))).exists
  exact hn' (ENNReal.ofReal_le_ofReal ((div_le_iff₀ (hp j)).mpr hj))

/-- A strict right-hand slope threshold supplies an entire favorable sequence.
Using the extended nonnegative reals makes a diverging positive slope have
liminf infinity. For a nonnegative structure factor the truncation in
`ENNReal.ofReal` is immaterial on positive frequencies. -/
theorem exists_small_steps_of_liminf_lt {S : ℝ → ℝ} {B : ℝ}
    (hlim : liminf (fun h => ENNReal.ofReal (S h / h)) (𝓝[>] 0) < ENNReal.ofReal B) :
    ∃ c : ℝ, 0 < c ∧ c < B ∧ ∃ d : ℕ → ℝ,
      (∀ n, 0 < d n) ∧ Tendsto d atTop (𝓝 0) ∧ ∀ n, S (d n) ≤ c * d n := by
  obtain ⟨e, he, heB⟩ := exists_between hlim
  have het : e ≠ ⊤ := (heB.trans (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)).ne
  have hepos : 0 < e.toReal := ENNReal.toReal_pos (bot_le.trans_lt he).ne' het
  have heB' : e.toReal < B := by
    rwa [← ENNReal.ofReal_toReal het, ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      ENNReal.toReal_nonneg] at heB
  have hfreq : ∃ᶠ h in 𝓝[>] (0 : ℝ), S h / h < e.toReal := by
    have H := frequently_lt_of_liminf_lt (f := 𝓝[>] (0 : ℝ))
      (u := fun h => ENNReal.ofReal (S h / h)) (b := e) (h := he)
    exact H.mono fun x hx => (ENNReal.ofReal_lt_ofReal_iff hepos).mp
      ((ENNReal.ofReal_toReal het).symm ▸ hx)
  obtain ⟨d, hmem, hd⟩ := mem_closure_iff_seq_limit.mp
    (mem_closure_iff_frequently.mpr (frequently_nhdsWithin_iff.mp hfreq) :
      (0 : ℝ) ∈ closure {h | S h / h < e.toReal ∧ h ∈ Ioi 0})
  refine ⟨e.toReal, hepos, heB', d, fun n => (hmem n).2, hd, fun n => ?_⟩
  exact ((div_lt_iff₀ (hmem n).2).mp (hmem n).1).le

/-- A single sequence with factors tending to zero forces a measurable
projection spectrum of length one. The frequencies need not include zero. -/
theorem exists_indicator_of_structureFactor_tendsto_zero {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (hmass : (∫ x, f x) = 1)
    {h : ℕ → ℝ} (hh : Tendsto (fun n => structureFactor f (h n)) atTop (𝓝 0)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 1 ∧ f =ᵐ[volume] E.indicator 1 := by
  have hle : structureFactor f 0 ≤ 0 :=
    ge_of_tendsto hh (Eventually.of_forall fun n => structureFactor_zero_le hf hb (h n))
  have hzero := le_antisymm hle (structureFactor_nonneg hf hb hmass 0)
  have hbinary := binary_of_structureFactor_zero hf hb hmass hzero
  let g := hf.aemeasurable.mk f
  let E : Set ℝ := g ⁻¹' {1}
  have hE : MeasurableSet E := (measurableSet_singleton _).preimage hf.aemeasurable.measurable_mk
  have heq : f =ᵐ[volume] E.indicator 1 := by
    filter_upwards [hf.aemeasurable.ae_eq_mk, hbinary] with x hx hx01
    change f x = g x at hx
    rcases hx01 with h0 | h1
    · have hout : x ∉ E := by
        change g x ≠ 1
        rw [← hx, h0]
        norm_num
      simp [hout, h0]
    · have hin : x ∈ E := by
        change g x = 1
        rw [← hx, h1]
      simp [hin, h1]
  refine ⟨E, hE, (ENNReal.toReal_eq_one_iff _).mp ?_, heq⟩
  calc
    (volume E).toReal = ∫ x, E.indicator (1 : ℝ → ℝ) x := (integral_indicator_one hE).symm
    _ = ∫ x, f x := integral_congr_ae heq.symm
    _ = 1 := hmass

/-- The slope criterion gives a measurable projection spectrum and positive
steps witnessing the same strict threshold. -/
theorem projection_and_steps_of_liminf_lt {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1) (hmass : (∫ x, f x) = 1) {B : ℝ}
    (hlim : liminf (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) <
      ENNReal.ofReal B) :
    ∃ (E : Set ℝ) (c : ℝ) (d : ℕ → ℝ), MeasurableSet E ∧ volume E = 1 ∧
      f =ᵐ[volume] E.indicator 1 ∧ 0 < c ∧ c < B ∧
      (∀ n, 0 < d n) ∧ Tendsto d atTop (𝓝 0) ∧
      ∀ n, structureFactor f (d n) ≤ c * d n := by
  obtain ⟨c, hc, hcB, d, hdpos, hd, hstep⟩ := exists_small_steps_of_liminf_lt hlim
  have hs : Tendsto (fun n => structureFactor f (d n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (tendsto_const_nhds (x := c)).mul hd)
      (fun n => structureFactor_nonneg hf hb hmass (d n)) hstep
  obtain ⟨E, hE, hvol, heq⟩ := exists_indicator_of_structureFactor_tendsto_zero hf hb hmass hs
  exact ⟨E, c, d, hE, hvol, heq, hc, hcB, hdpos, hd, hstep⟩

private theorem binary_bounds {f : ℝ → ℝ} (hb : ∀ᵐ x, f x = 0 ∨ f x = 1) :
    ∀ᵐ x, 0 ≤ f x ∧ f x ≤ 1 := by
  filter_upwards [hb] with x hx
  rcases hx with h | h <;> simp [h]

/-- Twice the projection structure factor equals the translation difference in L¹. -/
theorem twice_structureFactor_eq_integral_abs {f : ℝ → ℝ} (hf : Integrable f)
    (hmass : (∫ x, f x) = 1) (hb : ∀ᵐ x, f x = 0 ∨ f x = 1) (h : ℝ) :
    2 * structureFactor f h = ∫ x, |f x - f (x + h)| := by
  have hzero : structureFactor f 0 = 0 := by
    have heq : (∫ x, f x * f x) = ∫ x, f x := by
      apply integral_congr_ae
      filter_upwards [hb] with x hx
      rcases hx with h | h <;> simp [h]
    simp [structureFactor, heq, hmass]
  rw [← sub_zero (structureFactor f h), ← hzero,
    twice_structureFactor_sub_zero hf (binary_bounds hb) h]
  apply integral_congr_ae
  filter_upwards [hb, translate_ae hb h] with x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> norm_num [hx, hy]

/-- Evenness follows by translating the autocorrelation integrand. -/
theorem structureFactor_even (f : ℝ → ℝ) (h : ℝ) :
    structureFactor f (-h) = structureFactor f h := by
  unfold structureFactor
  rw [← integral_add_right_eq_self (fun x => f x * f (x + -h)) h]
  simp only [add_neg_cancel_right, mul_comm]

/-- The projection structure factor is subadditive by the L¹ triangle inequality. -/
theorem structureFactor_subadditive {f : ℝ → ℝ} (hf : Integrable f)
    (hmass : (∫ x, f x) = 1) (hb : ∀ᵐ x, f x = 0 ∨ f x = 1) (h k : ℝ) :
    structureFactor f (h + k) ≤ structureFactor f h + structureFactor f k := by
  let d (a x : ℝ) := |f x - f (x + a)|
  have hd (a : ℝ) : Integrable (d a) := (hf.sub (translate_integrable hf a)).abs
  have hle : (∫ x, d (h + k) x) ≤ (∫ x, d h x) + ∫ x, d k x := by
    rw [← integral_add_right_eq_self (d k) h,
      ← integral_add (hd h) (translate_integrable (hd k) h)]
    apply integral_mono (hd _) ((hd h).add (translate_integrable (hd k) h))
    intro x
    simpa [d, ← add_assoc] using abs_sub_le (f x) (f (x+h)) (f ((x+h)+k))
  change (∫ x, |f x - f (x + (h+k))|) ≤
    (∫ x, |f x - f (x+h)|) + (∫ x, |f x - f (x+k)|) at hle
  linarith [twice_structureFactor_eq_integral_abs hf hmass hb h,
    twice_structureFactor_eq_integral_abs hf hmass hb k,
    twice_structureFactor_eq_integral_abs hf hmass hb (h+k)]

end RiemannResearch.DPPSpectral

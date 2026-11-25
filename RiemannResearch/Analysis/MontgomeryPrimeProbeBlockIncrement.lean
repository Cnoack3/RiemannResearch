import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! A finite-interval estimate for increments of a centered monotone distribution. -/

noncomputable section

open MeasureTheory Set

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace

/-- For a monotone distribution, the integrated mass of sliding windows of width
`h` is bounded by `h` times the mass of the enlarged interval. -/
theorem monotone_integral_window_le {f : ℝ → ℝ} (hf : Monotone f)
    {a b h : ℝ} (hh : 0 ≤ h) :
    (∫ x in a..b, (f (x + h) - f x)) ≤ h * (f (b + h) - f a) := by
  have hs : Monotone (fun x : ℝ => f (x + h)) :=
    fun _ _ huv => hf (add_le_add huv le_rfl)
  have hupper := intervalIntegral.integral_mono_on (μ := volume)
    (f := f) (g := fun _ => f (b + h)) (a := b) (b := b + h)
    (by linarith) hf.intervalIntegrable intervalIntegrable_const
    (fun x hx => hf hx.2)
  have hlower := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ => f a) (g := f) (a := a) (b := a + h)
    (by linarith) intervalIntegrable_const hf.intervalIntegrable
    (fun x hx => hf hx.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hupper hlower
  rw [intervalIntegral.integral_sub hs.intervalIntegrable hf.intervalIntegrable,
    intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_interval_sub_interval_comm'
      (hf.intervalIntegrable (a := a+h) (b := b+h))
      (hf.intervalIntegrable (a := a) (b := b))
      (hf.intervalIntegrable (a := a+h) (b := a))]
  linarith only [hupper, hlower]

/-- The squared translation error on a block costs its remainder envelope
times the variation on the enlarged block and the translation length. -/
theorem centered_monotone_block_increment_sq_le {f : ℝ → ℝ} (hf : Monotone f)
    {a b h C B : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (henv : ∀ y ∈ Icc a (b + h), |f y - y - C| ≤ B) :
    (∫ x in a..b, (f (x+h) - f x - h)^2) ≤
      2 * B * h * (f (b+h) - f a + (b-a)) := by
  let d (x : ℝ) := f (x+h) - f x - h
  let g (x : ℝ) := f (x+h) - f x + h
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : (d x)^2 ≤ 2*B*g x := by
    have hleft := abs_le.mp (henv x ⟨hx.1, by linarith [hx.2]⟩)
    have hright := abs_le.mp (henv (x+h)
      ⟨by linarith [hx.1], add_le_add hx.2 le_rfl⟩)
    have hdim : |d x| ≤ 2*B := by
      apply abs_le.mpr
      dsimp [d]
      constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]
    have hmass := hf (show x ≤ x+h by linarith)
    have hvar : |d x| ≤ g x := by
      apply abs_le.mpr
      dsimp [d, g]
      constructor <;> linarith
    simpa only [← sq, sq_abs] using
      (mul_le_mul hdim hvar (abs_nonneg _) (by positivity : 0 ≤ 2*B))
  have hs : Monotone (fun x : ℝ => f (x + h)) :=
    fun _ _ huv => hf (add_le_add huv le_rfl)
  have hi : IntervalIntegrable g volume a b :=
    (hs.intervalIntegrable.sub hf.intervalIntegrable).add intervalIntegrable_const
  have hm : Measurable (fun x : ℝ => (d x)^2) :=
    (((hs.measurable.sub hf.measurable).sub measurable_const).pow_const 2)
  have hsq : IntervalIntegrable (fun x : ℝ => (d x)^2) volume a b := by
    apply (hi.const_mul (2*B)).mono_fun' hm.aestronglyMeasurable
    rw [Set.uIoc_of_le hab]
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc a b) measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (d x))] using
      hpoint x ⟨hx.1.le, hx.2⟩
  have hbound := intervalIntegral.integral_mono_on hab hsq (hi.const_mul (2*B)) hpoint
  rw [intervalIntegral.integral_const_mul] at hbound
  change (∫ x in a..b, (d x)^2) ≤ 2*B*h * (f (b+h) - f a + (b-a))
  calc
    _ ≤ 2*B * (∫ x in a..b, g x) := hbound
    _ ≤ 2*B * (h * (f (b+h) - f a) + (b-a)*h) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [g]
      rw [intervalIntegral.integral_add (hs.intervalIntegrable.sub hf.intervalIntegrable)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      exact add_le_add (monotone_integral_window_le hf hh) le_rfl
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryPrimeTrace

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite counting-window moments

Occurrence labels retain repeated ordinates. Endpoints use `Ioc`; this changes
the usual forward counting convention only on a finite, measure-zero set.
The overlap formula is clipped exactly at both ends. The un-clipped triangle
identity is specialized only under the displayed support assumptions.

Source: elementary interval-overlap argument developed in the user's
ordinate-pair-correlation program, 2026-10-11. No RH premise is used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace RiemannResearch.Analysis.OrdinateWindowVariance

def pulse (a b : ℝ) (t : ℝ) : ℝ := (Ioc a b).indicator (fun _ => 1) t

lemma pulse_integrable (a b : ℝ) : Integrable (pulse a b) := by
  apply (integrable_indicator_iff measurableSet_Ioc).2
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma integral_pulse (a b : ℝ) :
    (∫ t : ℝ, pulse a b t) = max (b - a) 0 := by
  simp only [pulse, integral_indicator_const (1 : ℝ) measurableSet_Ioc,
    Real.volume_real_Ioc, smul_eq_mul, mul_one]

lemma pulse_mul (a b c d t : ℝ) :
    pulse a b t * pulse c d t = pulse (max a c) (min b d) t := by
  have hs : Ioc a b ∩ Ioc c d = Ioc (max a c) (min b d) := Ioc_inter_Ioc
  unfold pulse
  rw [← hs]
  simp only [Set.indicator, mem_inter_iff]
  split_ifs <;> simp_all

def windowPulse (T h x : ℝ) : ℝ → ℝ :=
  pulse (max 0 (x - h)) (min T x)

def windowCount {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h t : ℝ) : ℝ :=
  ∑ i ∈ s, windowPulse T h (x i) t

lemma windowPulse_integrable (T h x : ℝ) : Integrable (windowPulse T h x) :=
  pulse_integrable _ _

lemma windowPulse_mul_integrable (T h x y : ℝ) :
    Integrable (fun t => windowPulse T h x t * windowPulse T h y t) := by
  simp_rw [windowPulse, pulse_mul]
  exact pulse_integrable _ _

lemma windowCount_integrable {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h : ℝ) :
    Integrable (windowCount s x T h) := by
  exact integrable_finsetSum s fun i _ => windowPulse_integrable T h (x i)

lemma windowCount_sq_expansion {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h t : ℝ) :
    windowCount s x T h t ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, windowPulse T h (x i) t * windowPulse T h (x j) t := by
  simp only [windowCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma windowCount_sq_integrable {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h : ℝ) :
    Integrable (fun t => windowCount s x T h t ^ 2) := by
  simp_rw [windowCount_sq_expansion]
  exact integrable_finsetSum s fun i _ =>
    integrable_finsetSum s fun j _ => windowPulse_mul_integrable T h (x i) (x j)

theorem integral_windowCount {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h : ℝ) :
    (∫ t : ℝ, windowCount s x T h t) =
      ∑ i ∈ s, max (min T (x i) - max 0 (x i - h)) 0 := by
  unfold windowCount
  rw [integral_finsetSum s (fun i _ => windowPulse_integrable T h (x i))]
  simp only [windowPulse, integral_pulse]

/-- Exact moment formula with both boundary clips retained. -/
theorem integral_windowCount_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h : ℝ) :
    (∫ t : ℝ, windowCount s x T h t ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s,
        max (min (min T (x i)) (min T (x j)) -
          max (max 0 (x i - h)) (max 0 (x j - h))) 0 := by
  simp_rw [windowCount_sq_expansion]
  rw [integral_finsetSum s (fun i _ =>
    integrable_finsetSum s (fun j _ => windowPulse_mul_integrable T h (x i) (x j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j _ => windowPulse_mul_integrable T h (x i) (x j))]
  simp_rw [windowPulse, pulse_mul, integral_pulse]

lemma overlap_triangle (h x y : ℝ) :
    min x y - max (x - h) (y - h) = h - |x - y| := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, max_eq_right (by linarith), abs_of_nonpos (by linarith)]
    ring
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx, max_eq_left (by linarith), abs_of_nonneg (by linarith)]
    ring

theorem integral_windowCount_of_supported {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T h : ℝ) (hh : 0 ≤ h) (hx : ∀ i ∈ s, h ≤ x i ∧ x i ≤ T) :
    (∫ t : ℝ, windowCount s x T h t) = (s.card : ℝ) * h := by
  rw [integral_windowCount]
  calc
    _ = ∑ i ∈ s, h := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [min_eq_right (hx i hi).2, max_eq_right (sub_nonneg.mpr (hx i hi).1)]
      have he : x i - (x i - h) = h := by ring
      rw [he, max_eq_left hh]
    _ = _ := by simp

theorem integral_windowCount_sq_of_supported {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T h : ℝ) (hx : ∀ i ∈ s, h ≤ x i ∧ x i ≤ T) :
    (∫ t : ℝ, windowCount s x T h t ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, max (h - |x i - x j|) 0 := by
  rw [integral_windowCount_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [min_eq_right (hx i hi).2, min_eq_right (hx j hj).2,
    max_eq_right (sub_nonneg.mpr (hx i hi).1),
    max_eq_right (sub_nonneg.mpr (hx j hj).1), overlap_triangle]

lemma windowPulse_mul_support (T h x t : ℝ) :
    windowPulse T h x t * pulse 0 T t = windowPulse T h x t := by
  simp only [windowPulse, pulse_mul]
  congr 1 <;> simp [max_comm]

lemma windowCount_mul_support {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h t : ℝ) :
    windowCount s x T h t * pulse 0 T t = windowCount s x T h t := by
  simp only [windowCount, Finset.sum_mul, windowPulse_mul_support]

def centeredCount {ι : Type*} (s : Finset ι) (x : ι → ℝ) (T h lam t : ℝ) : ℝ :=
  windowCount s x T h t - lam * pulse 0 T t

lemma centeredCount_sq_expansion {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T h lam t : ℝ) :
    centeredCount s x T h lam t ^ 2 =
      windowCount s x T h t ^ 2 - (2 * lam) * windowCount s x T h t +
        lam ^ 2 * pulse 0 T t := by
  unfold centeredCount
  calc
    _ = windowCount s x T h t ^ 2 -
        (2 * lam) * (windowCount s x T h t * pulse 0 T t) +
        lam ^ 2 * (pulse 0 T t * pulse 0 T t) := by ring
    _ = _ := by rw [windowCount_mul_support, pulse_mul]; simp only [max_self, min_self]

theorem integral_centeredCount_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T h lam : ℝ) :
    (∫ t : ℝ, centeredCount s x T h lam t ^ 2) =
      (∫ t : ℝ, windowCount s x T h t ^ 2) -
        (2 * lam) * (∫ t : ℝ, windowCount s x T h t) + lam ^ 2 * max T 0 := by
  have hc := windowCount_integrable s x T h
  have hc2 := windowCount_sq_integrable s x T h
  have hp := pulse_integrable 0 T
  simp_rw [centeredCount_sq_expansion]
  have hsub : Integrable (fun t : ℝ =>
      windowCount s x T h t ^ 2 - (2 * lam) * windowCount s x T h t) :=
    hc2.sub (hc.const_mul (2 * lam))
  rw [integral_add hsub (hp.const_mul (lam ^ 2)),
    integral_sub hc2 (hc.const_mul (2 * lam)), integral_const_mul,
    integral_const_mul, integral_pulse, sub_zero]

/-- Exact physical triangle energy equals squared mean plus count variance.
The displayed support and mean hypotheses remove all boundary correction terms. -/
theorem triangle_eq_mean_sq_add_variance {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T h lam : ℝ) (hT : 0 < T) (hh : 0 ≤ h)
    (hx : ∀ i ∈ s, h ≤ x i ∧ x i ≤ T)
    (hmean : (s.card : ℝ) * h = T * lam) :
    (∑ i ∈ s, ∑ j ∈ s, max (h - |x i - x j|) 0) / T =
      lam ^ 2 + (∫ t : ℝ, centeredCount s x T h lam t ^ 2) / T := by
  rw [integral_centeredCount_sq, integral_windowCount_sq_of_supported s x T h hx,
    integral_windowCount_of_supported s x T h hh hx, hmean, max_eq_left hT.le]
  field_simp [ne_of_gt hT]
  ring

end RiemannResearch.Analysis.OrdinateWindowVariance

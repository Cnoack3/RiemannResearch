/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryFejerDensity
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-sided weak Montgomery prediction

The Fejér diagonal bound supplies the large tent's lower bound. Subtracting
this bound from the one-sided predictions for two nonnegative complementary
tests yields the full weak raw Fourier limit.

The tent and Fourier target use Montgomery (1973),
https://websites.umich.edu/~hlm/paircor1.pdf. The two-test argument uses only
the exact tent calculation and the actual-zero count and collision imports.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate

/-- The upper half of the weak raw Fourier prediction for nonnegative
continuous interval tests. -/
def RawFormFactorTestUpper : Prop :=
  ∀ R : ℝ, 0 < R → ∀ f : ℝ → ℝ, Continuous f → f (-R) = 0 → f R = 0 →
    (∀ x ∈ Icc (-R) R, 0 ≤ f x) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ T : ℝ in atTop,
      (∫ x in (-R)..R, f x * formFactor T x) <
        f 0 + (∫ x in (-R)..R, f x * min |x| 1) + ε

private def clampedTest (r : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (max (-r) (min r x))

private theorem continuous_clampedTest (r : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (clampedTest r f) := by
  unfold clampedTest
  exact hf.comp (continuous_const.max (continuous_const.min continuous_id))

private theorem clampedTest_eq {r x : ℝ} {f : ℝ → ℝ} (hx : x ∈ Icc (-r) r) :
    clampedTest r f x = f x := by
  unfold clampedTest
  rw [min_eq_right hx.2, max_eq_right hx.1]

private theorem clampedTest_left {r x : ℝ} {f : ℝ → ℝ} (hr : 0 ≤ r) (hx : x ≤ -r)
    (hf : f (-r) = 0) : clampedTest r f x = 0 := by
  unfold clampedTest
  have hrr : -r ≤ r := by linarith
  rw [min_eq_right (hx.trans hrr), max_eq_left hx, hf]

private theorem clampedTest_right {r x : ℝ} {f : ℝ → ℝ} (hr : 0 ≤ r) (hx : r ≤ x)
    (hf : f r = 0) : clampedTest r f x = 0 := by
  unfold clampedTest
  have hrr : -r ≤ r := by linarith
  rw [min_eq_left hx, max_eq_right hrr, hf]

private theorem integral_clampedTest_mul {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hleft : f (-r) = 0) (hright : f r = 0) :
    (∫ x in (-R)..R, clampedTest r f x * g x) = ∫ x in (-r)..r, f x * g x := by
  have hc : Continuous (fun x => clampedTest r f x * g x) :=
    (continuous_clampedTest r hf).mul hg
  have hleftIntegral : (∫ x in (-R)..(-r), clampedTest r f x * g x) = 0 := by
    calc
      _ = ∫ _ in (-R)..(-r), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (neg_le_neg hrR)] at hx
        change clampedTest r f x * g x = 0
        rw [clampedTest_left hr hx.2 hleft, zero_mul]
      _ = _ := by simp
  have hrightIntegral : (∫ x in r..R, clampedTest r f x * g x) = 0 := by
    calc
      _ = ∫ _ in r..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hrR] at hx
        change clampedTest r f x * g x = 0
        rw [clampedTest_right hr hx.1 hright, zero_mul]
      _ = _ := by simp
  have hsumLeft := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-R) (-r)) (hc.intervalIntegrable (-r) r)
  have hsumRight := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-R) r) (hc.intervalIntegrable r R)
  calc
    _ = ∫ x in (-r)..r, clampedTest r f x * g x := by
      linarith only [hsumLeft, hsumRight, hleftIntegral, hrightIntegral]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (show -r ≤ r by linarith)] at hx
      change clampedTest r f x * g x = f x * g x
      rw [clampedTest_eq hx]

private theorem integral_add_scale_test (R c : ℝ) {k f g : ℝ → ℝ}
    (hk : Continuous k) (hf : Continuous f) (hg : Continuous g) :
    (∫ x in (-R)..R, (k x + c * f x) * g x) =
      (∫ x in (-R)..R, k x * g x) + c * (∫ x in (-R)..R, f x * g x) := by
  simp_rw [add_mul, mul_assoc]
  have hkg : IntervalIntegrable (fun x => k x * g x) volume (-R) R :=
    (hk.mul hg).intervalIntegrable (-R) R
  have hcfg : IntervalIntegrable (fun x => c * (f x * g x)) volume (-R) R :=
    (continuous_const.mul (hf.mul hg)).intervalIntegrable (-R) R
  rw [intervalIntegral.integral_add hkg hcfg, intervalIntegral.integral_const_mul]

private theorem tent_lower_of_count {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      R - δ < ∫ x in (-R)..R, (1 - |x| / R) * formFactor T x := by
  have hcount := tendsto_count_div_mainTerm.eventually
    (lt_mem_nhds (sub_lt_self (1 : ℝ) (div_pos hδ hR)))
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with T hTcount hT
  have hle : Ncount 0 T ≤ actualCollision T := by
    rw [actualCollision_eq_count_add_excess]
    exact Nat.le_add_right _ _
  have hD : 0 ≤ T * Real.log T / (2 * Real.pi) :=
    div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)
  calc
    _ = R * (1 - δ / R) := by field_simp [hR.ne']
    _ < R * ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) :=
      mul_lt_mul_of_pos_left hTcount hR
    _ ≤ R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by exact_mod_cast hle) hD) hR.le
    _ ≤ R * fejerFormFactor T R :=
      mul_le_mul_of_nonneg_left (collision_div_main_le_fejerFormFactor hT hR) hR.le
    _ = _ := by unfold fejerFormFactor; field_simp [hR.ne']

/-- An upper bound for all nonnegative tests already forces the full weak
Montgomery prediction for actual ordinates. -/
theorem rawFormFactorTestLimit_of_upper (h : RawFormFactorTestUpper) :
    RawFormFactorTestLimit := by
  intro r hr f hf hleft hright
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-r) r)).exists_bound_of_continuousOn
    hf.continuousOn
  have h0r : (0 : ℝ) ∈ Icc (-r) r := by constructor <;> linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 h0r)
  let a := 1 / (2 * (B + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have haB : a * B ≤ 1 / 2 := by
    calc
      _ = B / (2 * (B + 1)) := by dsimp [a]; ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)
  let δ := a * ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδa : 4 * δ = a * ε := by dsimp [δ]; ring
  let R := max 1 (max (2 * r) (1 / δ))
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have h2r : 2 * r ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hrR : r ≤ R := by linarith
  have hδR : 1 / δ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hmodelError : 1 / (3 * R) ≤ δ := by
    have hh := (div_le_iff₀ hδ).mp hδR
    exact (div_le_iff₀ (by positivity)).mpr
      (by nlinarith only [hh, mul_nonneg hR0.le hδ.le])
  let k : ℝ → ℝ := fun x => 1 - |x| / R
  let F := clampedTest r f
  let m : ℝ → ℝ := fun x => min |x| 1
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hF : Continuous F := continuous_clampedTest r hf
  have hm : Continuous m := by dsimp [m]; fun_prop
  have hF0 : F 0 = f 0 := clampedTest_eq h0r
  have hFleft : F (-R) = 0 := clampedTest_left hr.le (neg_le_neg hrR) hleft
  have hFright : F R = 0 := clampedTest_right hr.le hrR hright
  have hkleft : k (-R) = 0 := by simp [k, abs_of_pos hR0, hR0.ne']
  have hkright : k R = 0 := by simp [k, abs_of_pos hR0, hR0.ne']
  have hmodel : k 0 + (∫ x in (-R)..R, k x * m x) = R + 1 / (3 * R) := by
    have hscaled : (1 / R) * (k 0 + (∫ x in (-R)..R, k x * m x)) =
        1 + 1 / (3 * R ^ 2) := by
      simpa only [k, m, abs_zero, zero_div, sub_zero] using fejer_model_value hR
    calc
      _ = R * ((1 / R) * (k 0 + (∫ x in (-R)..R, k x * m x))) := by
        field_simp [hR0.ne']
      _ = R * (1 + 1 / (3 * R ^ 2)) := by rw [hscaled]
      _ = _ := by field_simp [hR0.ne']
  have hnonneg (c : ℝ) (hc : |c| ≤ a) (x : ℝ) (hx : x ∈ Icc (-R) R) :
      0 ≤ k x + c * F x := by
    have hkx : 0 ≤ k x := by
      dsimp [k]
      exact sub_nonneg.mpr ((div_le_iff₀ hR0).mpr (by
        simpa only [one_mul] using abs_le.mpr hx))
    by_cases hxleft : -r ≤ x
    · by_cases hxright : x ≤ r
      · have hxinner : x ∈ Icc (-r) r := ⟨hxleft, hxright⟩
        have hkhalf : 1 / 2 ≤ k x := by
          have hxdiv : |x| / R ≤ 1 / 2 := (div_le_iff₀ hR0).mpr
            (by linarith only [abs_le.mpr hxinner, h2r])
          dsimp [k]
          linarith only [hxdiv]
        have hFx : |F x| ≤ B := by
          rw [show F x = f x from clampedTest_eq hxinner]
          simpa only [Real.norm_eq_abs] using hB x hxinner
        have hprod : |c * F x| ≤ 1 / 2 := by
          rw [abs_mul]
          exact (mul_le_mul hc hFx (abs_nonneg _) ha.le).trans haB
        linarith only [hkhalf, (abs_le.mp hprod).1]
      · rw [show F x = 0 from clampedTest_right hr.le (lt_of_not_ge hxright).le hright]
        simpa only [mul_zero, add_zero] using hkx
    · rw [show F x = 0 from clampedTest_left hr.le (lt_of_not_ge hxleft).le hleft]
      simpa only [mul_zero, add_zero] using hkx
  have ht (c : ℝ) (hc : |c| ≤ a) : ∀ᶠ T : ℝ in atTop,
      c * ((∫ x in (-r)..r, f x * formFactor T x) -
        (f 0 + ∫ x in (-r)..r, f x * m x)) < a * ε := by
    have htest := h R hR0 (fun x => k x + c * F x)
      (hk.add (continuous_const.mul hF))
      (by simp only [hkleft, hFleft, mul_zero, add_zero])
      (by simp only [hkright, hFright, mul_zero, add_zero])
      (hnonneg c hc) δ hδ
    filter_upwards [htest, tent_lower_of_count hR0 hδ] with T htestT hbase
    have hff := MontgomeryGaussianSmoothing.continuous_formFactor T
    change (∫ x in (-R)..R, (k x + c * F x) * formFactor T x) <
      k 0 + c * F 0 + (∫ x in (-R)..R, (k x + c * F x) * m x) + δ at htestT
    rw [integral_add_scale_test R c hk hF hff,
      integral_add_scale_test R c hk hF hm,
      show (∫ x in (-R)..R, F x * formFactor T x) =
        ∫ x in (-r)..r, f x * formFactor T x from
          integral_clampedTest_mul hr.le hrR hf hff hleft hright,
      show (∫ x in (-R)..R, F x * m x) =
        ∫ x in (-r)..r, f x * m x from integral_clampedTest_mul hr.le hrR hf hm hleft hright,
      hF0] at htestT
    change R - δ < (∫ x in (-R)..R, k x * formFactor T x) at hbase
    linarith only [htestT, hbase, hmodel, hmodelError, hδa, hδ]
  filter_upwards [ht a (by simp [abs_of_pos ha]), ht (-a) (by simp [abs_of_pos ha])]
    with T hplus hminus
  change dist (∫ x in (-r)..r, f x * formFactor T x)
    (f 0 + ∫ x in (-r)..r, f x * m x) < ε
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · apply (mul_lt_mul_iff_right₀ ha).mp
    linarith only [hminus]
  · exact (mul_lt_mul_iff_right₀ ha).mp hplus

theorem rawFormFactorTestUpper_iff_limit :
    RawFormFactorTestUpper ↔ RawFormFactorTestLimit := by
  refine ⟨rawFormFactorTestLimit_of_upper, ?_⟩
  intro h R hR f hf hleft hright _ ε hε
  exact (h R hR f hf hleft hright).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))

end RiemannResearch.Analysis.MontgomeryFormFactor

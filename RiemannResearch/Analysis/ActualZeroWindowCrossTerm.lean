/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Mu
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import RiemannResearch.RH.WeilExplicitFormula.RvM.GammaSide

/-!
# The signed gamma–argument cross term in a zero-count window

Translation transfers the difference of the count discrepancy to the smooth
weight. The two endpoint integrals have length equal to the window width.
For a monotone weight its interior variation also telescopes to two endpoint
integrals. Compare the count/argument moment comparison in Goldston, Lee,
Schettler and Suriajaya, Proposition 2 (https://doi.org/10.1112/mtk.70127).
-/

open Filter MeasureTheory Set

namespace RiemannResearch.Analysis

/-- Finite translation identity. The end strips retain their signs. -/
theorem integral_increment_mul_eq_boundary (D g : ℝ → ℝ) (T h : ℝ)
    (hD : ∀ a b, IntervalIntegrable D volume a b) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..T, (D (t + h) - D t) * g t) =
      (∫ t in T..T + h, D t * g (t - h)) -
      (∫ t in (0 : ℝ)..h, D t * g t) -
      (∫ t in h..T, D t * (g t - g (t - h))) := by
  have hc : Continuous (fun t : ℝ => g (t - h)) := hg.comp (continuous_id.sub continuous_const)
  have hp (a b : ℝ) := (hD a b).mul_continuousOn hg.continuousOn
  have hq (a b : ℝ) := (hD a b).mul_continuousOn hc.continuousOn
  have hd : IntervalIntegrable (fun t => D (t + h)) volume 0 T := by
    simpa using (hD h (T + h)).comp_add_right h
  have hshift : (∫ t in (0 : ℝ)..T, D (t + h) * g t) =
      ∫ t in h..T + h, D t * g (t - h) := by
    simpa using intervalIntegral.integral_comp_add_right
      (a := 0) (b := T) (fun t => D t * g (t - h)) h
  simp_rw [sub_mul, mul_sub]
  rw [intervalIntegral.integral_sub (hd.mul_continuousOn hg.continuousOn) (hp 0 T), hshift,
    intervalIntegral.integral_sub (hp h T) (hq h T),
    ← intervalIntegral.integral_add_adjacent_intervals (hq h T) (hq T (T + h)),
    ← intervalIntegral.integral_add_adjacent_intervals (hp 0 h) (hp h T)]
  ring

/-- Cancellation for a bounded discrepancy tested against a continuous
weight monotone on the observation interval. -/
theorem abs_integral_increment_mul_le (D g : ℝ → ℝ) {T h M B : ℝ}
    (hh : 0 ≤ h) (hhT : h ≤ T)
    (hD : ∀ a b, IntervalIntegrable D volume a b) (hg : Continuous g)
    (hmono : MonotoneOn g (Icc 0 T))
    (hM : ∀ t ∈ Icc 0 (T + h), |D t| ≤ M) (hB : ∀ t ∈ Icc 0 T, |g t| ≤ B) :
    |∫ t in (0 : ℝ)..T, (D (t + h) - D t) * g t| ≤ 4 * h * M * B := by
  have hT := hh.trans hhT
  have hm := (abs_nonneg (D 0)).trans (hM 0 ⟨le_rfl, by linarith⟩)
  have hb := (abs_nonneg (g 0)).trans (hB 0 ⟨le_rfl, hT⟩)
  have strip {a b C : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
      (hf : ∀ t ∈ Ioc a b, |f t| ≤ C) : |∫ t in a..b, f t| ≤ C * (b - a) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := f)
        (C := C) (fun t ht => by
          rw [uIoc_of_le hab] at ht
          simpa [Real.norm_eq_abs] using hf t ht)
  have prod {x y : ℝ} (hx : x ∈ Icc 0 (T + h)) (hy : y ∈ Icc 0 T) :
      |D x * g y| ≤ M * B := by
    rw [abs_mul]
    exact mul_le_mul (hM _ hx) (hB _ hy) (abs_nonneg _) hm
  have hs := strip (show T ≤ T + h by linarith) (fun t => D t * g (t - h)) (C := M * B)
    (fun t ht => prod ⟨hT.trans ht.1.le, ht.2⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hl := strip hh (fun t => D t * g t) (C := M * B)
    (fun t ht => prod ⟨ht.1.le, by linarith [ht.2]⟩ ⟨ht.1.le, ht.2.trans hhT⟩)
  have htop := strip (show T - h ≤ T by linarith) g (C := B)
    (fun t ht => hB t ⟨by linarith [ht.1], ht.2⟩)
  have hbot := strip hh g (C := B) (fun t ht => hB t ⟨ht.1.le, ht.2.trans hhT⟩)
  have hc : Continuous (fun t : ℝ => g (t - h)) := hg.comp (continuous_id.sub continuous_const)
  have hv : (∫ t in h..T, g t - g (t - h)) =
      (∫ t in T - h..T, g t) - (∫ t in (0 : ℝ)..h, g t) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_sub_right]
    simp only [sub_self]
    linarith only [intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) 0 h) (hg.intervalIntegrable h T),
      intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) 0 (T - h)) (hg.intervalIntegrable (T - h) T)]
  have hvle : (∫ t in h..T, g t - g (t - h)) ≤ 2 * B * h := by
    rw [hv]
    linarith only [(abs_le.mp htop).2, (abs_le.mp hbot).1]
  have hvnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hhT
    (f := fun t => D t * (g t - g (t - h))) (g := fun t => M * (g t - g (t - h))) (by
      filter_upwards with t ht
      have ht0 : 0 ≤ t := hh.trans ht.1.le
      have hdiff := hmono (a := t - h) (b := t)
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨ht0, ht.2⟩ (by linarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdiff)]
      exact mul_le_mul_of_nonneg_right (hM t ⟨ht0, by linarith [ht.2]⟩) (sub_nonneg.mpr hdiff))
    (((hg.sub hc).intervalIntegrable h T).const_mul M)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hvnorm
  have hmid := hvnorm.trans (mul_le_mul_of_nonneg_left hvle hm)
  rw [integral_increment_mul_eq_boundary D g T h hD hg]
  apply abs_le.mpr
  constructor <;> nlinarith only [(abs_le.mp hs).1, (abs_le.mp hs).2,
    (abs_le.mp hl).1, (abs_le.mp hl).2, (abs_le.mp hmid).1, (abs_le.mp hmid).2]

namespace ActualZeroDiscrepancy

open Zeta23

/-- The exact gamma drift is monotone, including for windows starting at zero. -/
theorem gammaWindowDrift_monotoneOn {h : ℝ} (hh : 0 ≤ h) (lam : ℝ) :
    MonotoneOn (fun t : ℝ => (∫ u in t..t + h, mu u) - lam) (Ici 0) := by
  have shift (x : ℝ) : (∫ u in x..x + h, mu u) = ∫ u in (0 : ℝ)..h, mu (u + x) := by
    simpa only [zero_add, add_comm h x] using
      (intervalIntegral.integral_comp_add_right (a := 0) (b := h) mu x).symm
  intro a ha b hb hab
  change (∫ u in a..a + h, mu u) - lam ≤ (∫ u in b..b + h, mu u) - lam
  rw [shift a, shift b]
  apply sub_le_sub_right
  have hc := RvM.mu_continuous gammaFacts
  exact intervalIntegral.integral_mono_on hh
    ((hc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
    ((hc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
    (fun t ht => MuFields.mu_monotoneOn
      (show 0 ≤ t + a by linarith [ht.1, mem_Ici.mp ha])
      (show 0 ≤ t + b by linarith [ht.1, mem_Ici.mp hb]) (by linarith))

/-- The actual mixed term is bounded using only the discrepancy amplitude
and the two values of the smooth weight at the ends of the observation interval. -/
theorem abs_integral_discrepancy_increment_mul_gammaDrift_le {T h lam M B : ℝ}
    (hh : 0 ≤ h) (hhT : h ≤ T)
    (hM : ∀ t ∈ Icc 0 (T + h), |discrepancy t| ≤ M)
    (hlo : -B ≤ (∫ u in (0 : ℝ)..h, mu u) - lam)
    (hhi : (∫ u in T..T + h, mu u) - lam ≤ B) :
    |∫ t in (0 : ℝ)..T, (discrepancy (t + h) - discrepancy t) *
      ((∫ u in t..t + h, mu u) - lam)| ≤ 4 * h * M * B := by
  let g := fun t : ℝ => (∫ u in t..t + h, mu u) - lam
  have hc : Continuous g := by
    simp only [g, ← smoothCount_sub]
    exact ((smoothCount_continuous.comp (continuous_id.add continuous_const)).sub
      smoothCount_continuous).sub continuous_const
  have hg := gammaWindowDrift_monotoneOn hh lam
  have hT := hh.trans hhT
  apply abs_integral_increment_mul_le discrepancy g hh hhT discrepancy_intervalIntegrable hc
    (hg.mono (fun _ ht => ht.1)) hM
  intro t ht
  apply abs_le.mpr
  constructor
  · exact (by simpa [g] using hlo : -B ≤ g 0).trans
      (hg (a := 0) (b := t) (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.1) ht.1)
  · exact (hg (a := t) (b := T) (mem_Ici.mpr ht.1) (mem_Ici.mpr hT) ht.2).trans hhi

/-- A uniform finite - height mixed - term bound at every width at most one.
The only height dependence outside the microscopic width is logarithmic.
The exact weight retains the chosen center. -/
theorem exists_abs_integral_discrepancy_increment_mul_gammaDrift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T h lam : ℝ, 1 ≤ T → 0 ≤ h → h ≤ 1 →
      |∫ t in (0 : ℝ)..T, (discrepancy (t + h) - discrepancy t) *
        ((∫ u in t..t + h, mu u) - lam)| ≤
        4 * h * (C * (1 + Real.log (T + 5))) * (1 + |lam| + h * C * Real.log (T + 4)) := by
  obtain ⟨A, hA, hD⟩ := exists_abs_discrepancy_le_log
  obtain ⟨K, hK, hk⟩ := RvM.mu_le_log gammaFacts
  let C := max A K
  have hAC : A ≤ C := le_max_left _ _
  have hKC : K ≤ C := le_max_right _ _
  have hC : 0 < C := hA.trans_le hAC
  refine ⟨C, hC, ?_⟩
  intro T h lam hT hh hh1
  have hlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hplus : 0 ≤ h * C * Real.log (T + 4) := mul_nonneg (mul_nonneg hh hC.le) hlog
  have ha : -h ≤ ∫ u in (0 : ℝ)..h, mu u := by
    have hle := intervalIntegral.integral_mono_on (μ := volume) hh
      (f := fun _ : ℝ => -1) intervalIntegrable_const
      ((RvM.mu_continuous gammaFacts).intervalIntegrable 0 h)
      (fun u _ => MuFields.neg_one_lt_mu_zero.le.trans (MuFields.mu_zero_le u))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg_one] using hle
  have hupper : |∫ u in T..T + h, mu u| ≤ C * Real.log (T + 4) * h := by
    have hinc : T ≤ T + h := by linarith
    have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T + h)
      (f := mu) (C := C * Real.log (T + 4)) (fun u hu => by
        rw [uIoc_of_le hinc] at hu
        rw [Real.norm_eq_abs]
        refine (hk u (hT.trans hu.1.le)).trans ?_
        apply mul_le_mul hKC (Real.log_le_log (by linarith [hu.1]) (by linarith [hu.2]))
          (Real.log_nonneg (by linarith [hu.1])) hC.le)
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] using he
  apply abs_integral_discrepancy_increment_mul_gammaDrift_le hh (hh1.trans hT)
  · intro t ht
    exact (hD t ht.1).trans (mul_le_mul hAC
      (add_le_add le_rfl (Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])))
      (by linarith [Real.log_nonneg (show 1 ≤ t + 4 by linarith [ht.1])]) hC.le)
  · linarith only [ha, hh1, le_abs_self lam, hplus]
  · nlinarith only [(abs_le.mp hupper).2, neg_abs_le lam]

/-- The signed cross term is bounded by a constant times the unfolded width,
uniformly in height and for bounded widths and centers. -/
theorem eventually_abs_integral_discrepancy_increment_mul_gammaDrift_le_width_mul {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R lam : ℝ, 0 ≤ R → R ≤ B → |lam| ≤ B →
      let h := R / (Real.log T / (2 * Real.pi))
      |∫ t in (0 : ℝ)..T, (discrepancy (t + h) - discrepancy t) *
        ((∫ u in t..t + h, mu u) - lam)| ≤ R * K := by
  obtain ⟨C, hC, hc⟩ := exists_abs_integral_discrepancy_increment_mul_gammaDrift_le
  let P := 2 * Real.pi * B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨12 * C * (2 * Real.pi) * (1 + B + 2 * P * C), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 P)] with T hT hlog
  intro R lam hR hRB hlam
  let h := R / (Real.log T / (2 * Real.pi))
  have hL := (le_max_left (1 : ℝ) P).trans hlog
  have hPL := (le_max_right (1 : ℝ) P).trans hlog
  have hp : 0 < Real.log T := by linarith
  have hnn : 0 ≤ h := div_nonneg hR (div_nonneg hp.le (by positivity))
  have hprod : h * Real.log T = 2 * Real.pi * R := by
    dsimp [h]
    field_simp [hp.ne', Real.pi_ne_zero]
    <;> ring
  have hhP : h * Real.log T ≤ P := by rw [hprod]; exact mul_le_mul_of_nonneg_left hRB (by positivity)
  have hh1 : h ≤ 1 := (le_of_mul_le_mul_right ((hhP.trans hPL).trans_eq (one_mul _).symm) hp)
  have hlog5 : Real.log (T + 5) ≤ 2 * Real.log T := by
    calc Real.log (T + 5) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog4 : Real.log (T + 4) ≤ 2 * Real.log T :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlog5
  have hleft : 4 * h * (C * (1 + Real.log (T + 5))) ≤ 12 * C * (2 * Real.pi * R) := by
    calc
      _ ≤ 4 * h * (C * (3 * Real.log T)) := by gcongr <;> linarith
      _ = 12 * C * (h * Real.log T) := by ring
      _ = _ := by rw [hprod]
  have hright : 1 + |lam| + h * C * Real.log (T + 4) ≤ 1 + B + 2 * P * C := by
    apply add_le_add (add_le_add le_rfl hlam)
    calc h * C * Real.log (T + 4) ≤ h * C * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hlog4 (mul_nonneg hnn hC.le)
      _ = 2 * (h * Real.log T) * C := by ring
      _ ≤ 2 * P * C := by gcongr
  have he := (hc T h lam (by linarith) hnn hh1).trans
    (mul_le_mul hleft hright
      (by
        have hpos := Real.log_nonneg (show 1 ≤ T + 4 by linarith)
        positivity) (by positivity))
  exact he.trans_eq (by ring)

/-- On a compact range of unfolded widths and centers the signed cross
term is bounded uniformly in height before division by height. -/
theorem eventually_abs_integral_discrepancy_increment_mul_gammaDrift_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R lam : ℝ, 0 ≤ R → R ≤ B → |lam| ≤ B →
      let h := R / (Real.log T / (2 * Real.pi))
      |∫ t in (0 : ℝ)..T, (discrepancy (t + h) - discrepancy t) *
        ((∫ u in t..t + h, mu u) - lam)| ≤ K := by
  obtain ⟨K, hK, he⟩ := eventually_abs_integral_discrepancy_increment_mul_gammaDrift_le_width_mul hB
  refine ⟨B * K, mul_nonneg hB hK, ?_⟩
  filter_upwards [he] with T hT R lam hR hRB hlam
  exact (hT R lam hR hRB hlam).trans (mul_le_mul_of_nonneg_right hRB hK)

end ActualZeroDiscrepancy
end RiemannResearch.Analysis

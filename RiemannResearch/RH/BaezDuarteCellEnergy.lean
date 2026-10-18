import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Reciprocal-cell moments and the five-fourths energy comparison

Source: the natural-dilation setup of L. Baez-Duarte,
"A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis, 2",
https://arxiv.org/abs/math/0205003, equations (2.3)--(2.4).
The cell-moment refinement is an elementary development of that setup;
no mathematical priority is claimed.

The actual first cell moment is identified by an interval integral.
The scalar and infinite weighted energy comparisons are unconditional
given the displayed ordinary positivity and summability hypotheses.
The global change of variables and partition identifying this model with
`BaezDuarte.naturalError` is not formalized here; see the research record
`BaezDuarte2002Research20261018.md`. In particular no RH estimate is assumed.
-/

namespace RiemannResearch.RH.BaezDuarteCellEnergy

/-- Reciprocal trapezoid bound, proved by monotonicity of its difference. -/
private theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun t => (t - t⁻¹) / 2 - Real.log t
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt f ((1 - t⁻¹) ^ 2 / 2) t := by
    have h := (((hasDerivAt_id t).sub
      ((hasDerivAt_id t).inv (ne_of_gt ht))).div_const 2).sub
      (Real.hasDerivAt_log (ne_of_gt ht))
    convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [ne_of_gt ht]; ring)
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
      exact (hd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
      rw [(hd t ht').deriv]
      positivity
  have h := hmono (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show x ∈ Set.Ioi 0 by change 0 < x; linarith) hx
  dsimp [f] at h
  norm_num at h
  linarith

/-- Closed form of the mean of the density n(n+1)/(n+u)^2 on [0,1]. -/
noncomputable def cellMean (n : ℝ) : ℝ :=
  n * (n + 1) * Real.log ((n + 1) / n) - n

theorem cellMean_nonneg {n : ℝ} (hn : 0 < n) : 0 ≤ cellMean n := by
  have hn1 : 0 < n + 1 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn)
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (mul_pos hn hn1))
  have hid : n * (n + 1) * (1 - ((n + 1) / n)⁻¹) = n := by
    field_simp [ne_of_gt hn, ne_of_gt hn1]
    ring
  rw [hid] at hmul
  dsimp [cellMean]
  linarith

theorem cellMean_le_half {n : ℝ} (hn : 0 < n) : cellMean n ≤ 1 / 2 := by
  have hn1 : 0 < n + 1 := by linarith
  have hx : (1 : ℝ) ≤ (n + 1) / n := (le_div_iff₀ hn).2 (by linarith)
  have hlog := log_le_half_sub_inv hx
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (mul_pos hn hn1))
  have hid : n * (n + 1) * (((n + 1) / n - ((n + 1) / n)⁻¹) / 2) = n + 1 / 2 := by
    field_simp [ne_of_gt hn, ne_of_gt hn1]
    ring
  rw [hid] at hmul
  dsimp [cellMean]
  linarith

theorem cellMean_formula (n : ℝ) (hn : n ≠ 0) :
    cellMean n = n * (n + 1) * Real.log (1 + 1 / n) - n := by
  have harg : (n + 1) / n = 1 + 1 / n := by
    field_simp [hn]
  simp only [cellMean, harg]

end RiemannResearch.RH.BaezDuarteCellEnergy

open scoped BigOperators
namespace RiemannResearch.RH.BaezDuarteCellEnergy
/-- Normalized residual energy, with its share of the exact exterior charge. -/
def cellEnergy (r A m v : ℝ) : ℝ := (r + A * m) ^ 2 + A ^ 2 * (1 + v)
/-- Complete polynomial identity before any nonnegative term is discarded. -/
theorem cellEnergy_exact_remainder (r A m v : ℝ) :
    5 * cellEnergy r A m v - 4 * r ^ 2 =
      (r + 5 * A * m) ^ 2 + 5 * A ^ 2 * (1 - 4 * m ^ 2 + v) := by
  unfold cellEnergy
  ring
/-- The moment bounds improve the elementary squared-error factor two to five-fourths. -/
theorem sq_le_five_fourths_cellEnergy (r A m v : ℝ)
    (hm : 0 ≤ m) (hm' : m ≤ 1 / 2) (hv : 0 ≤ v) :
    r ^ 2 ≤ (5 / 4 : ℝ) * cellEnergy r A m v := by
  have hm2 : 0 ≤ 1 - 4 * m ^ 2 := by nlinarith
  have hp := mul_nonneg (sq_nonneg A) (show 0 ≤ 1 - 4 * m ^ 2 + v by linarith)
  have he := cellEnergy_exact_remainder r A m v
  nlinarith [sq_nonneg (r + 5 * A * m)]
/-- Complete infinite weighted comparison; also establishes target square summability.
Specialization to the continuous natural error needs the separate cell-partition identity. -/
theorem weighted_energy_le (w r m v : ℕ → ℝ) (A : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hm : ∀ n, 0 ≤ m n)
    (hm' : ∀ n, m n ≤ 1 / 2) (hv : ∀ n, 0 ≤ v n)
    (hs : Summable (fun n => w n * cellEnergy (r n) A (m n) (v n))) :
    Summable (fun n => w n * (r n) ^ 2) ∧
      (∑' n, w n * (r n) ^ 2) ≤
        (5 / 4 : ℝ) * ∑' n, w n * cellEnergy (r n) A (m n) (v n) := by
  have hpoint (n : ℕ) :
      w n * (r n) ^ 2 ≤ (5 / 4 : ℝ) * (w n * cellEnergy (r n) A (m n) (v n)) := by
    have h := mul_le_mul_of_nonneg_left
      (sq_le_five_fourths_cellEnergy (r n) A (m n) (v n) (hm n) (hm' n) (hv n)) (hw n)
    nlinarith
  have ht := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hw n) (sq_nonneg (r n))) hpoint (hs.mul_left (5 / 4 : ℝ))
  refine ⟨ht, ?_⟩
  simpa only [tsum_mul_left] using
    ht.tsum_le_tsum hpoint (hs.mul_left (5 / 4 : ℝ))
end RiemannResearch.RH.BaezDuarteCellEnergy

namespace RiemannResearch.RH.BaezDuarteCellEnergy

/-- The scalar cell mean is the actual normalized first moment. -/
theorem cellMean_eq_integral {n : ℝ} (hn : 0 < n) :
    cellMean n = n * (n + 1) * ∫ u in (0 : ℝ)..1, u / (n + u) ^ 2 := by
  have hn1 : 0 < n + 1 := by linarith
  have hpos (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) : 0 < n + u := by
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    linarith [hu'.1]
  have hd (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => Real.log (n + t) + n * (n + t)⁻¹)
        (u / (n + u) ^ 2) u := by
    have ha := (hasDerivAt_id u).const_add n
    have h := (ha.log (ne_of_gt (hpos u hu))).add
      ((ha.inv (ne_of_gt (hpos u hu))).const_mul n)
    convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [ne_of_gt (hpos u hu)]; ring)
  have hc : ContinuousOn (fun u : ℝ => u / (n + u) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro u hu
    exact pow_ne_zero 2 (ne_of_gt (hpos u hu))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [hi]
  simp only [cellMean, add_zero,
    Real.log_div (ne_of_gt hn1) (ne_of_gt hn)]
  field_simp [ne_of_gt hn, ne_of_gt hn1]
  ring

end RiemannResearch.RH.BaezDuarteCellEnergy

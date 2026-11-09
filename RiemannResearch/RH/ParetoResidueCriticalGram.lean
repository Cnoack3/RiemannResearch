/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueClassMellin
import RiemannResearch.Analysis.MellinDifferenceBounds
import RiemannResearch.RH.CriticalMellinGramLimits
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Critical-line Gram limits for exact Pareto residue classes

The finite zero projection follows the strategy of Burnol, *A lower bound in
an approximation problem involving the zeros of the Riemann zeta function*,
§5, https://arxiv.org/abs/math/0103058. Here the rows are grouped over
complete Pareto progressions. Their unnormalized complex Gram differs from
the first-period Gram by a bounded amount. The project critical-ordinate
Gram theorem then supplies the normalized limit.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.Cesaro
open SpectralObstruction

private abbrev critical := MellinFrequency.criticalPoint

def criticalScale (x : ℝ) : ℝ := 1 / (x * Real.sqrt x)

private theorem criticalScale_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ criticalScale x := by
  unfold criticalScale
  positivity

private theorem criticalScale_eq_rpow {x : ℝ} (hx : 0 < x) :
    criticalScale x = x ^ (-(3 / 2 : ℝ)) := by
  rw [criticalScale, Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

private theorem criticalScale_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    criticalScale (x * y) = criticalScale x * criticalScale y := by
  rw [criticalScale_eq_rpow (mul_pos hx hy), criticalScale_eq_rpow hx, criticalScale_eq_rpow hy,
    Real.mul_rpow hx.le hy.le]

private theorem criticalScale_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    criticalScale y ≤ criticalScale x := by
  rw [criticalScale_eq_rpow hx, criticalScale_eq_rpow (hx.trans_le hxy)]
  exact Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num)

private theorem criticalScale_relative {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    criticalScale y ≤ x / y * criticalScale x := by
  have hy := hx.trans_le hxy
  have hsx := Real.sqrt_pos.mpr hx
  calc
    _ = (1 / y) * (1 / Real.sqrt y) := by unfold criticalScale; ring
    _ ≤ (1 / y) * (1 / Real.sqrt x) :=
      mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hsx (Real.sqrt_le_sqrt hxy)) (by positivity)
    _ = _ := by unfold criticalScale; field_simp

private theorem critical_first_bound (t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖mellinFirst (critical t) n‖ ≤ ‖critical t‖ * criticalScale (n : ℝ) := by
  rw [criticalScale_eq_rpow (by exact_mod_cast hn)]
  have h := mellinFirst_norm_le (critical t) (by simp) n hn
  simpa only [MellinFrequency.criticalPoint_re, show -(1 / 2 : ℝ) - 1 = -(3 / 2) by norm_num]
    using h

def criticalTailMass : ℝ := ∑' k : ℕ, criticalScale ((k + 1 : ℕ) : ℝ)

private theorem criticalTailMass_nonneg : 0 ≤ criticalTailMass :=
  tsum_nonneg (fun _ => criticalScale_nonneg (Nat.cast_nonneg _))

private theorem criticalTailScale_summable :
    Summable (fun k : ℕ => criticalScale ((k + 1 : ℕ) : ℝ)) := by
  simp_rw [criticalScale_eq_rpow (by positivity : (0 : ℝ) < (( _ + 1 : ℕ) : ℝ))]
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))

/-- The complete progression after its first cell has uniform power decay. -/
theorem critical_class_tail_bound (t : ℝ) (N : ℕ) (r : Fin (N + 1)) :
    ‖classMellin N (critical t) r - mellinFirst (critical t) (r.val + 1)‖ ≤
      ‖critical t‖ * criticalScale ((N + 1 : ℕ) : ℝ) * criticalTailMass := by
  let u : ℕ → ℂ := fun k => mellinFirst (critical t) (r.val + (N + 1) * (k + 1) + 1)
  let a := ‖critical t‖ * criticalScale ((N + 1 : ℕ) : ℝ)
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (criticalScale_nonneg (Nat.cast_nonneg _))
  have hle (k : ℕ) : ‖u k‖ ≤ a * criticalScale ((k + 1 : ℕ) : ℝ) := by
    have hnat : (N + 1) * (k + 1) ≤ r.val + (N + 1) * (k + 1) + 1 := by omega
    have hR : ((N + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
        ((r.val + (N + 1) * (k + 1) + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul] using (show
        (((N + 1) * (k + 1) : ℕ) : ℝ) ≤ _ by exact_mod_cast hnat)
    have hscale := criticalScale_anti (by positivity) hR
    rw [criticalScale_mul (by positivity) (by positivity)] at hscale
    change ‖mellinFirst (critical t) (r.val + (N + 1) * (k + 1) + 1)‖ ≤ _
    exact (critical_first_bound t _ (Nat.succ_pos _)).trans
      ((mul_le_mul_of_nonneg_left hscale (norm_nonneg _)).trans_eq (by simp [a, mul_assoc]))
  have hsum := criticalTailScale_summable.mul_left a
  have hu := Summable.of_nonneg_of_le (fun k => norm_nonneg (u k)) hle hsum
  have hs := (classMellin_summable N (critical t) (by simp) r).tsum_eq_zero_add
  change classMellin N (critical t) r =
    mellinFirst (critical t) (r.val + (N + 1) * 0 + 1) + ∑' k, u k at hs
  simp only [Nat.mul_zero, Nat.add_zero] at hs
  rw [hs, add_sub_cancel_left]
  calc
    _ ≤ ∑' k, ‖u k‖ := norm_tsum_le_tsum_norm hu
    _ ≤ ∑' k, a * criticalScale ((k + 1 : ℕ) : ℝ) := hu.tsum_le_tsum hle hsum
    _ = _ := by rw [tsum_mul_left]; rfl

private theorem classWeight_relative (N : ℕ) (r : Fin (N + 1)) :
    paretoWeight r.val ≤ classWeight N r ∧
      classWeight N r - paretoWeight r.val ≤
        paretoWeight r.val * (((r.val : ℝ) + 1) / ((N : ℝ) + 1)) := by
  have hlo := positiveWeight_le_progressionWeight (N + 1) (r.val + 1) (Nat.succ_pos N)
  rw [positiveWeight_succ] at hlo
  refine ⟨hlo, ?_⟩
  have hu := progressionWeight_upper_one (N + 1) (r.val + 1) (Nat.succ_pos N)
  rw [positiveWeight_succ] at hu
  change classWeight N r ≤ paretoWeight r.val +
    1 / (((N + 1 : ℕ) : ℝ) * (((r.val + 1 : ℕ) : ℝ) + 1)) at hu
  push_cast at hu
  have he : paretoWeight r.val * (((r.val : ℝ) + 1) / ((N : ℝ) + 1)) =
      1 / (((N : ℝ) + 1) * ((r.val : ℝ) + 1 + 1)) := by
    unfold paretoWeight
    field_simp
    ring
  linarith

private theorem criticalScale_sq {x : ℝ} (hx : 0 < x) :
    criticalScale x ^ 2 = 1 / x ^ 3 := by
  rw [criticalScale, div_pow, one_pow, mul_pow, Real.sq_sqrt hx.le]
  ring

def classCrossTerm (t u : ℝ) (N : ℕ) (r : Fin (N + 1)) : ℂ :=
  classMellin N (critical t) r * star (classMellin N (critical u) r) /
    (classWeight N r : ℂ)

def firstCrossTerm (t u : ℝ) (n : ℕ) : ℂ :=
  mellinFirst (critical t) (n + 1) * star (mellinFirst (critical u) (n + 1)) /
    (paretoWeight n : ℂ)

private theorem crossTerm_diff_le (t u : ℝ) (N : ℕ) (r : Fin (N + 1)) :
    ‖classCrossTerm t u N r - firstCrossTerm t u r.val‖ ≤
      (2 * ‖critical t‖ * ‖critical u‖ * (1 + criticalTailMass)^2) / ((N : ℝ) + 1) := by
  let L : ℝ := (N : ℝ) + 1
  let x : ℝ := (r.val : ℝ) + 1
  let θ := x / L
  let h := criticalScale x
  let C := criticalTailMass
  let A := ‖critical t‖
  let B := ‖critical u‖
  let p := paretoWeight r.val
  let w := classWeight N r
  let a := classMellin N (critical t) r
  let b := classMellin N (critical u) r
  let d := mellinFirst (critical t) (r.val + 1)
  let e := mellinFirst (critical u) (r.val + 1)
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) r.val]
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hL : 0 < L := by dsimp [L]; positivity
  have hxL : x ≤ L := by
    have hr : (r.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show r.val ≤ N by omega)
    dsimp only [x, L]
    linarith
  have hθ : 0 ≤ θ := div_nonneg hx.le hL.le
  have hθ1 : θ ≤ 1 := (div_le_one hL).mpr hxL
  have hh : 0 ≤ h := criticalScale_nonneg hx.le
  have hC : 0 ≤ C := criticalTailMass_nonneg
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hp : 0 < p := paretoWeight_pos _
  obtain ⟨hpw, hwp⟩ := classWeight_relative N r
  have hw : 0 < w := hp.trans_le hpw
  have hrw : (w - p) / p ≤ θ := by
    apply (div_le_iff₀ hp).2
    simpa only [mul_comm] using hwp
  have hrw0 : 0 ≤ (w - p) / p := div_nonneg (sub_nonneg.mpr hpw) hp.le
  have hd : ‖d‖ ≤ A * h := by
    simpa only [d, A, h, x, Nat.cast_add, Nat.cast_one] using
      critical_first_bound t (r.val + 1) (Nat.succ_pos _)
  have he : ‖e‖ ≤ B * h := by
    simpa only [e, B, h, x, Nat.cast_add, Nat.cast_one] using
      critical_first_bound u (r.val + 1) (Nat.succ_pos _)
  have hscale : criticalScale L ≤ θ * h := criticalScale_relative hx hxL
  have ht : ‖a - d‖ ≤ A * (θ * h) * C := by
    have htail := critical_class_tail_bound t N r
    simp only [Nat.cast_add, Nat.cast_one] at htail
    exact htail.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale hA) hC)
  have hu : ‖b - e‖ ≤ B * (θ * h) * C := by
    have htail := critical_class_tail_bound u N r
    simp only [Nat.cast_add, Nat.cast_one] at htail
    exact htail.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale hB) hC)
  have hb : ‖b‖ ≤ B * h * (1 + C) := by
    have hsmall : B * (θ * h) * C ≤ B * h * C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right hθ1 hh).trans_eq (one_mul h)) hB) hC
    calc
      _ = ‖(b - e) + e‖ := by rw [sub_add_cancel]
      _ ≤ ‖b - e‖ + ‖e‖ := norm_add_le _ _
      _ ≤ B * h * C + B * h := add_le_add (hu.trans hsmall) he
      _ = _ := by ring
  have hsplit :
      a * star b / (w : ℂ) - d * star e / (p : ℂ) =
        ((a - d) * star b + d * star (b - e) -
          (((w - p) / p : ℝ) : ℂ) * d * star e) / (w : ℂ) := by
    rw [star_sub, Complex.ofReal_div, Complex.ofReal_sub]
    field_simp [Complex.ofReal_ne_zero.mpr hp.ne', Complex.ofReal_ne_zero.mpr hw.ne']
    ring
  have hnum :
      ‖(a - d) * star b + d * star (b - e) -
        (((w - p) / p : ℝ) : ℂ) * d * star e‖ ≤
        (A * (θ * h) * C) * (B * h * (1 + C)) +
          (A * h) * (B * (θ * h) * C) + θ * (A * h) * (B * h) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_star]
        exact mul_le_mul ht hb (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_star]
        exact mul_le_mul hd hu (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hrw0]
      exact mul_le_mul (mul_le_mul hrw hd (norm_nonneg _) hθ) he
        (norm_nonneg _) (by positivity)
  have hscale2 : θ * h^2 / p ≤ 2 / L := by
    have hform : p = 1 / (x * (x + 1)) := by dsimp [p, paretoWeight, x]; ring
    have hident : θ * h^2 / p = (x + 1) / (L * x) := by
      rw [hform, show h ^ 2 = 1 / x ^ 3 from criticalScale_sq hx]
      dsimp only [θ]
      field_simp
    rw [hident]
    calc
      _ ≤ (2 * x) / (L * x) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have hn : 0 ≤ (A * (θ * h) * C) * (B * h * (1 + C)) +
      (A * h) * (B * (θ * h) * C) + θ * (A * h) * (B * h) := by positivity
  change ‖a * star b / (w : ℂ) - d * star e / (p : ℂ)‖ ≤ _
  rw [hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  calc
    _ ≤ ((A * (θ * h) * C) * (B * h * (1 + C)) +
          (A * h) * (B * (θ * h) * C) + θ * (A * h) * (B * h)) / w :=
      div_le_div_of_nonneg_right hnum hw.le
    _ ≤ ((A * (θ * h) * C) * (B * h * (1 + C)) +
          (A * h) * (B * (θ * h) * C) + θ * (A * h) * (B * h)) / p :=
      div_le_div_of_nonneg_left hn hp hpw
    _ = (A * B * (1 + C)^2) * (θ * h^2 / p) := by ring
    _ ≤ (A * B * (1 + C)^2) * (2 / L) :=
      mul_le_mul_of_nonneg_left hscale2 (by positivity)
    _ = _ := by dsimp only [A, B, C, L]; ring

theorem firstCrossTerm_eq (t u : ℝ) (n : ℕ) :
    firstCrossTerm t u n =
      (paretoWeight n : ℂ) * mellinMode (MellinFrequency.criticalPoint t) n *
        star (mellinMode (MellinFrequency.criticalPoint u) n) := by
  have h (v : ℝ) :
      mellinMode (critical v) n =
        mellinFirst (critical v) (n + 1) / (paretoWeight n : ℂ) := by
    unfold mellinMode mellinFirst paretoWeight
    push_cast
    rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  have hp : (paretoWeight n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (paretoWeight_pos n).ne'
  rw [firstCrossTerm, h, h]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  field_simp [hp]

/-- The complete grouped complex Gram numerator before division by log L. -/
def classCrossSum (t u : ℝ) (N : ℕ) : ℂ :=
  ∑ r : Fin N, classCrossTerm t u N r.castSucc

/-- Grouping every progression changes the first-period Gram by a uniformly
bounded amount, including the perturbation of the physical class weights. -/
theorem classCrossSum_firstPeriod_bound (t u : ℝ) (N : ℕ) :
    ‖classCrossSum t u N - ∑ n ∈ Finset.range N, firstCrossTerm t u n‖ ≤
      2 * ‖critical t‖ * ‖critical u‖ * (1 + criticalTailMass)^2 := by
  let K := 2 * ‖critical t‖ * ‖critical u‖ * (1 + criticalTailMass)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [classCrossSum, ← Fin.sum_univ_eq_sum_range, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : Fin N, ‖classCrossTerm t u N r.castSucc - firstCrossTerm t u r.val‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : Fin N, K / ((N : ℝ) + 1) :=
      Finset.sum_le_sum (fun r _ => crossTerm_diff_le t u N r.castSucc)
    _ = (N : ℝ) * (K / ((N : ℝ) + 1)) := by simp [nsmul_eq_mul]
    _ ≤ ((N : ℝ) + 1) * (K / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp only [K]; field_simp

/-- The normalized grouped Gram uses all physical cells in every class. -/
def classCross (t u : ℝ) (N : ℕ) : ℂ :=
  classCrossSum t u N / (Real.log ((N : ℝ) + 1) : ℂ)

private theorem tendsto_modulus : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
  tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop

/-- The fixed critical ordinate Gram limit survives exact progression grouping. -/
theorem classCross_tendsto (t u : ℝ) :
    Tendsto (classCross t u) atTop
      (𝓝 (if t = u then critical t * star (critical u) else 0)) := by
  let K := 2 * ‖critical t‖ * ‖critical u‖ * (1 + criticalTailMass)^2
  have hi : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_modulus)
  have hbound (N : ℕ) :
      ‖classCross t u N - criticalCross t u N‖ ≤ K * (Real.log ((N : ℝ) + 1))⁻¹ := by
    have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
    rw [classCross, criticalCross, ← sub_div, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog, ← div_eq_mul_inv]
    simp_rw [← firstCrossTerm_eq]
    exact div_le_div_of_nonneg_right (classCrossSum_firstPeriod_bound t u N)
      hlog
  have hn : Tendsto (fun N : ℕ => ‖classCross t u N - criticalCross t u N‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hi.const_mul K)
  have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa only [Pi.add_apply, sub_add_cancel, zero_add] using
    hz.add (criticalCross_tendsto t u)

theorem critical_class_multiples_bound (t : ℝ) (N : ℕ) :
    ‖classMellin N (critical t) (Fin.last N)‖ ≤
      ‖critical t‖ * (1 + criticalTailMass) * criticalScale ((N + 1 : ℕ) : ℝ) := by
  let s := critical t
  let a := classMellin N s (Fin.last N)
  let d := mellinFirst s (N + 1)
  have h := critical_class_tail_bound t N (Fin.last N)
  change ‖a - d‖ ≤ _ at h
  calc
    ‖a‖ = ‖(a - d) + d‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - d‖ + ‖d‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add h (critical_first_bound t (N + 1) (Nat.succ_pos N))).trans_eq (by ring)

theorem critical_class_multiples_tendsto (t : ℝ) :
    Tendsto (fun N : ℕ => classMellin N (critical t) (Fin.last N)) atTop (𝓝 0) := by
  let C := ‖critical t‖ * (1 + criticalTailMass)
  have hC : 0 ≤ C := by dsimp [C]; positivity [criticalTailMass_nonneg]
  have hscale (N : ℕ) : criticalScale ((N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one, criticalScale, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (N : ℝ) + 1 = ((N : ℝ) + 1) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt (by
          linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ (N : ℝ) + 1))) (by positivity)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
    (by simpa using (tendsto_inv_atTop_zero.comp tendsto_modulus).const_mul C)
  exact (critical_class_multiples_bound t N).trans (mul_le_mul_of_nonneg_left (hscale N) hC)

private theorem critical_neg (t : ℝ) : critical (-t) = star (critical t) := by
  apply Complex.ext <;> simp [MellinFrequency.criticalPoint, Complex.mul_re, Complex.mul_im]

private theorem first_critical_neg (t : ℝ) (n : ℕ) :
    mellinFirst (critical (-t)) n = star (mellinFirst (critical t) n) := by
  have hn (m : ℕ) : Complex.arg (m : ℂ) ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]
    exact Real.pi_pos.ne
  unfold mellinFirst
  rw [critical_neg, star_sub, ← star_neg]
  congr 1
  · simpa only [Complex.star_def, Complex.conj_natCast] using
      Complex.cpow_conj (n : ℂ) (-critical t) (hn n)
  · simpa only [Complex.star_def, Complex.conj_natCast] using
      Complex.cpow_conj ((n + 1 : ℕ) : ℂ) (-critical t) (hn (n + 1))

/-- Negative ordinates give exactly the conjugate grouped first differences. -/
theorem classMellin_critical_neg (t : ℝ) (N : ℕ) (r : Fin (N + 1)) :
    classMellin N (critical (-t)) r = star (classMellin N (critical t) r) := by
  unfold classMellin
  rw [tsum_star]
  apply tsum_congr
  intro k
  exact first_critical_neg t _

end RiemannResearch.RH.Pareto.ResidueMellin

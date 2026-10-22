/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HyperbolaLogOptimization
import RiemannResearch.Analysis.PowerLogProfiles
import RiemannResearch.RH.ArithmeticFloorHyperbolaPowerBounds
import RiemannResearch.RH.ArithmeticFloorTruncationBounds
import RiemannResearch.RH.ParetoDominatedConvergence
import RiemannResearch.RH.DampedMobiusSignedHeadClosure

/-!
# Critical logarithmic arithmetic Hilbert convergence

The original signed prefix and density estimates survive every conductor
cutoff. A proved integer log cutoff yields a summable uniform physical
envelope. Limit existence and norm convergence are conclusions. At subhalf
Möbius damping the two arithmetic estimates remain open hypotheses.
-/

noncomputable section
open Filter Set RiemannResearch.Analysis
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Complete critical logarithmic criterion with conductor-uniform signed
prefix bounds. The original density-tail estimate is automatically made
uniform by truncation. All arithmetic hypotheses are explicit. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_uniform_critical_log_bounds
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε b : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hb : 1 < b)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ M t : ℕ, 0 < t →
      |positiveArithmeticPrefix (arithmeticCutoffWeight w M) t| ≤
        B * (t : ℝ) ^ ε / (6 + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (6 + Real.log (t : ℝ)) ^ b)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n - (n : ℝ) * C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have hp : 0 < 1 - ε := by linarith
  have hlog (t : ℕ) (ht : 0 < t) : 0 < 6 + Real.log (t : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Real.log_nonneg ht1]
  let T := fun t : ℕ => D / ((t : ℝ) ^ (1 - ε) * (6 + Real.log (t : ℝ)) ^ b)
  have htmono : AntitoneOn T (Set.Ici 1) := by
    intro i hi j hj hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by change 1 ≤ i at hi; omega)
    have hiN : 0 < i := by exact_mod_cast hi0
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hl := hlog i hiN
    apply div_le_div_of_nonneg_left hD (by positivity)
    apply mul_le_mul
    · exact Real.rpow_le_rpow hi0.le hijR hp.le
    · exact Real.rpow_le_rpow hl.le (by linarith [Real.log_le_log hi0 hijR]) (by linarith)
    · positivity
    · positivity
  have hE (M N y : ℕ) (hy : 0 < y) (hyN : y ≤ N) :
      |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
        (W / (1 - ε)) * (y : ℝ) ^ (1 - ε) +
        (B * (1 + 1 / (1 - ε)) + 2 * D) * (N : ℝ) /
          ((y : ℝ) ^ (1 - ε) * (6 + Real.log (y : ℝ)) ^ b) := by
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
    have ht := arithmeticCutoff_density_tail_profile_bound w C T htmono
      (fun t ht => by dsimp [T]; positivity) hT M y hy
    have ht' : |positiveArithmeticPrefix (fun k => w k / (k : ℝ)) M -
        ∑ k ∈ Finset.range (y + 1), arithmeticCutoffWeight w M k / (k : ℝ)| ≤
        (2 * D) / ((y : ℝ) ^ (1 - ε) * (6 + Real.log (y : ℝ)) ^ b) := by
      simpa only [T, mul_div_assoc] using ht
    have hwcut (t : ℕ) (ht : 0 < t) :
        |arithmeticCutoffWeight w M t| ≤ W * (t : ℝ) ^ (-ε) := by
      unfold arithmeticCutoffWeight
      split_ifs
      · exact hw t ht
      · simp only [abs_zero]; positivity
    rw [arithmeticFloorHilbertPartial_sequence_cutoff]
    apply arithmeticFloorPrefix_centered_hyperbola_critical_profile_bound
      (arithmeticCutoffWeight w M) (arithmeticCutoffWeight_zero w hw0 M) _
      hy hyN hW hB (Real.rpow_pos_of_pos (hlog y hy) b) hε.le (by linarith) hwcut _ ht'
    intro t hyt
    have ht0 : 0 < t := hy.trans_le hyt
    exact (hP M t ht0).trans (div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (hlog y hy) b)
      (Real.rpow_le_rpow (hlog y hy).le
        (by linarith [Real.log_le_log hy0 (show (y : ℝ) ≤ t by exact_mod_cast hyt)]) (by linarith)))
  obtain ⟨K, hK, hbound⟩ := eventual_sqrt_log_envelope_of_hyperbola_bound
    (fun M N => hilbertSequence (arithmeticFloorHilbertPartial w M) N)
    (1 - ε) b (W / (1 - ε)) (B * (1 + 1 / (1 - ε)) + 2 * D)
    (by linarith) (by linarith) hb (div_nonneg hW hp.le) (by positivity) hE
  have hlim (n : ℕ) : Tendsto (fun M => hilbertSequence (arithmeticFloorHilbertPartial w M) n)
      atTop (𝓝 (arithmeticFloorPrefix w n - (n : ℝ) * C)) := by
    have h := (tendsto_const_nhds (x := arithmeticFloorPrefix w n) (f := (atTop : Filter ℕ))).sub
      (hdensity.tendsto_sum_nat.const_mul (n : ℝ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    exact (arithmeticFloorHilbertPartial_sequence_of_le w M n hM).symm
  obtain ⟨f, hf, hconv⟩ := pareto_exists_tendsto_of_uniform_sqrt_log_bound
    (arithmeticFloorHilbertPartial w) (fun n => arithmeticFloorPrefix w n - (n : ℝ) * C)
    (by simp [arithmeticFloorPrefix]) hK (by linarith : 1 / 2 < b / 2) hlim hbound
  exact ⟨f, congrFun hf, hconv⟩

end RiemannResearch.RH.Pareto

noncomputable section
open Filter Set RiemannResearch.Analysis
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Critical prefix and density exponents suffice with any common
logarithmic saving greater than one. The shift is a free deterministic
parameter ensuring prefix monotonicity down to index one. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_critical_log_bounds
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε b c : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hb : 1 < b)
    (hc : 6 ≤ c) (hbc : b ≤ ε * c)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * (t : ℝ) ^ ε / (c + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (c + Real.log (t : ℝ)) ^ b)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n - (n : ℝ) * C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have hc0 : 0 < c := by linarith
  have hpmono : Monotone (fun t : ℕ => B * powerLogNatProfile ε b c t) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (powerLogNatProfile_monotone hc0 hε.le hbc hij) hB
  have hpall (t : ℕ) : |positiveArithmeticPrefix w t| ≤ B * powerLogNatProfile ε b c t := by
    by_cases ht : t = 0
    · simp [ht, powerLogNatProfile, positiveArithmeticPrefix_zero]
    · simpa only [powerLogNatProfile, if_neg ht, ← mul_div_assoc] using hP t (Nat.pos_of_ne_zero ht)
  have hlog (t : ℕ) (ht : 0 < t) : 0 < 6 + Real.log (t : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Real.log_nonneg ht1]
  apply arithmeticFloorHilbertPartial_tendsto_of_uniform_critical_log_bounds
    w hw0 C hdensity hW hB hD hε hεhalf hb hw
  · intro M t ht
    have hcut := arithmeticCutoff_prefix_profile_bound w _ hpmono hpall M t
    simp only [powerLogNatProfile, if_neg (Nat.ne_of_gt ht), ← mul_div_assoc] at hcut
    exact hcut.trans (div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (hlog t ht) b)
      (Real.rpow_le_rpow (hlog t ht).le (by linarith) (by linarith)))
  · intro t ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    apply (hT t ht).trans
    apply div_le_div_of_nonneg_left hD (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hlog t ht).le (by linarith) (by linarith))
      (Real.rpow_nonneg ht0.le _)

/-- Möbius specialization of the full critical logarithmic criterion.
The displayed signed estimates remain open at subhalf damping. -/
theorem dampedMobius_cutoffs_converge_of_critical_log_bounds
    {ε b c B D : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hb : 1 < b) (hc : 6 ≤ c) (hbc : b ≤ ε * c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix (dampedMobiusWeight ε) t| ≤
      B * (t : ℝ) ^ ε / (c + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |(1 / riemannZeta (1 + (ε : ℂ))).re -
        positiveArithmeticPrefix (fun k => dampedMobiusWeight ε k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (c + Real.log (t : ℝ)) ^ b)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  apply arithmeticFloorHilbertPartial_tendsto_of_critical_log_bounds
    (dampedMobiusWeight ε) (dampedMobiusWeight_zero ε) _ (dampedMobius_density_hasSum hε)
    (W := 1) (by norm_num) hB hD hε hεhalf hb hc hbc _ hP hT
  intro t ht
  rw [dampedMobiusWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t)))
    (Real.rpow_nonneg (Nat.cast_nonneg t) _)


/-- Independent critical prefix and density logarithms: their minimum,
and only their minimum, determines the admissible physical saving. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_critical_two_log_bounds
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε b e c : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hb : 1 < b) (he : 1 < e)
    (hc : 6 ≤ c) (hbc : min b e ≤ ε * c)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * (t : ℝ) ^ ε / (c + Real.log (t : ℝ)) ^ b)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / ((t : ℝ) ^ (1 - ε) * (c + Real.log (t : ℝ)) ^ e)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n - (n : ℝ) * C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have hlog (t : ℕ) (ht : 0 < t) : 1 ≤ c + Real.log (t : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith [Real.log_nonneg ht1]
  apply arithmeticFloorHilbertPartial_tendsto_of_critical_log_bounds
    w hw0 C hdensity hW hB hD hε hεhalf (lt_min hb he) hc hbc hw
  · intro t ht
    apply (hP t ht).trans
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (by linarith [hlog t ht]) _)
      (Real.rpow_le_rpow_of_exponent_le (hlog t ht) (min_le_left b e))
  · intro t ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    apply (hT t ht).trans
    apply div_le_div_of_nonneg_left hD (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hlog t ht) (min_le_right b e))
      (Real.rpow_nonneg ht0.le _)

end RiemannResearch.RH.Pareto

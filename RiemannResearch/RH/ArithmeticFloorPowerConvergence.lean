/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HyperbolaExponentOptimization
import RiemannResearch.RH.ArithmeticFloorHyperbolaPowerBounds
import RiemannResearch.RH.ArithmeticFloorTruncationBounds
import RiemannResearch.RH.ParetoDominatedConvergence
import RiemannResearch.RH.DampedMobiusSignedHeadClosure

/-!
# Arithmetic Hilbert convergence from strict prefix and tail exponents

This is a conditional research reduction when specialized to subhalf
Möbius damping. The prefix and density-tail estimates remain explicit
arithmetic hypotheses. The generic truncation, integer-cutoff optimization,
and full-tail dominated convergence are proved without such a provider.
-/

noncomputable section
open Filter Set RiemannResearch.Analysis
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The signed prefix and density power bounds survive arbitrary conductor
truncation and control the entire physical tail. -/
theorem arithmeticFloorHilbertPartial_uniform_power_hyperbola_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {W B D ε a d : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (ha : 0 ≤ a) (ha1 : a < 1) (hd : 0 ≤ d)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤ B * (t : ℝ) ^ a)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤ D * (t : ℝ) ^ (-d))
    (M N y : ℕ) (hy : 0 < y) (hyN : y ≤ N) :
    |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
      (W / (1 - ε)) * (y : ℝ) ^ (1 - ε) +
      (B * (1 + 1 / (1 - a))) * (N : ℝ) * (y : ℝ) ^ (a - 1) +
      (2 * D) * (N : ℝ) * (y : ℝ) ^ (-d) := by
  have hpmono : Monotone (fun t : ℕ => B * (t : ℝ) ^ a) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg i) (by exact_mod_cast hij) ha) hB
  have hpall (t : ℕ) : |positiveArithmeticPrefix w t| ≤ B * (t : ℝ) ^ a := by
    rcases t with _ | t
    · simp only [positiveArithmeticPrefix_zero, abs_zero]
      positivity
    · exact hP _ (by omega)
  have htmono : AntitoneOn (fun t : ℕ => D * (t : ℝ) ^ (-d)) (Set.Ici 1) := by
    intro i hi j hj hij
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < i by change 1 ≤ i at hi; omega))
        (by exact_mod_cast hij) (by linarith)) hD
  have ht := arithmeticCutoff_density_tail_profile_bound w C
    (fun t => D * (t : ℝ) ^ (-d)) htmono (fun t _ => by positivity) hT M y hy
  have hwcut (t : ℕ) (ht : 0 < t) :
      |arithmeticCutoffWeight w M t| ≤ W * (t : ℝ) ^ (-ε) := by
    unfold arithmeticCutoffWeight
    split_ifs
    · exact hw t ht
    · simp only [abs_zero]
      positivity
  rw [arithmeticFloorHilbertPartial_sequence_cutoff]
  apply arithmeticFloorPrefix_centered_hyperbola_power_bound
    (arithmeticCutoffWeight w M) (arithmeticCutoffWeight_zero w hw0 M) _
    hy hyN hW hB hε hε1 ha ha1 hwcut
  · intro t _
    exact arithmeticCutoff_prefix_profile_bound w _ hpmono hpall M t
  · simpa only [mul_assoc] using ht

/-- Pure-power convergence criterion in the difficult range. The exact
arithmetic inputs are a signed prefix exponent `a < ε` and a density-tail
decay exponent `d > 1-ε`. No energy bound is assumed. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_prefix_density_powers
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    {W B D ε a d : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (ha : 0 ≤ a) (haε : a < ε)
    (hd : 1 - ε < d)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W * (t : ℝ) ^ (-ε))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤ B * (t : ℝ) ^ a)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤ D * (t : ℝ) ^ (-d)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n - (n : ℝ) * C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  let p := 1 - ε
  let r := min (1 - a) d
  have hp : 1 / 2 ≤ p := by dsimp [p]; linarith
  have hr : p < r := lt_min (by dsimp [p]; linarith) hd
  have ha1 : a < 1 := by linarith
  have hd0 : 0 ≤ d := by linarith
  let A := W / (1 - ε)
  let B' := B * (1 + 1 / (1 - a)) + 2 * D
  have hA : 0 ≤ A := div_nonneg hW (by linarith)
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hE (M N y : ℕ) (hy : 0 < y) (hyN : y ≤ N) :
      |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
        A * (y : ℝ) ^ p + B' * (N : ℝ) * (y : ℝ) ^ (-r) := by
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hpa : (y : ℝ) ^ (a - 1) ≤ (y : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by dsimp [r]; linarith [min_le_left (1-a) d])
    have hpd : (y : ℝ) ^ (-d) ≤ (y : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by dsimp [r]; linarith [min_le_right (1-a) d])
    have hb := arithmeticFloorHilbertPartial_uniform_power_hyperbola_bound
      w hw0 C hW hB hD hε.le (by linarith) ha ha1 hd0 hw hP hT M N y hy hyN
    have h1 := mul_le_mul_of_nonneg_left hpa
      (show 0 ≤ B * (1 + 1 / (1 - a)) * (N : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hpd
      (show 0 ≤ (2 * D) * (N : ℝ) by positivity)
    dsimp [A, B', p]
    nlinarith
  obtain ⟨K, hK, hbound⟩ := eventual_power_envelope_of_hyperbola_bound
    (fun M N => hilbertSequence (arithmeticFloorHilbertPartial w M) N) p r A B'
    hp hr hA hB' hE
  have hbeta : p / (p + r) < 1 / 2 :=
    (balanced_hyperbola_power_lt_half_iff p r (by linarith)).mpr hr
  have hlim (n : ℕ) : Tendsto (fun M => hilbertSequence (arithmeticFloorHilbertPartial w M) n)
      atTop (𝓝 (arithmeticFloorPrefix w n - (n : ℝ) * C)) := by
    have h := (tendsto_const_nhds (x := arithmeticFloorPrefix w n) (f := (atTop : Filter ℕ))).sub
      (hdensity.tendsto_sum_nat.const_mul (n : ℝ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    exact (arithmeticFloorHilbertPartial_sequence_of_le w M n hM).symm
  obtain ⟨f, hf, hconv⟩ := pareto_exists_tendsto_of_uniform_rpow_bound
    (arithmeticFloorHilbertPartial w) (fun n => arithmeticFloorPrefix w n - (n : ℝ) * C)
    (by simp [arithmeticFloorPrefix]) hK hbeta hlim hbound
  exact ⟨f, congrFun hf, hconv⟩

/-- Möbius specialization. Both cancellation estimates below are OPEN
arithmetic hypotheses for every fixed positive damping below one half. -/
theorem dampedMobius_cutoffs_converge_of_prefix_density_powers
    {ε a d B D : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (haε : a < ε) (hd : 1 - ε < d) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hP : ∀ t : ℕ, 0 < t →
      |positiveArithmeticPrefix (dampedMobiusWeight ε) t| ≤ B * (t : ℝ) ^ a)
    (hT : ∀ t : ℕ, 0 < t →
      |(1 / riemannZeta (1 + (ε : ℂ))).re -
        positiveArithmeticPrefix (fun k => dampedMobiusWeight ε k / (k : ℝ)) t| ≤
        D * (t : ℝ) ^ (-d)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  apply arithmeticFloorHilbertPartial_tendsto_of_prefix_density_powers
    (dampedMobiusWeight ε) (dampedMobiusWeight_zero ε) _ (dampedMobius_density_hasSum hε)
    (W := 1) (by norm_num) hB hD hε hεhalf ha haε hd _ hP hT
  intro t ht
  rw [dampedMobiusWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t)))
    (Real.rpow_nonneg (Nat.cast_nonneg t) _)

end RiemannResearch.RH.Pareto

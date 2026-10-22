/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.HyperbolaLoglogStretchedCutoff
import RiemannResearch.RH.ArithmeticFloorTruncationBounds
import RiemannResearch.Analysis.WeightedMertensLoglogStretched

/-!
# Uniform arithmetic floor envelopes for the optimized profile

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

theorem arithmeticCutoff_prefix_loglog_stretched_bound
    (w : ℕ → ℝ) {B β d : ℝ} (hB : 0 ≤ B)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1 / 2) (hd : 0 ≤ d) (hd4 : d ≤ 1 / 8)
    (hp : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) * loglogStretchedProfile β d (t : ℝ))
    (M t : ℕ) (ht : 0 < t) :
    |positiveArithmeticPrefix (arithmeticCutoffWeight w M) t| ≤
      B * Real.sqrt (t : ℝ) * loglogStretchedProfile β d (t : ℝ) := by
  rw [positiveArithmeticPrefix_cutoff]
  by_cases hm : min M t = 0
  · simp only [hm, positiveArithmeticPrefix_zero, abs_zero]
    unfold loglogStretchedProfile
    positivity
  · have hmp : 0 < min M t := Nat.pos_of_ne_zero hm
    have hm1 : (1 : ℝ) ≤ min M t := by exact_mod_cast hmp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hmono := halfLoglogStretchedPrimitive_monotoneOn β d hβ hβ1 hd hd4
      hm1 ht1 (by exact_mod_cast min_le_right M t)
    simp only [halfLoglogStretchedPrimitive_eq_sqrt] at hmono
    have h := mul_le_mul_of_nonneg_left hmono hB
    exact (hp (min M t) hmp).trans (by simpa only [mul_assoc] using h)

theorem arithmeticFloorHilbertPartial_uniform_loglog_stretched_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ) {W B D β d : ℝ}
    (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hβ : 0 < β) (hβ1 : β ≤ 1 / 2) (hd : 0 < d) (hd4 : d ≤ 1 / 8)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W / Real.sqrt (t : ℝ))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) * loglogStretchedProfile β d (t : ℝ))
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun k => w k / (k : ℝ)) t| ≤
        D / Real.sqrt (t : ℝ) * loglogStretchedProfile β d (t : ℝ))
    (M n : ℕ) (hn : 0 < n) (hlarge : 10 ≤ Real.log (n : ℝ)) :
    |hilbertSequence (arithmeticFloorHilbertPartial w M) n| ≤
      (2 * W + 6 * B + 4 * D) * Real.sqrt (n : ℝ) *
        Real.exp (-(d / 8) * logProductPower β (6 + Real.log (n : ℝ))) := by
  let T : ℕ → ℝ := fun t => D / Real.sqrt (t : ℝ) * loglogStretchedProfile β d (t : ℝ)
  have htmono : AntitoneOn T (Set.Ici 1) := by
    intro i hi j hj hij
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by change 1 ≤ i at hi; omega)
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp [T]
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left hD (Real.sqrt_pos.mpr hi0) (Real.sqrt_le_sqrt hijR)
    · exact loglogStretchedProfile_antitone β d hβ.le hd.le hi1 hijR
    · unfold loglogStretchedProfile
      positivity
    · positivity
  have htcut (t : ℕ) (ht : 0 < t) :
      |positiveArithmeticPrefix (fun k => w k / (k : ℝ)) M -
        ∑ k ∈ Finset.range (t + 1), arithmeticCutoffWeight w M k / (k : ℝ)| ≤
        (2 * D) / Real.sqrt (t : ℝ) * Real.exp (-d * logProductPower β (6 + Real.log (t : ℝ))) := by
    have h := arithmeticCutoff_density_tail_profile_bound w C T htmono
      (fun t ht => by dsimp [T, loglogStretchedProfile]; positivity) hT M t ht
    simpa only [T, loglogStretchedProfile, stretchedLoglogCore, logProductPower,
      mul_div_assoc, mul_assoc] using h
  have hwcut (t : ℕ) (ht : 0 < t) :
      |arithmeticCutoffWeight w M t| ≤ W / Real.sqrt (t : ℝ) := by
    unfold arithmeticCutoffWeight
    split_ifs
    · exact hw t ht
    · simp only [abs_zero]
      positivity
  have hpcut (t : ℕ) (ht : 0 < t) :
      |positiveArithmeticPrefix (arithmeticCutoffWeight w M) t| ≤
        B * Real.sqrt (t : ℝ) * Real.exp (-d * logProductPower β (6 + Real.log (t : ℝ))) := by
    exact arithmeticCutoff_prefix_loglog_stretched_bound w hB hβ.le hβ1 hd.le hd4 hP M t ht
  rw [arithmeticFloorHilbertPartial_sequence_cutoff]
  have h := arithmeticFloorPrefix_loglog_stretched_bound
    (arithmeticCutoffWeight w M) (arithmeticCutoffWeight_zero w hw0 M)
    (positiveArithmeticPrefix (fun k => w k / (k : ℝ)) M)
    hW hB (show 0 ≤ 2 * D by positivity) hβ hβ1 hd (by linarith) hwcut hpcut htcut hn hlarge
  convert h using 1
  ring

end RiemannResearch.RH.Pareto

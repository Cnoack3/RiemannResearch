import RiemannResearch.RH.ProjectedDualProjectionError
import RiemannResearch.Analysis.MellinStepSeries
import RiemannResearch.RH.ParetoBoundedMellinLinearity
import Mathlib.Tactic.LinearCombination
/-!
# Small coefficient duals as nonzero Mellin witnesses

Source: independently derived finite-support calculations for the user's
coefficient-mass obstruction, 28 September 2026. The second and third duals
cannot both have zero Mellin integral anywhere in Re(s)>0. At a zeta zero,
every finite residue combination has zero Mellin integral; bounded linearity
therefore preserves the selected witness in its projection error.
No critical-zero existence theorem or RH hypothesis is imported.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.Analysis.Cesaro
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

private theorem coefficientRiesz_two_bounded :
    ∀ j, |hilbertSequence (coefficientRiesz 2) j| ≤ (6:ℝ) := by
  intro j
  by_cases hj : j ≤ 2
  · interval_cases j <;> rw [coefficientRiesz_sequence 2 _ (by decide)] <;>
      norm_num [dualCoeff, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · rw [coefficientRiesz_sequence_zero 2 j (by decide) (by omega)]
    norm_num

private theorem coefficientRiesz_three_bounded :
    ∀ j, |hilbertSequence (coefficientRiesz 3) j| ≤ (12:ℝ) := by
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j <;> rw [coefficientRiesz_sequence 3 _ (by decide)] <;>
      norm_num [dualCoeff, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  · rw [coefficientRiesz_sequence_zero 3 j (by decide) (by omega)]
    norm_num

theorem coefficientRiesz_two_three_bounded {d:ℕ} (hd:d=2 ∨ d=3) :
    ∀ j, |hilbertSequence (coefficientRiesz d) j| ≤ (12:ℝ) := by
  rcases hd with rfl | rfl
  · intro j
    exact (coefficientRiesz_two_bounded j).trans (by norm_num)
  · exact coefficientRiesz_three_bounded

theorem coefficientRiesz_two_mellin (s:ℂ) (hs:0<s.re) :
    s * paretoMellin (coefficientRiesz 2) s =
      4 - 10*(2:ℂ)^(-s) + 6*(3:ℂ)^(-s) := by
  have h := hasSum_first_mellin_pairing_of_bounded
    (coefficientRiesz 2) 6 coefficientRiesz_two_bounded s hs
  calc
    _ = ∑ k ∈ Finset.range 2, mellinFirst s (k+1) *
        (hilbertSequence (coefficientRiesz 2) (k+1):ℂ) := by
      rw [← h.tsum_eq]
      apply tsum_eq_sum
      intro k hk
      have hk' : 2 ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
      rw [coefficientRiesz_sequence_zero 2 (k+1) (by decide) (by omega)]
      simp
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        coefficientRiesz_sequence 2 _ (by decide)]
      norm_num [dualCoeff, mellinFirst,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      <;> ring

theorem coefficientRiesz_three_mellin (s:ℂ) (hs:0<s.re) :
    s * paretoMellin (coefficientRiesz 3) s =
      2 + 4*(2:ℂ)^(-s) - 18*(3:ℂ)^(-s) + 12*(4:ℂ)^(-s) := by
  have h := hasSum_first_mellin_pairing_of_bounded
    (coefficientRiesz 3) 12 coefficientRiesz_three_bounded s hs
  calc
    _ = ∑ k ∈ Finset.range 3, mellinFirst s (k+1) *
        (hilbertSequence (coefficientRiesz 3) (k+1):ℂ) := by
      rw [← h.tsum_eq]
      apply tsum_eq_sum
      intro k hk
      have hk' : 3 ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
      rw [coefficientRiesz_sequence_zero 3 (k+1) (by decide) (by omega)]
      simp
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        coefficientRiesz_sequence 3 _ (by decide)]
      norm_num [dualCoeff, mellinFirst,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      <;> ring

theorem coefficientRiesz_two_or_three_mellin_ne_zero (s:ℂ) (hs:0<s.re) :
    paretoMellin (coefficientRiesz 2) s ≠ 0 ∨
      paretoMellin (coefficientRiesz 3) s ≠ 0 := by
  by_contra h
  push Not at h
  let x : ℂ := (2:ℂ)^(-s)
  have hx : ‖x‖ < 1 := by
    calc
      ‖x‖ = (2:ℝ)^(-s.re) := by
        simpa [x] using Complex.norm_cpow_eq_rpow_re_of_pos
          (by norm_num : (0:ℝ)<2) (-s)
      _ < (2:ℝ)^(0:ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := by simp
  have hfour : (4:ℂ)^(-s) = x^2 := by
    dsimp [x]
    convert Complex.mul_cpow_ofReal_nonneg (a:=2) (b:=2)
      (by norm_num) (by norm_num) (-s) using 1 <;> norm_num [pow_two]
  have h2 := coefficientRiesz_two_mellin s hs
  have h3 := coefficientRiesz_three_mellin s hs
  rw [h.1, mul_zero] at h2
  rw [h.2, mul_zero, hfour] at h3
  change 0 = 4-10*x+6*(3:ℂ)^(-s) at h2
  change 0 = 2+4*x-18*(3:ℂ)^(-s)+12*x^2 at h3
  have hp : (6*x-7)*(x-1) = 0 := by
    linear_combination -(3/2:ℂ)*h2-(1/2:ℂ)*h3
  rcases mul_eq_zero.mp hp with hp | hp
  · have he : x = (7/6:ℂ) := by linear_combination hp/6
    rw [he] at hx
    norm_num at hx
  · have he : x = 1 := sub_eq_zero.mp hp
    rw [he, norm_one] at hx
    exact (lt_irrefl (1:ℝ)) hx

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
/-- Bounded Mellin linearity and the residue zeta identity annihilate every
finite legal combination at the displayed zeta zero. -/
theorem paretoMellin_eq_zero_of_mem_finiteSpace
    (n:ℕ) (f:ThresholdHilbert) (hf:f ∈ finiteSpace n) (s:ℂ)
    (hs:0<s.re) (hs1:s≠1) (hz:riemannZeta s=0) :
    paretoMellin f s=0 := by
  obtain ⟨a,ha⟩ := finiteSpace_expansion n f hf
  have hb (i:Fin n) : ∀ k, |hilbertSequence (a i • residueAtom i.val) k| ≤ |a i| := by
    intro k
    have hr : |hilbertSequence (residueAtom i.val) k| ≤ (1:ℝ) := by
      rw [residueAtom,normalizedResidueHilbert_sequence]
      unfold ArithmeticCumulative.residueFraction
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_one (by positivity : (0:ℝ)<((i.val+2:ℕ):ℝ))).mpr
      exact_mod_cast (Nat.le_of_lt (Nat.mod_lt k (by omega : 0 < i.val + 2)))
    change |hilbertSequenceLinear (a i • residueAtom i.val) k| ≤ _
    rw [map_smul]
    change |a i * hilbertSequence (residueAtom i.val) k| ≤ _
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg (a i))
  rw [ha,paretoMellin_fintype_sum_of_bounded _ (fun i=>⟨|a i|,hb i⟩) s hs]
  apply Finset.sum_eq_zero
  intro i hi
  have hs0 : s≠0 := by intro he; simp [he] at hs
  have h := normalizedResidue_mellin_zeta (i.val+2) (by omega) s hs hs1
  change s*paretoMellin (residueAtom i.val) s = _ at h
  rw [hz,mul_zero] at h
  have hzero := (mul_eq_zero.mp h).resolve_left hs0
  rw [paretoMellin_smul,hzero,smul_zero]

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
/-- Pointwise physical control by the actual absolute column mass. -/
theorem projectedDual_sequence_abs_le_mass (n d j : ℕ) :
    |hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) j| ≤
      projectedDualCoefficientMass n d := by
  obtain ⟨a,ha⟩ := finiteSpace_expansion n
    ((finiteSpace n).starProjection (coefficientRiesz d))
    ((finiteSpace n).starProjection_apply_mem _)
  have hc (i:Fin n) : coefficientCLM (i.val+2)
      ((finiteSpace n).starProjection (coefficientRiesz d)) = a i := by
    rw [ha,coefficient_finite_sum]
  have hmass : projectedDualCoefficientMass n d = ∑ i:Fin n, |a i| := by
    unfold projectedDualCoefficientMass
    simp only [hc]
  have hr (i:Fin n) : |hilbertSequence (residueAtom i.val) j| ≤ (1:ℝ) := by
    rw [residueAtom, normalizedResidueHilbert_sequence]
    unfold ArithmeticCumulative.residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity : (0:ℝ)<((i.val+2:ℕ):ℝ))).mpr
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt j (by omega : 0 < i.val + 2)))
  rw [hmass,ha]
  change |hilbertSequenceLinear (∑ i:Fin n, a i • residueAtom i.val) j| ≤ _
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  change |a i| * |hilbertSequence (residueAtom i.val) j| ≤ |a i|
  simpa using mul_le_mul_of_nonneg_left (hr i) (abs_nonneg (a i))

theorem projectedDualError_sequence_abs_le (n d : ℕ) (hd : d=2∨d=3) (j:ℕ) :
    |hilbertSequence (coefficientRiesz d -
      (finiteSpace n).starProjection (coefficientRiesz d)) j| ≤
        12 + projectedDualCoefficientMass n d := by
  have hh := coefficientRiesz_two_three_bounded hd j
  change |hilbertSequenceLinear (coefficientRiesz d -
    (finiteSpace n).starProjection (coefficientRiesz d)) j| ≤ _
  rw [map_sub]
  change |hilbertSequence (coefficientRiesz d) j -
    hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) j| ≤ _
  calc
    _ ≤ |hilbertSequence (coefficientRiesz d) j| +
        |hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) j| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (hilbertSequence (coefficientRiesz d) j) 0
        (hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) j)
    _ ≤ _ := add_le_add hh (projectedDual_sequence_abs_le_mass n d j)

theorem projectedDualError_mellin_at_zero (n d:ℕ) (hd:d=2∨d=3)
    (s:ℂ) (hs:0<s.re) (hs1:s≠1) (hz:riemannZeta s=0) :
    paretoMellin (coefficientRiesz d -
      (finiteSpace n).starProjection (coefficientRiesz d)) s =
        paretoMellin (coefficientRiesz d) s := by
  let p : ThresholdHilbert := (finiteSpace n).starProjection (coefficientRiesz d)
  have hh := coefficientRiesz_two_three_bounded hd
  have hn : ∀j, |hilbertSequence (-p) j| ≤ projectedDualCoefficientMass n d := by
    intro j
    change |hilbertSequenceLinear (-p) j| ≤ _
    rw [map_neg]
    change |-(hilbertSequence p j)| ≤ _
    simpa only [abs_neg] using projectedDual_sequence_abs_le_mass n d j
  have hmneg : paretoMellin (-p) s = -paretoMellin p s := by
    simpa only [neg_one_smul] using paretoMellin_smul (-1:ℝ) p s
  have hpzero : paretoMellin p s=0 :=
    paretoMellin_eq_zero_of_mem_finiteSpace n p
      ((finiteSpace n).starProjection_apply_mem _) s hs hs1 hz
  change paretoMellin (coefficientRiesz d - p) s = _
  rw [sub_eq_add_neg, paretoMellin_add_of_bounded _ _ hh hn s hs,
    hmneg,hpzero,neg_zero,add_zero]

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

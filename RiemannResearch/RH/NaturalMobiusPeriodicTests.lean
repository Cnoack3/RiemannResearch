import RiemannResearch.RH.NaturalMobiusPrimitiveTests
import RiemannResearch.Analysis.PeriodicHarmonicMean
import RiemannResearch.RH.ParetoCRTGramTransfer

/-!
# Centered periodic tests of the actual raw Möbius residual

Source: the Abel argument in `ReciprocalCharge_DilationAndPeriodicSource_20260924.md`,
Sections 7–8. The arithmetic variation estimate and PNT supply the hypotheses
of the bounded-primitive pairing theorem. The complete Gram-source limit is assembled in `NaturalMobiusSourceLimits`
using the separately proved logarithmic Möbius mean for the constant mode.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
open ArithmeticCumulative

/-- A centered periodic physical test has bounded positive-coordinate partial sums. -/
theorem rawMobiusResidual_inner_tendsto_of_periodic_zero_mean
    (f : ThresholdHilbert) (p : ℕ) (hp : 0 < p) (C : ℝ)
    (hperiod : ∀ k, hilbertSequence f (k + p + 1) = hilbertSequence f (k + 1))
    (hmean : (∑ k ∈ Finset.range p, hilbertSequence f (k + 1)) = 0)
    (hbound : ∀ k, |hilbertSequence f (k + 1)| ≤ C) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f) atTop (𝓝 0) := by
  apply rawMobiusResidual_inner_tendsto_of_bounded_partial_sums f ((p : ℝ) * C)
  intro K
  exact periodic_zero_sum_prefix_bound (fun k => hilbertSequence f (k + 1)) p hp
    (fun k => hperiod k) hmean C hbound K

private theorem centeredResidue_sum_positive_period (m : ℕ) :
    (∑ k ∈ Finset.range m, centeredResidue m (k + 1)) = 0 := by
  have hz : (∑ k ∈ Finset.range m, centeredResidue m k) = 0 := by
    have h := fin_real_centered_sum m
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (k : ℝ) - ((m : ℝ) - 1) / 2) m] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    simp only [centeredResidue, residue, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
  have he := Finset.sum_range_succ' (f := centeredResidue m) m
  rw [Finset.sum_range_succ, hz] at he
  have hm0 : centeredResidue m m = centeredResidue m 0 := by
    simp [centeredResidue, residue]
  rw [hm0] at he
  linarith

/-- The centered part of every actual residue Gram source tends to zero.
The constant source is retained explicitly, rather than assumed to vanish. -/
theorem rawMobiusResidual_centered_residue_inner_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N =>
      inner ℝ (hilbertOne - rawMobiusHilbert N) (normalizedResidueHilbert m hm) -
        (((m : ℝ) - 1) / (2 * (m : ℝ))) *
          inner ℝ (hilbertOne - rawMobiusHilbert N) hilbertOne) atTop (𝓝 0) := by
  let c : ℝ := ((m : ℝ) - 1) / (2 * (m : ℝ))
  let f : ThresholdHilbert := normalizedResidueHilbert m hm - c • hilbertOne
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hseq (k : ℕ) : hilbertSequence f (k + 1) = centeredResidue m (k + 1) / (m : ℝ) := by
    change hilbertSequenceLinear (_ - _) (k + 1) = _
    rw [map_sub, map_smul]
    change hilbertSequence (normalizedResidueHilbert m hm) (k + 1) -
      c * hilbertSequence hilbertOne (k + 1) = _
    rw [normalizedResidueHilbert_sequence, hilbertOne_sequence]
    simp only [zeroAnchor, Nat.add_one_ne_zero, if_false, mul_one]
    dsimp [c, centeredResidue, residueFraction, residue]
    field_simp [ne_of_gt hmR]
  have hperiod (k : ℕ) : hilbertSequence f (k + m + 1) = hilbertSequence f (k + 1) := by
    rw [hseq, hseq]
    have h := centeredResidue_period_of_dvd (dvd_refl m) (k + 1)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg
      (fun x : ℝ => x / (m : ℝ)) h
  have hmean : (∑ k ∈ Finset.range m, hilbertSequence f (k + 1)) = 0 := by
    simp_rw [hseq]
    rw [← Finset.sum_div, centeredResidue_sum_positive_period, zero_div]
  have hbound (k : ℕ) : |hilbertSequence f (k + 1)| ≤ 1 := by
    rw [hseq, abs_div, abs_of_pos hmR]
    apply (div_le_iff₀ hmR).mpr
    simpa only [one_mul] using centeredResidue_abs_le m (k + 1) hm
  have ht := rawMobiusResidual_inner_tendsto_of_periodic_zero_mean f m hm 1
    hperiod hmean hbound
  simpa only [f, c, inner_sub_right, inner_smul_right] using ht

end RiemannResearch.RH.Pareto

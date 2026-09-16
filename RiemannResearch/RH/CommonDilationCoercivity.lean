import RiemannResearch.RH.DyadicRegularizedNorm
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Coercivity of a common outward remainder dilation

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 11, especially Lemma 11.1.  This module proves its estimate on the
actual weighted Hilbert space. No sign condition on the scalar or the vector,
and no arithmetic approximation hypothesis, is used.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem positiveWeight_mul_nat_sq (n : ℕ) :
    positiveWeight n * (n : ℝ)^2 = (n : ℝ) / ((n : ℝ) + 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num [positiveWeight]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold positiveWeight
    field_simp
    <;> ring

/-- The full infinite Pareto norm of a remainder is at most `2 A`.
The proof retains the entire tail, whose exact mass is `1/A`. -/
theorem hilbertResidue_norm_sq_le_twice (A : ℕ) (hA : 0 < A) :
    ‖hilbertResidue A hA‖^2 ≤ 2 * (A : ℝ) := by
  have hs := hilbertSequence_square_summable (hilbertResidue A hA)
  simp only [hilbertResidue_sequence] at hs
  have hsplit := hs.sum_add_tsum_nat_add A
  have hhead : (∑ n ∈ Finset.range A,
      positiveWeight n * residue A n ^ 2) ≤ (A : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [show residue A n = (n : ℝ) from by
          simp [residue, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)],
          positiveWeight_mul_nat_sq]
        exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
      _ = _ := by simp
  have hw := (summable_nat_add_iff A).mpr positiveWeight_summable
  have ht := (summable_nat_add_iff A).mpr hs
  have htail : (∑' n : ℕ,
      positiveWeight (n + A) * residue A (n + A) ^ 2) ≤ (A : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, positiveWeight (n + A) * (A : ℝ)^2 := by
        apply ht.tsum_le_tsum _ (hw.mul_right _)
        intro n
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        have hb := residue_abs_le A (n + A) hA
        have hsq := (sq_le_sq₀ (abs_nonneg (residue A (n + A)))
          (Nat.cast_nonneg A)).mpr hb
        simpa only [sq_abs] using hsq
      _ = (1 / (A : ℝ)) * (A : ℝ)^2 := by
        rw [hw.tsum_mul_right, positiveWeight_tail_tsum A hA]
      _ = (A : ℝ) := by
        have hA0 : (A : ℝ) ≠ 0 := by positivity
        field_simp
  rw [hilbert_norm_weighted_sq, hilbertResidue_sequence]
  linarith

/-- Before its first dilation block the complete signed vector equals `q n`.
Its norm therefore controls the scalar charge even when every later block
has arbitrary cancellations. -/
theorem commonDilation_head_control (A : ℕ) (hA : 2 ≤ A)
    (f : ThresholdHilbert) (q : ℝ) :
    (A : ℝ) / 4 * q^2 ≤
      ‖hilbertDilation A (by omega) f + q • hilbertResidue A (by omega)‖^2 := by
  let C := hilbertDilation A (by omega) f + q • hilbertResidue A (by omega)
  have hcoord (n : ℕ) (hn : n < A) : hilbertSequence C n = q * (n : ℝ) := by
    dsimp [C]
    simp [hilbertSequence_add, hilbertSequence_smul, hilbertDilation_sequence,
      hilbertResidue_sequence, dilation, Nat.div_eq_of_lt hn,
      residue, Nat.mod_eq_of_lt hn]
  have hterm (n : ℕ) (hn : n ∈ Finset.Ico 1 A) :
      q^2 / 2 ≤ positiveWeight n * hilbertSequence C n ^ 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    rw [hcoord n (Finset.mem_Ico.mp hn).2, mul_pow]
    have he : positiveWeight n * (q^2 * (n : ℝ)^2) =
        q^2 * ((n : ℝ) / ((n : ℝ) + 1)) := by
      rw [← positiveWeight_mul_nat_sq]
      ring
    rw [he]
    have hr : (1 / 2 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
      apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg q)]
  have hsum : ((A - 1 : ℕ) : ℝ) * (q^2 / 2) ≤ ‖C‖^2 := by
    calc
      _ = ∑ _n ∈ Finset.Ico 1 A, q^2 / 2 := by simp
      _ ≤ ∑ n ∈ Finset.Ico 1 A,
          positiveWeight n * hilbertSequence C n ^ 2 :=
        Finset.sum_le_sum hterm
      _ ≤ ∑' n : ℕ, positiveWeight n * hilbertSequence C n ^ 2 :=
        Summable.sum_le_tsum _
          (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
          (hilbertSequence_square_summable C)
      _ = ‖C‖^2 := (hilbert_norm_weighted_sq C).symm
  have hAc : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hcast : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ A)]
    norm_num
  rw [hcast] at hsum
  have hnon := mul_nonneg (sub_nonneg.mpr hAc) (sq_nonneg q)
  change (A : ℝ) / 4 * q^2 ≤ ‖C‖^2
  nlinarith

/-- Lemma 11.1 for every vector of the actual Pareto Hilbert space.
The scalar boundary charge may have either sign. -/
theorem commonDilation_coercivity (A : ℕ) (hA : 2 ≤ A)
    (f : ThresholdHilbert) (q : ℝ) :
    (A : ℝ) / (1 + 2 * Real.sqrt 2)^2 * ‖f‖^2 ≤
      ‖hilbertDilation A (by omega) f + q • hilbertResidue A (by omega)‖^2 := by
  let D := hilbertDilation A (by omega) f
  let R := hilbertResidue A (by omega)
  let C := D + q • R
  have hhead : (A : ℝ) / 4 * q^2 ≤ ‖C‖^2 :=
    commonDilation_head_control A hA f q
  have hR : ‖R‖^2 ≤ 2 * (A : ℝ) := hilbertResidue_norm_sq_le_twice A (by omega)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : ‖q • R‖^2 ≤ 8 * ‖C‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hb := mul_le_mul_of_nonneg_left hR (sq_nonneg q)
    nlinarith
  have hqnorm : ‖q • R‖ ≤ (2 * Real.sqrt 2) * ‖C‖ := by
    have hnon : 0 ≤ (2 * Real.sqrt 2) * ‖C‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hnon).mp
    calc
      ‖q • R‖^2 ≤ 8 * ‖C‖^2 := hq
      _ = ((2 * Real.sqrt 2) * ‖C‖)^2 := by
        rw [mul_pow, mul_pow, hs2]
        ring
  have htri : ‖D‖ ≤ (1 + 2 * Real.sqrt 2) * ‖C‖ := by
    have he : D = C - q • R := by dsimp [C]; abel
    calc
      ‖D‖ = ‖C - q • R‖ := congrArg norm he
      _ ≤ ‖C‖ + ‖q • R‖ := norm_sub_le _ _
      _ ≤ (1 + 2 * Real.sqrt 2) * ‖C‖ := by nlinarith
  have hsq : ‖D‖^2 ≤ (1 + 2 * Real.sqrt 2)^2 * ‖C‖^2 := by
    have hnon : 0 ≤ (1 + 2 * Real.sqrt 2) * ‖C‖ := by positivity
    have hh := (sq_le_sq₀ (norm_nonneg D) hnon).mpr htri
    simpa only [mul_pow] using hh
  have hD : ‖D‖^2 = (A : ℝ) * ‖f‖^2 := hilbertDilation_norm_sq A (by omega) f
  rw [hD] at hsq
  have hden : 0 < (1 + 2 * Real.sqrt 2)^2 := by positivity
  change (A : ℝ) / (1 + 2 * Real.sqrt 2)^2 * ‖f‖^2 ≤ ‖C‖^2
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hden).mpr (by nlinarith [hsq])

end
end RiemannResearch.RH.Pareto

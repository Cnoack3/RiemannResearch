import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gap-energy and geometric-summability reductions

Source: user-provided continuation, Section 12.2. Short-gap mass and exceptional
large-gap mass control the cubic sum. The intended arithmetic providers are
Baker--Harman--Pintz (maximal gaps, DOI 10.1112/plms/83.3.532) and Jaerviniemi
(large-gap total mass, https://arxiv.org/abs/2212.10965). Their statements and
application to all prime powers are NOT formalized here: externalMaxGap,
externalTotalMass, externalLargeGapMass, and externalCubicGapSummability are
explicit hypotheses. Geometric-majorant summability and its full tail bound
are proved. None of these bounds the actual signed von Mangoldt discrepancy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.GapEnergy

/-- Cubic gap energy separates into a short-gap mass and a large-gap mass.
The total gap mass is deliberately not replaced by the cardinality. -/
theorem cubic_gap_sum_le {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    (H G : ℝ) (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hg : ∀ i ∈ S, 0 ≤ g i) (hgG : ∀ i ∈ S, g i ≤ G) :
    (∑ i ∈ S, g i ^ 3) ≤
      H ^ 2 * (∑ i ∈ S, g i) +
        G ^ 2 * (∑ i ∈ S.filter (fun i => H ≤ g i), g i) := by
  classical
  have hpoint (i : ι) (hi : i ∈ S) :
      g i ^ 3 ≤ H ^ 2 * g i + G ^ 2 * (if H ≤ g i then g i else 0) := by
    have hgi := hg i hi
    by_cases hlarge : H ≤ g i
    · simp only [if_pos hlarge]
      have hsq : g i ^ 2 ≤ G ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hgG i hi)) (add_nonneg hG hgi)]
      have hcube := mul_le_mul_of_nonneg_right hsq hgi
      have hshort := mul_nonneg (sq_nonneg H) hgi
      nlinarith
    · simp only [if_neg hlarge, mul_zero, add_zero]
      have hgiH : g i ≤ H := le_of_lt (lt_of_not_ge hlarge)
      have hsq : g i ^ 2 ≤ H ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hgiH) (add_nonneg hH hgi)]
      have hcube := mul_le_mul_of_nonneg_right hsq hgi
      nlinarith
  calc
    (∑ i ∈ S, g i ^ 3) ≤
        ∑ i ∈ S, (H ^ 2 * g i + G ^ 2 * (if H ≤ g i then g i else 0)) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_filter]

/-- Explicit named external-input reduction: maximal gaps plus exceptional
large-gap mass control the complete cubic gap sum. No prime-gap theorem is
silently assumed; all three arithmetic bounds are arguments. -/
theorem cubic_gap_sum_le_of_external_bounds {ι : Type*}
    (S : Finset ι) (g : ι → ℝ) (H G totalMass largeMass : ℝ)
    (hH : 0 ≤ H) (hG : 0 ≤ G)
    (hg : ∀ i ∈ S, 0 ≤ g i)
    (externalMaxGap : ∀ i ∈ S, g i ≤ G)
    (externalTotalMass : (∑ i ∈ S, g i) ≤ totalMass)
    (externalLargeGapMass :
      (∑ i ∈ S.filter (fun i => H ≤ g i), g i) ≤ largeMass) :
    (∑ i ∈ S, g i ^ 3) ≤ H ^ 2 * totalMass + G ^ 2 * largeMass := by
  exact (cubic_gap_sum_le S g H G hH hG hg externalMaxGap).trans
    (add_le_add (mul_le_mul_of_nonneg_left externalTotalMass (sq_nonneg H))
      (mul_le_mul_of_nonneg_left externalLargeGapMass (sq_nonneg G)))

/-- Geometric summability is a consequence of cubic-gap summability, not a
bound for the actual signed cumulative von Mangoldt discrepancy. -/
theorem summable_remainder_of_cubic_gap {ι : Type*} (R g q : ι → ℝ)
    (hR : ∀ i, 0 ≤ R i)
    (hupper : ∀ i, R i ≤ g i ^ 3 / (12 * q i ^ 2))
    (externalCubicGapSummability : Summable (fun i => g i ^ 3 / q i ^ 2)) :
    Summable R := by
  have he (i : ι) : g i ^ 3 / (12 * q i ^ 2) =
      (1 / 12 : ℝ) * (g i ^ 3 / q i ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hmajor : Summable (fun i => g i ^ 3 / (12 * q i ^ 2)) := by
    simpa only [he] using externalCubicGapSummability.mul_left (1 / 12 : ℝ)
  exact Summable.of_nonneg_of_le hR hupper hmajor

/-- A dyadic or other geometric majorant suffices for geometric-remainder
summability. Obtaining the majorant remains an explicit input. -/
theorem summable_of_geometric_majorant (R : ℕ → ℝ) (C r : ℝ)
    (hR : ∀ n, 0 ≤ R n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmajorant : ∀ n, R n ≤ C * r ^ n) :
    Summable R := by
  exact Summable.of_nonneg_of_le hR hmajorant
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)

/-- The complete tail is retained and inherits the exact geometric majorant. -/
theorem tail_tsum_le_of_geometric_majorant (R : ℕ → ℝ) (C r : ℝ)
    (hR : ∀ n, 0 ≤ R n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmajorant : ∀ n, R n ≤ C * r ^ n) (k : ℕ) :
    (∑' n, R (k + n)) ≤ C * r ^ k / (1 - r) := by
  have hb (n : ℕ) : R (k + n) ≤ (C * r ^ k) * r ^ n := by
    simpa only [pow_add, mul_assoc] using hmajorant (k + n)
  have hgs : Summable (fun n : ℕ => (C * r ^ k) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (C * r ^ k)
  have hrs : Summable (fun n : ℕ => R (k + n)) :=
    Summable.of_nonneg_of_le (fun n => hR (k + n)) hb hgs
  have hle := Summable.tsum_le_tsum hb hrs hgs
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
    using hle

end RiemannResearch.Analysis.GapEnergy

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QDivisorDPPSpectralTails
import RiemannResearch.RH.QDivisorDPPArithmeticWindows
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
/-!
# Global arithmetic overlap and uniform Q divisor-kernel estimates

Source: Section 7 of the user-provided moving-window research record,
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QDPPMovingWindowsResearch20261014.md
supports the statements. The proof here uses saturated finite divisor sums
and complete-basis Parseval to justify the infinite limit, without assuming
an auxiliary independent-prime law. Counting coordinate i is physical i+1.
The exact absolute overlap precedes both the kernel estimate and its gcd
corollary. Arbitrary finite diagonal tapers of absolute value at most one
obey the same overlap estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoProbability ZetaTwoHilbert QDivisorHilbert
theorem basisFeatures_absolute_arithmetic (i j r : ℕ) :
    |normalizedDivisorWavelet (basisIndex r) i * normalizedDivisorWavelet (basisIndex r) j| =
      Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
        absoluteOverlapAF (basisIndex i) (basisIndex j) (r + 1) := by
  rw [normalizedDivisorWavelet_coordinate, normalizedDivisorWavelet_coordinate]
  have hJ := qJordanTwo_pos (r + 1) (Nat.succ_pos r)
  have hi : (Real.sqrt (qJordanTwo (r + 1)))⁻¹ *
      (Real.sqrt (qJordanTwo (r + 1)))⁻¹ = (qJordanTwo (r + 1))⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt hJ.le]
  change |Real.sqrt (qWeight i) * (Real.sqrt (qJordanTwo (r + 1)))⁻¹ *
      qDivisorWavelet (r + 1) (i + 1) *
      (Real.sqrt (qWeight j) * (Real.sqrt (qJordanTwo (r + 1)))⁻¹ *
        qDivisorWavelet (r + 1) (j + 1))| = _
  calc
    _ = |Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
      (qDivisorWavelet (r + 1) (i + 1) * qDivisorWavelet (r + 1) (j + 1)) *
      ((Real.sqrt (qJordanTwo (r + 1)))⁻¹ * (Real.sqrt (qJordanTwo (r + 1)))⁻¹)| := by
        congr 1; ring
    _ = _ := by
      rw [hi]
      change |Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
          (qDivisorWavelet (r + 1) (i + 1) * qDivisorWavelet (r + 1) (j + 1)) *
          (qJordanTwo (r + 1))⁻¹| =
        Real.sqrt (qWeight i) * Real.sqrt (qWeight j) *
          (|qDivisorWavelet (r + 1) (i + 1) * qDivisorWavelet (r + 1) (j + 1)| / qJordanTwo (r + 1))
      simp only [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_pos hJ, div_eq_mul_inv ]
      ring

theorem absoluteOverlapAF_summable (n m : ℕ+) :
    Summable (absoluteOverlapAF n m) := by
  let i := (n : ℕ) - 1
  let j := (m : ℕ) - 1
  have hi : basisIndex i = n := Subtype.ext (Nat.sub_add_cancel n.pos)
  have hj : basisIndex j = m := Subtype.ext (Nat.sub_add_cancel m.pos)
  have hC : Real.sqrt (qWeight i) * Real.sqrt (qWeight j) ≠ 0 :=
    ne_of_gt (mul_pos (Real.sqrt_pos.mpr (qWeight_pos i))
      (Real.sqrt_pos.mpr (qWeight_pos j)))
  apply (summable_nat_add_iff 1).mp
  have h := (basisFeatures_summable i j).abs.div_const
    (Real.sqrt (qWeight i) * Real.sqrt (qWeight j))
  apply h.congr
  intro r
  rw [basisFeatures_absolute_arithmetic, hi, hj, mul_div_cancel_left₀ _ hC]

theorem absoluteOverlapAF_tsum_one :
    (∑' r : ℕ, absoluteOverlapAF 1 1 r) = zetaTwo := by
  have he (r : ℕ) : spectralMass 0 r = qWeight 0 * absoluteOverlapAF 1 1 (r + 1) := by
    rw [spectralMass_arithmetic]
    simp [absoluteOverlapAF, basisIndex, ← pow_two, mul_div_assoc]
  have h := spectralMass_tsum 0
  simp_rw [he] at h
  rw [tsum_mul_left] at h
  have hs := (absoluteOverlapAF_summable 1 1).sum_add_tsum_nat_add 1
  have hf0 : absoluteOverlapAF 1 1 0 = 0 := by simp [absoluteOverlapAF, qJordanTwo]
  simp only [Finset.sum_range_one, hf0, zero_add] at hs
  rw [hs] at h
  have hZ := ne_of_gt zetaTwo_pos
  unfold qWeight positiveQWeight at h
  norm_num at h
  field_simp [hZ] at h
  linarith

theorem divisor_sum_exhaustion (f : ℕ → ℝ) (hf : Summable f) (hf0 : f 0 = 0)
    (c : ℕ) (hc : c ≠ 0) :
    Tendsto (fun N => ∑ r ∈ (c * (N + 1).factorial).divisors, f r)
      atTop (𝓝 (∑' r, f r)) := by
  let s : ℕ → Finset ℕ := fun N => insert 0 (c * (N + 1).factorial).divisors
  have hs : Tendsto s atTop atTop := by
    apply tendsto_atTop.mpr
    intro T
    apply eventually_atTop.mpr
    refine ⟨T.sup id, ?_⟩
    intro N hN r hr
    by_cases hr0 : r = 0
    · subst r; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Nat.mem_divisors.mpr
      refine ⟨?_, mul_ne_zero hc (ne_of_gt (Nat.factorial_pos _))⟩
      exact (Nat.dvd_factorial (Nat.pos_of_ne_zero hr0)
        ((Finset.le_sup hr).trans (by omega : T.sup id ≤ N + 1))).trans
          (dvd_mul_left _ c)
  have h := hf.hasSum.comp hs
  simpa [Function.comp_def, s, Finset.sum_insert, hf0] using h

theorem absoluteOverlapAF_tsum (n m : ℕ+) :
    (∑' r : ℕ, absoluteOverlapAF n m r) =
      zetaTwo * (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 * overlapCorrection n m := by
  let c := ((n : ℕ) * (m : ℕ)) ^ 2
  have hc : c ≠ 0 := pow_ne_zero 2 (mul_ne_zero (ne_of_gt n.pos) (ne_of_gt m.pos))
  have hnm := divisor_sum_exhaustion (absoluteOverlapAF n m)
    (absoluteOverlapAF_summable n m) (by simp [absoluteOverlapAF, qJordanTwo]) c hc
  have h11 := divisor_sum_exhaustion (absoluteOverlapAF 1 1)
    (absoluteOverlapAF_summable 1 1) (by simp [absoluteOverlapAF, qJordanTwo]) c hc
  rw [absoluteOverlapAF_tsum_one] at h11
  have hscaled := h11.const_mul
    ((Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 * overlapCorrection n m)
  have he (N : ℕ) :
      (∑ r ∈ (c * (N + 1).factorial).divisors, absoluteOverlapAF n m r) =
        (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 * overlapCorrection n m *
          ∑ r ∈ (c * (N + 1).factorial).divisors, absoluteOverlapAF 1 1 r :=
    absoluteOverlapAF_divisor_ratio_of_square_dvd n m _
      (mul_ne_zero hc (ne_of_gt (Nat.factorial_pos _))) (dvd_mul_right _ _)
  simp_rw [← he] at hscaled
  have h := tendsto_nhds_unique hnm hscaled
  nlinarith [h]

theorem qWeight_sqrt_product (i j : ℕ) :
    Real.sqrt (qWeight i) * Real.sqrt (qWeight j) =
      1 / (zetaTwo * ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  have he (k : ℕ) : Real.sqrt (qWeight k) =
      1 / (Real.sqrt zetaTwo * ((k + 1 : ℕ) : ℝ)) := by
    unfold qWeight positiveQWeight
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one,
      Real.sqrt_mul zetaTwo_pos.le, Real.sqrt_sq (by positivity)]
  rw [he, he]
  have hs : Real.sqrt zetaTwo ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr zetaTwo_pos)
  have hZ := ne_of_gt zetaTwo_pos
  have hi : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hs, hZ, hi, hj]
  nlinarith [Real.sq_sqrt zetaTwo_pos.le]

theorem basisFeatures_absolute_tsum (i j : ℕ) :
    (∑' r : ℕ, |normalizedDivisorWavelet (basisIndex r) i *
      normalizedDivisorWavelet (basisIndex r) j|) =
      (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        overlapCorrection (basisIndex i) (basisIndex j) := by
  simp_rw [basisFeatures_absolute_arithmetic]
  rw [tsum_mul_left, qWeight_sqrt_product]
  have hs := (absoluteOverlapAF_summable (basisIndex i) (basisIndex j)).sum_add_tsum_nat_add 1
  have hf0 : absoluteOverlapAF (basisIndex i) (basisIndex j) 0 = 0 := by
    simp [absoluteOverlapAF, qJordanTwo]
  simp only [Finset.sum_range_one, hf0, zero_add] at hs
  rw [hs, absoluteOverlapAF_tsum]
  change 1 / (zetaTwo * ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
    (zetaTwo * (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 *
      overlapCorrection (basisIndex i) (basisIndex j)) = _
  field_simp [ne_of_gt zetaTwo_pos]

theorem wavelet_sum_abs_le_overlap (i j : ℕ) (S : Finset ℕ)
    (a : ℕ → ℝ) (ha : ∀ r ∈ S, |a r| ≤ 1) :
    |∑ r ∈ S, a r * (normalizedDivisorWavelet (basisIndex r) i *
      normalizedDivisorWavelet (basisIndex r) j)| ≤
      (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        overlapCorrection (basisIndex i) (basisIndex j) := by
  rw [← basisFeatures_absolute_tsum]
  calc
    _ ≤ ∑ r ∈ S, |a r * (normalizedDivisorWavelet (basisIndex r) i *
        normalizedDivisorWavelet (basisIndex r) j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, |normalizedDivisorWavelet (basisIndex r) i *
        normalizedDivisorWavelet (basisIndex r) j| := by
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ha r hr)
    _ ≤ _ := (basisFeatures_summable i j).abs.sum_le_tsum S (fun _ _ => abs_nonneg _)

theorem basisKernel_abs_le_overlap (N i j : ℕ) :
    |basisKernel N i j| ≤
      (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        overlapCorrection (basisIndex i) (basisIndex j) := by
  rw [basisKernel_eq_range_sum]
  simpa using wavelet_sum_abs_le_overlap i j (Finset.range N) (fun _ => 1)
    (fun _ _ => by norm_num)

theorem basisKernel_sq_le_gcd (N i j : ℕ) :
    basisKernel N i j ^ 2 ≤
      4 * (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  let g : ℝ := Nat.gcd (i + 1) (j + 1)
  let k : ℝ := ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)
  let F := overlapCorrection (basisIndex i) (basisIndex j)
  have hk : 0 < k := by dsimp [k]; positivity
  have hF : 0 ≤ F := overlapCorrection_nonneg _ _
  have hB : 0 ≤ g ^ 2 / k * F := mul_nonneg (div_nonneg (sq_nonneg _) hk.le) hF
  have hK := basisKernel_abs_le_overlap N i j
  change |basisKernel N i j| ≤ g ^ 2 / k * F at hK
  have hsq : basisKernel N i j ^ 2 ≤ (g ^ 2 / k * F) ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hK
  have hf : F ^ 2 * g ^ 2 ≤ 4 * k := by
    simpa [F, g, k, basisIndex, mul_assoc] using
      overlapCorrection_sq_mul_gcd_sq_le (basisIndex i) (basisIndex j)
  calc
    _ ≤ (g ^ 2 / k * F) ^ 2 := hsq
    _ = (F ^ 2 * g ^ 2) * g ^ 2 / k ^ 2 := by ring
    _ ≤ (4 * k) * g ^ 2 / k ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hf (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by change _ = 4 * g ^ 2 / k; field_simp [ne_of_gt hk]

theorem prime_inverse_product_tendsto :
    Tendsto (fun N : ℕ => ∏ p ∈ (N + 1).factorial.primeFactors,
      (((p : ℕ) : ℝ) ^ 2 / (((p : ℕ) : ℝ) ^ 2 - 1))) atTop (𝓝 zetaTwo) := by
  have h := divisor_sum_exhaustion (absoluteOverlapAF 1 1)
    (absoluteOverlapAF_summable 1 1) (by simp [absoluteOverlapAF, qJordanTwo]) 1 one_ne_zero
  simp only [one_mul, absoluteOverlapAF_tsum_one] at h
  have he (N : ℕ) : (∑ r ∈ (N + 1).factorial.divisors, absoluteOverlapAF 1 1 r) =
      ∏ p ∈ (N + 1).factorial.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    rw [absoluteOverlapAF_divisor_saturated 1 1 _ (ne_of_gt (Nat.factorial_pos _))]
    · apply Finset.prod_congr rfl
      intro p hp
      simpa [primeValuation] using localAbsoluteOverlap_self p 0 (Nat.prime_of_mem_primeFactors hp)
    · intro p hp
      have hne : (N + 1).factorial.factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
      simp [primeValuation]
      omega
  simpa only [he] using h


theorem basisFeatures_absolute_tsum_mismatch (i j : ℕ) :
    (∑' r : ℕ, |normalizedDivisorWavelet (basisIndex r) i *
      normalizedDivisorWavelet (basisIndex r) j|) =
      (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        ∏ p ∈ valuationMismatchPrimes (basisIndex i) (basisIndex j),
          2 * (1 - 1 / (p : ℝ) ^ 2) := by
  rw [basisFeatures_absolute_tsum, overlapCorrection_eq_prod_mismatch]

theorem basisKernel_abs_le_two_pow (N i j : ℕ) :
    |basisKernel N i j| ≤
      (Nat.gcd (i + 1) (j + 1) : ℝ) ^ 2 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
        (2 : ℝ) ^ (valuationMismatchPrimes (basisIndex i) (basisIndex j)).card := by
  exact (basisKernel_abs_le_overlap N i j).trans
    (mul_le_mul_of_nonneg_left (overlapCorrection_le_two_pow _ _)
      (div_nonneg (sq_nonneg _) (by positivity)))

theorem prime_product_tendsto :
    Tendsto (fun N : ℕ => Finset.prod (N + 1).factorial.primeFactors
      (fun p : ℕ => (1 : ℝ) - 1 / (p : ℝ) ^ 2)) atTop (𝓝 (1 / zetaTwo)) := by
  have ht := prime_inverse_product_tendsto.inv₀ (ne_of_gt zetaTwo_pos)
  have he (N : ℕ) :
      (Finset.prod (N + 1).factorial.primeFactors
        (fun p : ℕ => (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)))⁻¹ =
          Finset.prod (N + 1).factorial.primeFactors
            (fun p : ℕ => (1 : ℝ) - 1 / (p : ℝ) ^ 2) := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [inv_div]
    field_simp [hp0]
  simpa only [he, one_div] using ht

end RiemannResearch.RH.QDivisorDPP

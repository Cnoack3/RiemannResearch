/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.QAbsoluteChargeMass
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletBounds
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QPhysicalDifference
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Actual inverse-square Jordan rows of the physical first difference

Möbius inversion reconstructs each jump from the charges on its divisors.
The mass of a divisor event under Q is exactly its reciprocal square, so the
absolute charge estimate justifies changing the order of the two sums.
Source: Balazard, Proposition 9, https://doi.org/10.1007/978-3-030-61887-2_3
for charge summability, combined with the physical Jordan divisor basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiemannResearch.RH.QJordanChargeRows
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert
open Pareto QPhysicalDifference SquarefreeRadicalDifference

private theorem divisor_sum_wavelets (m : ℕ) :
    (∑ d ∈ m.divisors, divisorWavelet d) = (m : ℝ) ^ 2 • qDivisor m := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    change qSequenceLinear (∑ d ∈ m.divisors, divisorWavelet d) (n+1) =
      qSequenceLinear ((m : ℝ)^2 • qDivisor m) (n+1)
    rw [map_sum, map_smul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ d ∈ m.divisors, qSequence (divisorWavelet d) (n+1)) =
      (m : ℝ)^2 * qSequence (qDivisor m) (n+1)
    simp only [qSequence_divisorWavelet_succ, ← divisorWaveletAF_apply, sum_divisorWaveletAF,
      qSequence_qDivisor, positiveDivisor, Nat.succ_ne_zero, if_false]
    rfl

/-- A Jordan row integrates an indicator of divisibility to a single signed-packet weight. -/
theorem divisor_inner_wavelet (m : ℕ) (s : ℕ+) :
    inner ℝ (qDivisor m) (divisorWavelet (s : ℕ)) =
      if (s : ℕ) ∣ m then qJordanTwo (s : ℕ) / (m : ℝ)^2 else 0 := by
  by_cases hm : m = 0
  · subst m
    have he : qDivisor 0 = 0 := by
      apply qSequence_injective
      funext n
      rw [qSequence_qDivisor]
      have hz : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
      rw [hz]
      by_cases hn : n = 0 <;> simp [positiveDivisor, hn]
    simp [he]
  have hi := congrArg (fun z : QHilbert => inner ℝ z (divisorWavelet (s : ℕ)))
    (divisor_sum_wavelets m)
  simp only [sum_inner, real_inner_smul_left] at hi
  have hsum :
      (∑ t ∈ m.divisors, inner ℝ (divisorWavelet t) (divisorWavelet (s : ℕ))) =
      if (s : ℕ) ∣ m then qJordanTwo (s : ℕ) else 0 := by
    calc
      _ = ∑ t ∈ m.divisors, if (s : ℕ) = t then qJordanTwo (s : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        let u : ℕ+ := ⟨t, Nat.pos_of_mem_divisors ht⟩
        have h := divisorWavelet_inner u s
        by_cases hst : (s : ℕ) = t
        · subst t
          simpa using divisorWavelet_inner s s
        · have hus : u ≠ s := fun he => hst ((congrArg Subtype.val he).symm)
          rw [if_neg hus] at h
          have hu : (u : ℕ) = t := rfl
          rw [hu] at h
          rw [if_neg hst]
          exact h
      _ = _ := by simp [Nat.mem_divisors, hm]
  rw [hsum] at hi
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  split_ifs at hi ⊢ with hs
  · exact (eq_div_iff (pow_ne_zero _ hmR)).mpr (by linarith only [hi])
  · exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero _ hmR)

private theorem event_weights (m : ℕ) :
    HasSum (fun n => positiveQWeight n * positiveDivisor m n) (1/(m : ℝ)^2) := by
  by_cases hm : m = 0
  · subst m
    have he : (fun n => positiveQWeight n * positiveDivisor 0 n) = (fun _ : ℕ => 0) := by
      funext n
      by_cases hn : n = 0 <;> simp [positiveDivisor, hn]
    rw [he]
    simp
  have he := qOne_inner_qDivisor m (Nat.pos_of_ne_zero hm)
  rw [qInner_weighted] at he
  rw [← he]
  have hs := (qSequence_product_summable qOne (qDivisor m)).hasSum
  convert hs using 1
  funext n
  by_cases hn : n = 0 <;> simp [hn, qSequence_qOne, qOneSequence, qSequence_qDivisor, positiveDivisor]

/-- Signed coefficient in the unnormalized Jordan row. The formula holds
for every physical vector; specialization to the actual displacement requires
no assumption on RH or on the size of its first differences. -/
theorem difference_inner_wavelet (f : QHilbert) (s : ℕ+) :
    inner ℝ (differenceCLM f) (divisorWavelet (s : ℕ)) =
      qJordanTwo (s : ℕ) * ∑' m : ℕ, if (s : ℕ) ∣ m then
        mobiusDifference m (qSequence f) / (m : ℝ)^2 else 0 := by
  let b := fun m => mobiusDifference m (qSequence f)
  let y := divisorWavelet (s : ℕ)
  let J := qJordanTwo (s : ℕ)
  let v := fun (m n : ℕ) => positiveQWeight n * positiveDivisor m n
  let z := fun m n : ℕ => b m * v m n * qSequence y n
  let g := fun (p : ℕ × ℕ) => |b p.1| * v p.1 p.2 * J
  have hJ : 0 ≤ J := (qJordanTwo_pos (s : ℕ) s.pos).le
  have hv (m n : ℕ) : 0 ≤ v m n := by
    apply mul_nonneg (positiveQWeight_nonneg n)
    unfold positiveDivisor
    split_ifs <;> norm_num
  have hy (n : ℕ) : |qSequence y n| ≤ J := by
    cases n with
    | zero => simpa using hJ
    | succ n =>
      change |qSequence (divisorWavelet (s : ℕ)) (n+1)| ≤ qJordanTwo (s : ℕ)
      rw [qSequence_divisorWavelet_succ]
      let k : ℕ+ := ⟨n+1, by omega⟩
      have hk : (k : ℕ) = n+1 := rfl
      have hc := qDivisorWavelet_abs_le_jordan (s : ℕ) s.pos.ne' k
      rw [hk] at hc
      exact hc
  have hrow (m : ℕ) : HasSum (fun n => g (m,n)) (|b m| * (1/(m : ℝ)^2) * J) :=
    ((event_weights m).mul_left _).mul_right _
  have hg : Summable g := by
    apply (summable_prod_of_nonneg (f := g) (fun p => mul_nonneg
      (mul_nonneg (abs_nonneg _) (hv _ _)) hJ)).mpr
    refine ⟨fun m => (hrow m).summable, ?_⟩
    simp only [(hrow _).tsum_eq]
    apply ((qSequence_mobiusDifference_absolute_mass f).mul_right J).congr
    intro n
    dsimp [b]
    ring
  have hz : Summable (Function.uncurry z) := by
    apply Summable.of_norm_bounded hg
    intro p
    change ‖b p.1 * v p.1 p.2 * qSequence y p.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hv _ _)]
    exact mul_le_mul_of_nonneg_left (hy _) (mul_nonneg (abs_nonneg _) (hv _ _))
  have hcol (n : ℕ) : (∑' m, z m n) =
      positiveQWeight n * qSequence (differenceCLM f) n * qSequence y n := by
    by_cases hn : n = 0
    · subst n
      simp [z, v, positiveDivisor]
    have hn' := Nat.pos_of_ne_zero hn
    rw [tsum_eq_sum (s := n.divisors) (by
      intro m hm
      have hdiv : ¬m ∣ n := fun hd => hm (Nat.mem_divisors.mpr ⟨hd,hn⟩)
      simp [z, v, positiveDivisor, hn, hdiv])]
    rw [qSequence_differenceCLM, qDifference, ← sum_mobiusDifference (qSequence f) n hn',
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    have hd := (Nat.mem_divisors.mp hm).1
    simp only [z, v, b, positiveDivisor, if_neg hn, if_pos hd, mul_one]
    ring
  have hterm (m : ℕ) : (∑' n, z m n) = b m * inner ℝ (qDivisor m) y := by
    rw [qInner_weighted, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [z, v, qSequence_qDivisor]
    ring
  rw [qInner_weighted, ← tsum_mul_left]
  change (∑' n, positiveQWeight n * qSequence (differenceCLM f) n * qSequence y n) = _
  calc
    _ = ∑' n, ∑' m, z m n := tsum_congr (fun n => (hcol n).symm)
    _ = ∑' m, ∑' n, z m n := hz.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro m
      rw [hterm]
      dsimp only [y, b]
      rw [divisor_inner_wavelet]
      split_ifs <;> ring

/-- Explicit coefficient in the complete, normalized arithmetic basis. -/
theorem difference_inner_normalized_wavelet (f : QHilbert) (s : ℕ+) :
    inner ℝ (differenceCLM f) (normalizedDivisorWavelet s) =
      Real.sqrt (qJordanTwo (s : ℕ)) * ∑' m : ℕ, if (s : ℕ) ∣ m then
        mobiusDifference m (qSequence f) / (m : ℝ)^2 else 0 := by
  rw [normalizedDivisorWavelet, inner_smul_right, difference_inner_wavelet]
  have hpos := qJordanTwo_pos (s : ℕ) s.pos
  have hs := Real.sq_sqrt hpos.le
  have hne := (Real.sqrt_pos.mpr hpos).ne'
  rw [← mul_assoc]
  congr 1
  field_simp [hne] <;> nlinarith only [hs]

/-- The complete Q energy of the physical difference, with the signed charge
packet kept inside its square at every conductor. -/
theorem difference_charge_parseval (f : QHilbert) :
    (∑' s : ℕ+, qJordanTwo (s : ℕ) * (∑' m : ℕ, if (s : ℕ) ∣ m then
      mobiusDifference m (qSequence f) / (m : ℝ)^2 else 0)^2) = ‖differenceCLM f‖^2 := by
  rw [← divisorWavelet_parseval_norm]
  apply tsum_congr
  intro s
  rw [difference_inner_wavelet]
  have h := (qJordanTwo_pos (s : ℕ) s.pos).ne'
  field_simp [h]

/-- Every inverse-square packet at a nonsquarefree conductor vanishes for the
actual projected displacement. -/
theorem displacement_packet_eq_zero_of_not_squarefree (s : ℕ+)
    (hs : ¬Squarefree (s : ℕ)) :
    (∑' m : ℕ, if (s : ℕ) ∣ m then
      mobiusDifference m (qSequence QSquarefreeDisplacementRigidity.displacement) /
        (m : ℝ)^2 else 0) = 0 := by
  have hz (m : ℕ) : (if (s : ℕ) ∣ m then
      mobiusDifference m (qSequence QSquarefreeDisplacementRigidity.displacement) /
        (m : ℝ)^2 else 0) = 0 := by
    by_cases hd : (s : ℕ) ∣ m
    · rw [if_pos hd]
      by_cases hm : m = 0
      · simp [hm]
      have hn : ¬Squarefree m := fun h => hs (h.squarefree_of_dvd hd)
      have hm1 : m ≠ 1 := by
        rintro rfl
        exact hn squarefree_one
      have hm2 : 2 ≤ m := by omega
      rw [QSquarefreeCompatibleHeads.nonsquarefree_charge_zero
        (qSequence QSquarefreeDisplacementRigidity.displacement) m
        (fun n hn' _ => QSquarefreeDisplacementRegularity.displacement_difference_radical n hn')
        m hm2 le_rfl hn, zero_div]
    · rw [if_neg hd]
  simp_rw [hz]
  simp

/-- Parseval on the actual displacement is supported on all squarefree conductors,
with no bound on their number of prime factors. -/
theorem displacement_squarefree_charge_parseval :
    (∑' s : ℕ+, if Squarefree (s : ℕ) then qJordanTwo (s : ℕ) *
      (∑' m : ℕ, if (s : ℕ) ∣ m then
        mobiusDifference m (qSequence QSquarefreeDisplacementRigidity.displacement) /
          (m : ℝ)^2 else 0)^2 else 0) =
      ‖differenceCLM QSquarefreeDisplacementRigidity.displacement‖^2 := by
  rw [← difference_charge_parseval]
  apply tsum_congr
  intro s
  by_cases hs : Squarefree (s : ℕ)
  · rw [if_pos hs]
  · rw [if_neg hs, displacement_packet_eq_zero_of_not_squarefree s hs]
    ring

end RiemannResearch.RH.QJordanChargeRows

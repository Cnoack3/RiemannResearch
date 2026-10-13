import RiemannResearch.RH.QFloorDilation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Escape of the undamped floor-dilation zeta series

Source: the user's prime convolution proposal, 13 October 2026.
The finite operators here are the integer coefficient truncations
`sum_{1 <= d <= N} T_d` of the formal Euler-zeta operator. No identification
with a finite product over primes is asserted. Their exact action on one
is `min N n`, and their operator norms are unbounded. Consequently finite
closure preservation cannot justify the undamped infinite operator passage.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFloorZetaEscape
open ZetaTwoHilbert ZetaTwoProbability QFloorDilation

/-- Integer coefficient truncation of the formal floor-dilation zeta series. -/
def zetaPartial (N : ℕ) : QHilbert →L[ℝ] QHilbert :=
  ∑ d ∈ Finset.range N, floorDilation (d + 1) (Nat.succ_pos d)

theorem floorDilation_qOne_sequence (m : ℕ) (hm : 0 < m) (n : ℕ) :
    qSequence (floorDilation m hm qOne) n = if m ≤ n then 1 else 0 := by
  rw [floorDilation_sequence, qSequence_qOne]
  by_cases hmn : m ≤ n
  · have hd : 0 < n / m := Nat.div_pos hmn hm
    simp [qOneSequence, ne_of_gt hd, hmn]
  · simp [qOneSequence, Nat.div_eq_of_lt (lt_of_not_ge hmn), hmn]

theorem zetaPartial_succ (N : ℕ) :
    zetaPartial (N + 1) = zetaPartial N + floorDilation (N + 1) (Nat.succ_pos N) := by
  simp only [zetaPartial, Finset.sum_range_succ]

/-- The formal Euler-zeta coefficients have a completely explicit physical action. -/
theorem zetaPartial_qOne_sequence (N n : ℕ) :
    qSequence (zetaPartial N qOne) n = (min N n : ℕ) := by
  induction N with
  | zero =>
      change qSequenceLinear (0 : QHilbert) n = ((min 0 n : ℕ) : ℝ)
      rw [map_zero]
      simp
  | succ N ih =>
      rw [zetaPartial_succ, ContinuousLinearMap.add_apply]
      change qSequenceLinear (zetaPartial N qOne +
        floorDilation (N + 1) (Nat.succ_pos N) qOne) n = _
      rw [map_add]
      change qSequence (zetaPartial N qOne) n +
        qSequence (floorDilation (N + 1) (Nat.succ_pos N) qOne) n = _
      rw [ih, floorDilation_qOne_sequence]
      by_cases hn : N < n
      · rw [min_eq_left (Nat.le_of_lt hn),
          min_eq_left (show N + 1 ≤ n by omega), if_pos (by omega)]
        push_cast
        ring
      · rw [min_eq_right (show n ≤ N by omega),
          min_eq_right (show n ≤ N + 1 by omega), if_neg (by omega)]
        simp

/-- The exact initial-coordinate contribution; every remaining summand is nonnegative. -/
theorem zetaPartial_qOne_head_energy (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      positiveQWeight n * (qSequence (zetaPartial N qOne) n) ^ 2) =
        (N : ℝ) / zetaTwo := by
  calc
    (∑ n ∈ Finset.Icc 1 N,
      positiveQWeight n * (qSequence (zetaPartial N qOne) n) ^ 2) =
        ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) / zetaTwo := by
      apply Finset.sum_congr rfl
      intro n hn
      have hbounds := Finset.mem_Icc.mp hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      rw [zetaPartial_qOne_sequence, min_eq_right hbounds.2]
      unfold positiveQWeight
      field_simp [hn0, ne_of_gt zetaTwo_pos]
    _ = (N : ℝ) / zetaTwo := by
      simp [Nat.card_Icc, nsmul_eq_mul, div_eq_mul_inv]

/-- Exact full energy, retaining every tail coordinate. The complement
contains zero as well; its Q weight is zero. -/
theorem zetaPartial_qOne_norm_sq_eq (N : ℕ) :
    ‖zetaPartial N qOne‖ ^ 2 = (N : ℝ) / zetaTwo +
      ∑' n : {n : ℕ // n ∉ Finset.Icc 1 N},
        positiveQWeight n.val * (N : ℝ) ^ 2 := by
  have hs := (qSequence_square_summable (zetaPartial N qOne)).sum_add_tsum_compl
    (s := Finset.Icc 1 N)
  rw [zetaPartial_qOne_head_energy] at hs
  rw [qNorm_weighted_sq, ← hs]
  congr 1
  apply tsum_congr
  intro n
  rw [zetaPartial_qOne_sequence]
  by_cases hn0 : n.val = 0
  · simp [hn0, positiveQWeight]
  · have hn : N < n.val := by
      have hnot : ¬ (1 ≤ n.val ∧ n.val ≤ N) := by
        simpa only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc] using n.property
      omega
    rw [min_eq_left hn.le]

theorem zetaPartial_qOne_tail_nonneg (N : ℕ) :
    0 ≤ ∑' n : {n : ℕ // n ∉ Finset.Icc 1 N},
      positiveQWeight n.val * (N : ℝ) ^ 2 :=
  tsum_nonneg (fun n => mul_nonneg (positiveQWeight_nonneg n.val) (sq_nonneg _))

/-- An unconditional lower bound in the complete Q norm. -/
theorem zetaPartial_qOne_norm_sq_ge (N : ℕ) :
    (N : ℝ) / zetaTwo ≤ ‖zetaPartial N qOne‖ ^ 2 := by
  rw [qNorm_weighted_sq]
  rw [← zetaPartial_qOne_head_energy N]
  exact Summable.sum_le_tsum (Finset.Icc 1 N)
    (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    (qSequence_square_summable (zetaPartial N qOne))

theorem zetaPartial_opNorm_sq_ge (N : ℕ) :
    (N : ℝ) / zetaTwo ≤ ‖zetaPartial N‖ ^ 2 := by
  have hn : ‖zetaPartial N qOne‖ ≤ ‖zetaPartial N‖ := by
    simpa only [qOne_norm, mul_one] using (zetaPartial N).le_opNorm qOne
  exact le_trans (zetaPartial_qOne_norm_sq_ge N)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)

/-- The undamped operator series cannot have uniformly bounded truncations. -/
theorem zetaPartial_opNorm_unbounded (B : ℝ) :
    ∃ N : ℕ, B < ‖zetaPartial N‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (zetaTwo * (max B 0) ^ 2)
  refine ⟨N, ?_⟩
  have hZ := zetaTwo_pos
  have hlarge : (max B 0) ^ 2 < (N : ℝ) / zetaTwo := by
    apply (lt_div_iff₀ hZ).mpr
    simpa only [mul_comm] using hN
  have hsq : (max B 0) ^ 2 < ‖zetaPartial N‖ ^ 2 :=
    lt_of_lt_of_le hlarge (zetaPartial_opNorm_sq_ge N)
  have hm : max B 0 < ‖zetaPartial N‖ :=
    (sq_lt_sq₀ (le_max_right B 0) (norm_nonneg _)).mp hsq
  exact lt_of_le_of_lt (le_max_left B 0) hm

/-- Despite this escape, every finite truncation preserves the legal closure. -/
theorem zetaPartial_mem_legalClosure (N : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) :
    zetaPartial N f ∈ QFullResidueProjection.closure := by
  unfold zetaPartial
  rw [ContinuousLinearMap.sum_apply]
  apply QFullResidueProjection.closure.sum_mem
  intro d hd
  exact floorDilation_mem_legalClosure (d + 1) (Nat.succ_pos d) f hf

theorem zetaPartial_qResidue_two_sequence (N n : ℕ) :
    qSequence (zetaPartial N (qResidue 2)) n =
      ∑ d ∈ Finset.range N, ArithmeticCumulative.residueFraction 2 (n / (d + 1)) := by
  unfold zetaPartial
  rw [ContinuousLinearMap.sum_apply]
  change qSequenceLinear (∑ d ∈ Finset.range N,
    floorDilation (d + 1) (Nat.succ_pos d) (qResidue 2)) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  change qSequence (floorDilation (d + 1) (Nat.succ_pos d) (qResidue 2)) n = _
  rw [floorDilation_sequence, qSequence_qResidue]

/-- Escape is already visible on the legal atom g₂: the upper half of the
floor-dilation indices each contributes exactly one half. -/
theorem zetaPartial_qResidue_two_head_lower (N n : ℕ) (hnN : n ≤ N) :
    (n : ℝ) / 4 ≤ qSequence (zetaPartial N (qResidue 2)) n := by
  rw [zetaPartial_qResidue_two_sequence]
  have hs : Finset.Ico (n / 2) n ⊆ Finset.range N := by
    intro d hd
    have hd' := Finset.mem_Ico.mp hd
    exact Finset.mem_range.mpr (by omega)
  have hhalf : (∑ d ∈ Finset.Ico (n / 2) n,
      ArithmeticCumulative.residueFraction 2 (n / (d + 1))) =
        ((n - n / 2 : ℕ) : ℝ) / 2 := by
    calc
      (∑ d ∈ Finset.Ico (n / 2) n,
        ArithmeticCumulative.residueFraction 2 (n / (d + 1))) =
          ∑ _d ∈ Finset.Ico (n / 2) n, (1 : ℝ) / 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd' := Finset.mem_Ico.mp hd
        have hdiv : n / (d + 1) = 1 := by
          apply Nat.div_eq_of_lt_le <;> omega
        norm_num [hdiv, ArithmeticCumulative.residueFraction]
      _ = ((n - n / 2 : ℕ) : ℝ) / 2 := by
        simp [Nat.card_Ico, nsmul_eq_mul, div_eq_mul_inv]
  have hcount : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (n - n / 2) by omega)
  calc
    (n : ℝ) / 4 ≤ ((n - n / 2 : ℕ) : ℝ) / 2 := by linarith
    _ = ∑ d ∈ Finset.Ico (n / 2) n,
        ArithmeticCumulative.residueFraction 2 (n / (d + 1)) := hhalf.symm
    _ ≤ ∑ d ∈ Finset.range N,
        ArithmeticCumulative.residueFraction 2 (n / (d + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro d hd hnot
      unfold ArithmeticCumulative.residueFraction
      positivity

/-- Complete Q energy grows linearly even when the input is a fixed legal atom. -/
theorem zetaPartial_qResidue_two_norm_sq_ge (N : ℕ) :
    (N : ℝ) / (16 * zetaTwo) ≤ ‖zetaPartial N (qResidue 2)‖ ^ 2 := by
  have hZ := zetaTwo_pos
  calc
    (N : ℝ) / (16 * zetaTwo) =
        ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) / (16 * zetaTwo) := by
      simp [Nat.card_Icc, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        positiveQWeight n * (qSequence (zetaPartial N (qResidue 2)) n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := Finset.mem_Icc.mp hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hl := zetaPartial_qResidue_two_head_lower N n hb.2
      calc
        (1 : ℝ) / (16 * zetaTwo) = positiveQWeight n * ((n : ℝ) / 4) ^ 2 := by
          unfold positiveQWeight
          field_simp [hn0, ne_of_gt hZ]
          <;> ring
        _ ≤ positiveQWeight n * (qSequence (zetaPartial N (qResidue 2)) n) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
          exact (sq_le_sq₀ (by positivity) (le_trans (by positivity) hl)).mpr hl
    _ ≤ ‖zetaPartial N (qResidue 2)‖ ^ 2 := by
      rw [qNorm_weighted_sq]
      exact Summable.sum_le_tsum (Finset.Icc 1 N)
        (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
        (qSequence_square_summable (zetaPartial N (qResidue 2)))

theorem zetaPartial_qResidue_two_unbounded (B : ℝ) :
    ∃ N : ℕ, B < ‖zetaPartial N (qResidue 2)‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((16 * zetaTwo) * (max B 0) ^ 2)
  refine ⟨N, ?_⟩
  have hZ : 0 < 16 * zetaTwo := mul_pos (by norm_num) zetaTwo_pos
  have hlarge : (max B 0) ^ 2 < (N : ℝ) / (16 * zetaTwo) := by
    apply (lt_div_iff₀ hZ).mpr
    simpa only [mul_comm] using hN
  have hsq : (max B 0) ^ 2 < ‖zetaPartial N (qResidue 2)‖ ^ 2 :=
    lt_of_lt_of_le hlarge (zetaPartial_qResidue_two_norm_sq_ge N)
  have hm : max B 0 < ‖zetaPartial N (qResidue 2)‖ :=
    (sq_lt_sq₀ (le_max_right B 0) (norm_nonneg _)).mp hsq
  exact lt_of_le_of_lt (le_max_left B 0) hm

end RiemannResearch.RH.QFloorZetaEscape

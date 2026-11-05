import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The conductor-two comparison vector
Twice the first squarefree atom matches the target on every odd positive site.
Even positive sites have complete Q mass 1/4. This halves the a priori
residual norm bound without introducing a fitted or truncated Gram matrix. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage ArithmeticCumulative

/-- The exact error of the legal conductor-two trial vector. -/
theorem qOne_sub_twice_residue_two_norm_sq :
    ‖qOne - (2 : ℝ) • qResidue 2‖^2 = 1/4 := by
  let x := qOne - (2 : ℝ) • qResidue 2
  let f := fun n : ℕ => positiveQWeight n * (qSequence x n)^2
  have hx (n : ℕ) : qSequence x n = qOneSequence n - 2 * residueFraction 2 n := by
    change qSequenceLinear (qOne - (2 : ℝ) • qResidue 2) n = _
    rw [map_sub, map_smul]
    change qSequence qOne n - 2 * qSequence (qResidue 2) n = _
    rw [qSequence_qOne, qSequence_qResidue]
  have hfe (k : ℕ) : f (2*k) = positiveQWeight k / 4 := by
    by_cases hk : k = 0
    · simp [hk, f, positiveQWeight]
    · have hne : 2*k ≠ 0 := by omega
      have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk
      have hm : (2*k) % 2 = 0 := by omega
      dsimp only [f]
      rw [hx]
      simp only [qOneSequence, if_neg hne, residueFraction, hm, Nat.cast_zero,
        zero_div, mul_zero, sub_zero, one_pow, mul_one, positiveQWeight, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [hk', zetaTwo_pos.ne']
      <;> ring
  have hfo (k : ℕ) : f (2*k+1) = 0 := by
    dsimp only [f]
    rw [hx]
    have hm : (2*k+1) % 2 = 1 := by omega
    simp [qOneSequence, residueFraction, hm, show 2*k+1 ≠ 0 by omega]
  have he : Summable (fun k : ℕ => f (2*k)) :=
    (positiveQWeight_summable.div_const 4).congr (fun k => (hfe k).symm)
  have ho : Summable (fun k : ℕ => f (2*k+1)) := by simp only [hfo]; exact summable_zero
  change ‖x‖^2 = _
  rw [qNorm_weighted_sq]
  change (∑' k : ℕ, f k) = _
  rw [← tsum_even_add_odd he ho]
  simp only [hfe, hfo, tsum_zero, add_zero, tsum_div_const, positiveQWeight_tsum]

/-- Uniform improvement from ‖r‖ ≤ 1 for the infinite legal space. -/
theorem limitingResidual_norm_le_half_parity : ‖limitingResidual‖ ≤ 1/2 := by
  let K := Submodule.span ℝ (Set.range squarefreeAtom)
  have hfirst : qResidue 2 ∈ K := by
    apply Submodule.subset_span
    refine ⟨0, ?_⟩
    simp [squarefreeAtom, Nat.prime_two.squarefree]
  have hc : (2 : ℝ) • qResidue 2 ∈ closure :=
    closure.smul_mem _ (K.le_topologicalClosure hfirst)
  have hmin : ‖limitingResidual‖ ≤ ‖qOne - (2 : ℝ) • qResidue 2‖ := by
    unfold limitingResidual
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩
      (⟨(2 : ℝ) • qResidue 2, hc⟩ : closure)
  have he := qOne_sub_twice_residue_two_norm_sq
  nlinarith [norm_nonneg (qOne - (2 : ℝ) • qResidue 2)]

theorem displacement_sq_le_one_div_thirty_two : ‖displacement‖^2 ≤ 1/32 := by
  have hr := limitingResidual_norm_le_half_parity
  have hd := displacement_energy_bound
  nlinarith [mul_nonneg (sub_nonneg.mpr hr)
    (add_nonneg (norm_nonneg limitingResidual) (by norm_num : (0:ℝ) ≤ 1/2))]

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

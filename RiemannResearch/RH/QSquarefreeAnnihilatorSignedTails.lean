/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeSieveDerivativeApproximation
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.ParetoRamanujanSquarefreeAnnihilator
import RiemannResearch.Analysis.SummableDiscreteAbel
import RiemannResearch.RH.ThresholdLegalIntegrability

/-!
# Summable signed tails of squarefree annihilators

Test against the finite factorial Möbius sieves. Their primitives are bounded
at each individual cutoff, and their differences are bounded by one uniformly
in the cutoff. Discrete summation by parts transfers those differences to the
summable signed tail.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert

private def mobiusSieve (Y : ℕ) : QHilbert :=
  -(∑ d ∈ Y.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue d)

private theorem mobiusSieve_mem (Y : ℕ) :
    mobiusSieve Y ∈ ZetaTwoOptimizerStage.closure := by
  apply ZetaTwoOptimizerStage.closure.neg_mem
  apply ZetaTwoOptimizerStage.closure.sum_mem
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  by_cases hs : Squarefree d
  · by_cases h1 : d = 1
    · simp [h1]
    · exact ZetaTwoOptimizerStage.closure.smul_mem _
        (ParetoRamanujanSquarefreeAnnihilator.qResidue_mem_squarefreeClosure (by omega) hs)
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

private theorem mobiusSieve_coordinate (Y n : ℕ) :
    qSequence (mobiusSieve Y) n = Pareto.derivativeSievePrimitive Y n := by
  change qSequenceLinear (-(∑ d ∈ Y.factorial.divisors,
    (ArithmeticFunction.moebius d : ℝ) • qResidue d)) n = _
  simp only [map_neg, map_sum, map_smul, Pi.neg_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change -(∑ d ∈ Y.factorial.divisors,
    (ArithmeticFunction.moebius d : ℝ) * qSequence (qResidue d) n) = _
  simp only [qSequence_qResidue, Pareto.derivativeSievePrimitive,
    Pareto.sieveResidue, one_mul]

/-- Summability of the signed tails suffices for zero mean under squarefree orthogonality. -/
theorem mean_zero_of_summable_signedTail (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) (hs : Summable (anchoredTail u)) :
    inner ℝ qOne u = 0 := by
  classical
  let J (Y n : ℕ) : ℝ :=
    (if Nat.gcd Y.factorial n = 1 then 1 else 0) - Pareto.sieveReciprocal Y.factorial
  have hsum (Y : ℕ) : (∑' n, anchoredTail u n * J Y n) = 0 := by
    have ho := Submodule.inner_right_of_mem_orthogonal (mobiusSieve_mem Y) hu
    obtain ⟨C, hC⟩ := Pareto.legalSeedSpan_bounded ArithmeticCumulative.allPositiveSeeds
      (fun _ h => h) (Pareto.derivativeSievePrimitive_mem_legal Y)
    have hparts := Analysis.summable_discrete_summation_by_parts hs
      (show anchoredTail u 0 = 0 by simp [anchoredTail]) hC
    calc
      _ = ∑' n, anchoredTail u n *
          (Pareto.derivativeSievePrimitive Y n - Pareto.derivativeSievePrimitive Y (n - 1)) := by
        apply tsum_congr
        intro n
        cases n with
        | zero => simp [anchoredTail]
        | succ n =>
          exact congrArg (fun x : ℝ => anchoredTail u (n + 1) * x)
            (Pareto.derivativeSievePrimitive_difference_succ Y n).symm
      _ = ∑' n, (anchoredTail u n - anchoredTail u (n+1)) *
          Pareto.derivativeSievePrimitive Y n := hparts.symm
      _ = inner ℝ (mobiusSieve Y) u := by
        rw [qInner_weighted]
        apply tsum_congr
        intro n
        cases n with
        | zero => simp
        | succ n =>
          rw [anchoredTail_difference u (n+1) (Nat.succ_pos n), mobiusSieve_coordinate]
          unfold signedCoefficient
          ring
      _ = 0 := ho
  have hpt (n : ℕ) : Tendsto (fun Y : ℕ => anchoredTail u n * J Y n)
      atTop (𝓝 (if n = 1 then anchoredTail u 1 else 0)) := by
    by_cases hn : n = 0
    · subst n
      simp [anchoredTail]
    have hmask : ∀ᶠ Y : ℕ in atTop, Nat.gcd Y.factorial n = n := by
      filter_upwards [eventually_ge_atTop n] with Y hY
      exact Nat.gcd_eq_right (Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hY)
    have hJ : Tendsto (fun Y => J Y n) atTop (𝓝 (if n = 1 then (1 : ℝ) else 0)) := by
      have ht : Tendsto
          (fun Y : ℕ => (if n = 1 then (1 : ℝ) else 0) - Pareto.sieveReciprocal Y.factorial)
          atTop (𝓝 (if n = 1 then (1 : ℝ) else 0)) := by
        simpa only [sub_zero] using
          ((tendsto_const_nhds (x := (if n = 1 then (1 : ℝ) else 0))).sub
            Pareto.factorialSieveReciprocal_tendsto_zero)
      exact ht.congr' (hmask.mono (fun Y hY => by simp [J, hY]))
    have ht := hJ.const_mul (anchoredTail u n)
    by_cases h1 : n = 1 <;> simpa [h1] using ht
  have hlim := tendsto_tsum_of_dominated_convergence hs.norm
    (f := fun Y n : ℕ => anchoredTail u n * J Y n)
    (g := fun n : ℕ => if n = 1 then anchoredTail u 1 else 0)
    hpt
    (Eventually.of_forall (fun Y n => by
      have h0 := (Pareto.sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)).le
      have h1 := Pareto.sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
      have hJ : |J Y n| ≤ 1 := by
        dsimp [J]
        split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
      simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left hJ (abs_nonneg (anchoredTail u n))))
  have h1 : anchoredTail u 1 = 0 := by
    have hzero : Tendsto (fun Y => ∑' n, anchoredTail u n * J Y n) atTop (𝓝 0) := by
      simpa only [hsum] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  calc
    inner ℝ qOne u = anchoredTail u 1 := by
      rw [qInner_weighted, anchoredTail, if_neg one_ne_zero, signedTail_eq_tsum_sub_sum]
      have hc0 : signedCoefficient u 0 = 0 := by simp [signedCoefficient]
      rw [Finset.sum_range_one, hc0, sub_zero]
      apply tsum_congr
      intro n
      by_cases hn : n = 0 <;> simp [hn, signedCoefficient, qOneSequence]
    _ = 0 := h1

end RiemannResearch.RH.QSignedTailRigidity

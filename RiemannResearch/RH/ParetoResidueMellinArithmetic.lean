import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.RH.NymanConductorContinuation
import RiemannResearch.RH.ParetoSequenceCertificates
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Actual residue Mellin integrals on the arithmetic convergence half-plane

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §9.
Mathlib's `LSeries_eq_mul_integral` supplies the Abel-summation integral;
the partial coefficient sums below are proved to be the actual residues.
No arithmetic transform identity is a hypothesis.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open MeasureTheory Filter Set Asymptotics
noncomputable section

theorem nymanConductorBeta_residue_difference (a k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    nymanConductorBeta a k = (residue a k - residue a (k - 1)) / (a : ℝ) := by
  rw [nymanConductorBeta_apply (ne_of_gt hk), residue_difference a k hk]
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  split_ifs <;> field_simp <;> ring

theorem nymanConductorBeta_partial_sum (a n : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.Icc 1 n, (nymanConductorBeta a k : ℂ)) =
      ((residue a n / (a : ℝ) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [residue]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih,
      nymanConductorBeta_residue_difference a (n + 1) ha (by omega)]
    simp only [Nat.add_sub_cancel, Complex.ofReal_div, Complex.ofReal_sub]
    ring

theorem nymanConductorBeta_partial_sum_bigO (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (nymanConductorBeta a k : ℂ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
  refine Asymptotics.isBigO_iff.2 ⟨1, Filter.Eventually.of_forall (fun n => ?_)⟩
  rw [nymanConductorBeta_partial_sum a n ha]
  simp only [Real.rpow_zero, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ residue a n / (a : ℝ) := by
    unfold residue
    positivity
  rw [abs_of_nonneg hnonneg]
  apply (div_le_one (by positivity : (0 : ℝ) < a)).2
  exact (le_abs_self _).trans (residue_abs_le a n ha)

/-- Exact identification before analytic continuation; all inputs are concrete. -/
theorem paretoMellin_residue_arithmetic (a : ℕ) [NeZero a]
    (s : ℂ) (hs : 1 < s.re) :
    s * paretoMellin (digitHilbert a 1 (NeZero.pos a) (by omega)) s =
      (a : ℂ) * nymanConductorLFunction a s := by
  have ha : 0 < a := NeZero.pos a
  have hi := LSeries_eq_mul_integral
    (fun k : ℕ => (nymanConductorBeta a k : ℂ))
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) < s.re by linarith)
    (lSeriesSummable_nymanConductorBeta a hs) (nymanConductorBeta_partial_sum_bigO a ha)
  have hint :
      (∫ x in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        (nymanConductorBeta a k : ℂ)) * (x : ℂ) ^ (-(s + 1))) =
        (1 / (a : ℂ)) * paretoMellin (digitHilbert a 1 ha (by omega)) s := by
    rw [paretoMellin_eq_step_integral, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [nymanConductorBeta_partial_sum a ⌊x⌋₊ ha, hilbertSequence_digitHilbert]
    simp only [Complex.ofReal_div, digitSequence, Nat.div_one]
    have he : -(s + 1) = -s - 1 := by ring
    rw [he]
    simp only [residue]
    push_cast
    ring
  rw [hint, ← nymanConductorLFunction_eq_LSeries a hs] at hi
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  calc
    _ = (a : ℂ) * (s * ((1 / (a : ℂ)) *
        paretoMellin (digitHilbert a 1 ha (by omega)) s)) := by field_simp
    _ = _ := by rw [← hi]

end
end RiemannResearch.RH.Pareto

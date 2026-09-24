import RiemannResearch.RH.ParetoResidualShell
import RiemannResearch.RH.ParetoTailAverages

/-!
# Finite arithmetic cancellation constraints on Pareto tail averages

Source: user-provided `RH_Research_Agenda_2026-09-24(1).md`, Priority 3,
for the requested connection between arithmetic orthogonality and tails.
The exact finite Abel identity here is a direct derivation, using the existing
arithmetic identity `residue_difference`; no claim of novelty is made.

The combined finite sum is retained. The two component infinite sums need not
converge separately. No Noor regularity or residual-tail upper bound is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Abel summation with the genuine residue jump, including its exact boundary. -/
theorem tailAverage_residue_abel (f : ThresholdHilbert) (m : ℕ) (hm : 0 < m)
    (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 / (m : ℝ) - if m ∣ n + 1 then 1 else 0) *
        (tailAverage f n / ((n : ℝ) + 1))) =
      hilbertShellPairing f (normalizedResidueHilbert m hm) 0 N +
        residueFraction m N * (tailAverage f N / ((N : ℝ) + 1)) := by
  let B : ℕ → ℝ := fun n => inner ℝ f hilbertOne -
    ∑ k ∈ Finset.range n, paretoWeight k * hilbertGibbsPhysical f k
  have hB (n : ℕ) : tailAverage f n / ((n : ℝ) + 1) = B n := by
    dsimp [tailAverage, B]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  have hstep (n : ℕ) : B (n + 1) =
      B n - paretoWeight n * hilbertGibbsPhysical f n := by
    dsimp [B]
    rw [Finset.sum_range_succ]
    ring
  have hdiff (n : ℕ) : residueFraction m (n + 1) - residueFraction m n =
      1 / (m : ℝ) - if m ∣ n + 1 then 1 else 0 := by
    have hd := residue_difference m (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hd
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    unfold residueFraction
    unfold residue at hd
    split_ifs at hd ⊢ with hdiv
    · field_simp [hm0]
      nlinarith [hd]
    · field_simp [hm0]
      nlinarith [hd]
  have hfinite : ∀ K : ℕ,
      (∑ n ∈ Finset.range K,
        (1 / (m : ℝ) - if m ∣ n + 1 then 1 else 0) * B n) =
      (∑ n ∈ Finset.range K,
        paretoWeight n * hilbertGibbsPhysical f n * residueFraction m (n + 1)) +
        residueFraction m K * B K := by
    intro K
    induction K with
    | zero => simp [residueFraction]
    | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hstep, ← hdiff]
      ring
  have hhead : hilbertShellPairing f (normalizedResidueHilbert m hm) 0 N =
      ∑ n ∈ Finset.range N,
        paretoWeight n * hilbertGibbsPhysical f n * residueFraction m (n + 1) := by
    rw [hilbertShellPairing_weighted]
    simp only [Nat.add_zero, positiveWeight_succ, normalizedResidueHilbert_sequence,
      hilbertGibbsPhysical_eq, mul_assoc]
  simp_rw [hB]
  rw [hhead]
  exact hfinite N

namespace CoefficientStabilization

/-- At complete periods the boundary vanishes. Actual residual orthogonality
identifies the finite harmonic-dilation discrepancy with the signed full tail. -/
theorem residual_tailAverage_period_discrepancy (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hperiod : m ∣ N) :
    (∑ n ∈ Finset.range N,
      (1 / (m : ℝ) - if m ∣ n + 1 then 1 else 0) *
        (tailAverage limitResidual n / ((n : ℝ) + 1))) =
      -inner ℝ (hilbertTailShift limitResidual N)
        (hilbertTailShift (normalizedResidueHilbert m hm) N) := by
  rw [tailAverage_residue_abel limitResidual m hm N]
  have hz : residueFraction m N = 0 := by
    simp [residueFraction, Nat.mod_eq_zero_of_dvd hperiod]
  rw [hz, zero_mul, add_zero]
  exact residual_legal_head_tail_observation
    ((Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (normalizedResidue_mem_atomSpan m hm)) N

end CoefficientStabilization
end RiemannResearch.RH.Pareto

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMeanSquareDisplacement
import RiemannResearch.RH.QPolylogBlockEnergy

/-!
A local form of the averaging criterion of FourCriteriaContinuation20261105.md.
On each dyadic scale one may choose an approximant separately and allow a
fixed polylogarithmic loss in both its mean square and its Hilbert error.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QMeanSquareDisplacement
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open QSquarefreeDisplacementRigidity QPolylogTailEnergy
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

theorem riemannHypothesis_of_polylog_dyadic_displacement
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ,
      (∑ i ∈ Finset.range (2 ^ j), qSequence displacement (2 ^ j + i + 1) ^ 2) ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  let k := 2 * m + 2
  have hs := weightedEnergy_summable_of_dyadic_meanSquare displacement m C hC hb
  apply QSquarefreeLogDisplacement.riemannHypothesis_of_frequent_log_displacement_tail k
  refine ⟨((k : ℝ) + 6) ^ k * (∑' n : ℕ, polylogWeightedEnergyTerm k displacement n),
    (Eventually.of_forall ?_).frequently⟩
  intro N
  change logWeight k N * ‖tail N displacement‖ ^ 2 ≤ _
  calc
    _ ≤ (((k : ℝ) + 6) ^ k * polylogTailProfile k N) * ‖tail N displacement‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (logWeight_le_polylogTailProfile k N) (sq_nonneg _)
    _ = ((k : ℝ) + 6) ^ k * (polylogTailProfile k N * ‖tail N displacement‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (profile_mul_tail_energy_le k N displacement hs)
      (pow_nonneg (by positivity : 0 ≤ (k : ℝ) + 6) k)

/-- Each dyadic scale may use its own approximant. Both budgets may grow
by any fixed power of its logarithm. -/
theorem riemannHypothesis_of_local_polylog_mean_square
    (m : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ j : ℕ, ∃ u : QHilbert,
      headEnergy (2 ^ j + 2 ^ j) u ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m) ∧
      ((2 ^ j : ℕ) : ℝ) * ‖displacement - u‖ ^ 2 ≤
        D * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  have hz := zetaTwo_pos
  apply riemannHypothesis_of_polylog_dyadic_displacement m (2 * C + 8 * zetaTwo * D)
    (by positivity)
  intro j
  obtain ⟨u, hu, he⟩ := h j
  let N : ℕ := 2 ^ j
  let L : ℝ := (6 + Real.log (N : ℝ)) ^ (2 * m)
  change headEnergy (N + N) u ≤ C * (N : ℝ) * L at hu
  change (N : ℝ) * ‖displacement - u‖ ^ 2 ≤ D * L at he
  have hsum : (∑ i ∈ Finset.range N, qSequence displacement (N + i + 1) ^ 2) ≤
      headEnergy (N + N) displacement := by
    unfold headEnergy
    rw [Finset.sum_range_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h1 := headEnergy_add_error_le (N + N) displacement u
  have h2 := headEnergy_norm_le (N + N) (displacement - u)
  rw [Nat.cast_add] at h2
  have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ zetaTwo * (N : ℝ) by positivity)
  change _ ≤ (2 * C + 8 * zetaTwo * D) * (N : ℝ) * L
  change (∑ i ∈ Finset.range N, qSequence displacement (N + i + 1) ^ 2) ≤ _
  nlinarith


/-- A common polylogarithmic mean budget on a covering sequence of heads
suffices. The actual physical head for the test at stage j is H j. -/
theorem riemannHypothesis_of_covered_polylog_head_means
    (H : ℕ → ℕ) (u : ℕ → QHilbert) (K C D : ℝ) (m : ℕ)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcover : ∀ N, 1 ≤ N → ∃ j, N ≤ H j ∧ (H j : ℝ) ≤ K * (N : ℝ))
    (hu : ∀ j, headEnergy (H j) (u j) ≤
      C * (H j : ℝ) * (6 + Real.log (H j : ℝ)) ^ (2 * m))
    (he : ∀ j, (H j : ℝ) * ‖displacement - u j‖ ^ 2 ≤ D) :
    RiemannHypothesis := by
  let A : ℝ := 1 + Real.log (2 * K)
  have hK' : 0 < 2 * K := by linarith
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith [Real.log_nonneg (show 1 ≤ 2 * K by linarith)]
  have hA' : 0 ≤ A := by linarith
  apply riemannHypothesis_of_local_polylog_mean_square m
    (C * (2 * K) * A ^ (2 * m)) D (by positivity) hD
  intro i
  let N : ℕ := 2 ^ i
  have hpos : 0 < N := by dsimp [N]; positivity
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨j, hLo, hHi⟩ := hcover (N + N) (by omega)
  have hNR : (0 : ℝ) < N := by positivity
  have hHr : (0 : ℝ) < H j := by exact_mod_cast (show 0 < H j by omega)
  have hhn : (H j : ℝ) ≤ (2 * K) * N := by
    rw [Nat.cast_add] at hHi
    linarith
  let L : ℝ := 6 + Real.log (N : ℝ)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hn]
  have hL0 : 0 ≤ L := by linarith
  have hLH : 0 ≤ 6 + Real.log (H j : ℝ) := by
    have hx : (1 : ℝ) ≤ H j := by exact_mod_cast (show 1 ≤ H j by omega)
    linarith [Real.log_nonneg hx]
  have hlogs : 6 + Real.log (H j : ℝ) ≤ A * L := by
    have hh := Real.log_le_log hHr hhn
    rw [Real.log_mul hK'.ne' hNR.ne'] at hh
    have hprod := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hL)
    dsimp [A, L] at *
    nlinarith
  have hp := pow_le_pow_left₀ hLH hlogs (2 * m)
  rw [mul_pow] at hp
  refine ⟨u j, ?_, ?_⟩
  · have hbudget := hu j
    have hbound := mul_le_mul
      (mul_le_mul_of_nonneg_left hhn hC) hp (pow_nonneg hLH _)
      (show 0 ≤ C * ((2 * K) * (N : ℝ)) by positivity)
    change headEnergy (N + N) (u j) ≤ (C * (2 * K) * A ^ (2 * m)) * (N : ℝ) * L ^ (2 * m)
    calc
      _ ≤ headEnergy (H j) (u j) := headEnergy_mono (u j) hLo
      _ ≤ _ := hbudget.trans hbound
      _ = _ := by ring
  · have hnm : (N : ℝ) ≤ H j := by exact_mod_cast (show N ≤ H j by omega)
    change (N : ℝ) * ‖displacement - u j‖ ^ 2 ≤ D * L ^ (2 * m)
    calc
      _ ≤ (H j : ℝ) * ‖displacement - u j‖ ^ 2 := mul_le_mul_of_nonneg_right hnm (sq_nonneg _)
      _ ≤ D := he j
      _ ≤ _ := le_mul_of_one_le_right hD (one_le_pow₀ hL)

/-- At each dyadic scale test only its new annulus, with an independent
approximant and a fixed polylogarithmic allowance in both budgets. -/
theorem riemannHypothesis_of_local_annular_polylog_means
    (m : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ j : ℕ, let N : ℕ := 2 ^ j; let L := (6 + Real.log (N : ℝ)) ^ (2 * m)
      ∃ u : QHilbert, headEnergy (N + N) u - headEnergy N u ≤ C * (N : ℝ) * L ∧
        (N : ℝ) * ‖displacement - u‖ ^ 2 ≤ D * L) : RiemannHypothesis := by
  have hz := zetaTwo_pos
  apply riemannHypothesis_of_polylog_dyadic_displacement m (2 * C + 8 * zetaTwo * D)
    (by positivity)
  intro j
  let N : ℕ := 2 ^ j
  let L : ℝ := (6 + Real.log (N : ℝ)) ^ (2 * m)
  obtain ⟨u, hu, he⟩ := h j
  change headEnergy (N + N) u - headEnergy N u ≤ C * (N : ℝ) * L at hu
  change (N : ℝ) * ‖displacement - u‖ ^ 2 ≤ D * L at he
  have h1 := annular_headEnergy_add_error N (N + N) (Nat.le_add_right N N) displacement u
  have h2 := headEnergy_norm_le (N + N) (displacement - u)
  rw [Nat.cast_add] at h2
  have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ zetaTwo * (N : ℝ) by positivity)
  have hs : headEnergy (N + N) displacement = headEnergy N displacement +
      ∑ i ∈ Finset.range N, qSequence displacement (N + i + 1) ^ 2 := by
    unfold headEnergy
    rw [Finset.sum_range_add]
  change (∑ i ∈ Finset.range N, qSequence displacement (N + i + 1) ^ 2) ≤
    (2 * C + 8 * zetaTwo * D) * (N : ℝ) * L
  nlinarith

end RiemannResearch.RH.QMeanSquareDisplacement

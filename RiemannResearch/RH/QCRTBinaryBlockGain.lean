/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QCRTFiniteCertificates
import RiemannResearch.RH.QFiniteEnergyBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A strict complete-energy gain from an explicit convex block

Source: user-provided minimum-energy exact-head research agenda,
28 October 2026, priority 5. The finite arithmetic witnesses are the checked
binary certificates at periods 6 and 30. Their values at n=20 provide a
positive complete-Q source term. No numerical quadrature or truncated
infinite sum is used, and no cofinal uniform estimate is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTBinaryBlockGain
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QCRTFiniteCertificates QFiniteEnergyBounds

/-- A two-period affine block; it is convex when t lies in [0,1]. -/
def binaryBlock (t : ℝ) : QHilbert :=
  (1 - t) • sixCertificate + t • thirtyCertificate

private theorem difference_sequence (n : ℕ) :
    qSequence (sixCertificate - thirtyCertificate) n =
      qSequence sixCertificate n - qSequence thirtyCertificate n := by
  change qSequenceLinear (sixCertificate - thirtyCertificate) n = _
  simp only [map_sub, Pi.sub_apply]
  rfl

/-- Full signed energy identity before any estimate is applied. -/
theorem binaryBlock_energy (t : ℝ) :
    ‖binaryBlock t‖ ^ 2 = ‖sixCertificate‖ ^ 2 -
      2 * t * inner ℝ sixCertificate (sixCertificate - thirtyCertificate) +
      t ^ 2 * ‖sixCertificate - thirtyCertificate‖ ^ 2 := by
  have he : binaryBlock t = sixCertificate - t • (sixCertificate - thirtyCertificate) := by
    simp only [binaryBlock, sub_smul, one_smul, smul_sub]
    abel
  rw [he, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right]
  ring

/-- Binary values bound the complete energy of the difference, including its tail. -/
theorem binary_difference_energy_le_one :
    ‖sixCertificate - thirtyCertificate‖ ^ 2 ≤ 1 := by
  rw [qNorm_weighted_sq, ← positiveQWeight_tsum]
  apply (qSequence_square_summable _).tsum_le_tsum _ positiveQWeight_summable
  intro n
  rw [difference_sequence]
  rcases sixCertificate_binary n with h6 | h6 <;>
    rcases thirtyCertificate_binary n with h30 | h30 <;>
      norm_num [h6, h30] <;> exact positiveQWeight_nonneg n

/-- At n=20 the period-six certificate is one and the period-thirty certificate is zero.
All the other terms in the relevant complete-Q source pairing are nonnegative. -/
theorem binary_source_ge_twenty :
    positiveQWeight 20 ≤ inner ℝ sixCertificate (sixCertificate - thirtyCertificate) := by
  have hnonneg (n : ℕ) : 0 ≤ positiveQWeight n * qSequence sixCertificate n *
      qSequence (sixCertificate - thirtyCertificate) n := by
    rw [difference_sequence]
    rcases sixCertificate_binary n with h6 | h6 <;>
      rcases thirtyCertificate_binary n with h30 | h30 <;>
        norm_num [h6, h30] <;> exact positiveQWeight_nonneg n
  have hs := qSequence_product_summable sixCertificate (sixCertificate - thirtyCertificate)
  have h := hs.sum_le_tsum ({20} : Finset ℕ) (fun n _ => hnonneg n)
  have h6 : qSequence sixCertificate 20 = 1 := by
    rw [sixCertificate_sequence]
    norm_num
  have h30 : qSequence thirtyCertificate 20 = 0 := by
    rw [thirtyCertificate_sequence]
    norm_num
  rw [qInner_weighted]
  simpa only [Finset.sum_singleton, difference_sequence, h6, h30,
    one_mul, mul_one, sub_zero] using h

/-- A rational lower bound at one physical coordinate is enough for a rational block. -/
theorem positiveQWeight_twenty_ge_thousandth :
    (1 / 1000 : ℝ) ≤ positiveQWeight 20 := by
  have hZ := inverse_zetaTwo_rational_bounds.1
  have he : positiveQWeight 20 = (1 / zetaTwo) / 400 := by
    norm_num [positiveQWeight, div_eq_mul_inv, mul_inv_rev] <;> ring
  rw [he]
  linarith

/-- An actual rational convex block improves the period-six certificate by at least 10^-6. -/
theorem binaryBlock_thousandth_gain :
    ‖binaryBlock (1 / 1000)‖ ^ 2 ≤ ‖sixCertificate‖ ^ 2 - 1 / 1000000 := by
  have hs := binary_source_ge_twenty
  have hw := positiveQWeight_twenty_ge_thousandth
  have hd := binary_difference_energy_le_one
  rw [binaryBlock_energy]
  nlinarith

theorem binaryBlock_mem_stage (t : ℝ) : binaryBlock t ∈ divisorStage 30 := by
  exact (divisorStage 30).add_mem
    ((divisorStage 30).smul_mem _
      (divisorStage_mono (by norm_num : 6 ∣ 30) sixCertificate_mem_stage))
    ((divisorStage 30).smul_mem _ thirtyCertificate_mem_stage)

theorem binaryBlock_legal (t : ℝ) : binaryBlock t ∈ qSquarefreeCRTSpan := by
  exact qSquarefreeCRTSpan.add_mem
    (qSquarefreeCRTSpan.smul_mem _ sixCertificate_legal)
    (qSquarefreeCRTSpan.smul_mem _ thirtyCertificate_legal)

theorem binaryBlock_exact_head (t : ℝ) (n : ℕ) (hn : 0 < n) (hH : n ≤ 2) :
    qSequence (binaryBlock t) n = 1 := by
  change qSequenceLinear ((1 - t) • sixCertificate + t • thirtyCertificate) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (1 - t) * qSequence sixCertificate n + t * qSequence thirtyCertificate n = 1
  rw [sixCertificate_exact_head n hn hH,
    thirtyCertificate_exact_head n hn (by omega)]
  ring

end RiemannResearch.RH.QCRTBinaryBlockGain

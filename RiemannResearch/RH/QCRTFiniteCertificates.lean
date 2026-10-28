/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Explicit complete-energy certificates at periods six and thirty

Source: the user-provided minimum-energy exact-head research agenda,
28 October 2026, priorities 1 and 3. The two coefficient choices below
were found by finite-stage exploration. All claims use complete Q energy,
including the entire infinite tail. They provide finite benchmarks only;
no cofinal bound or RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTFiniteCertificates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QCRTMinimumEnergy

def sixCertificate : QHilbert :=
  qResidue 2 + (2 : ℝ) • qResidue 3 - qResidue 6

def thirtyCertificate : QHilbert :=
  qResidue 2 + qResidue 3 + qResidue 5 - qResidue 30

theorem sixCertificate_sequence (n : ℕ) :
    qSequence sixCertificate n =
      ((n % 2 : ℕ) : ℝ) / 2 + 2 * (((n % 3 : ℕ) : ℝ) / 3) - ((n % 6 : ℕ) : ℝ) / 6 := by
  change qSequenceLinear (qResidue 2 + (2 : ℝ) • qResidue 3 - qResidue 6) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n + 2 * qSequence (qResidue 3) n -
    qSequence (qResidue 6) n = _
  simp [qSequence_qResidue, residueFraction]

theorem thirtyCertificate_sequence (n : ℕ) :
    qSequence thirtyCertificate n =
      ((n % 2 : ℕ) : ℝ) / 2 + ((n % 3 : ℕ) : ℝ) / 3 + ((n % 5 : ℕ) : ℝ) / 5 -
        ((n % 30 : ℕ) : ℝ) / 30 := by
  change qSequenceLinear (qResidue 2 + qResidue 3 + qResidue 5 - qResidue 30) n = _
  simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
  change qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    qSequence (qResidue 5) n - qSequence (qResidue 30) n = _
  simp [qSequence_qResidue, residueFraction]

theorem sixCertificate_binary (n : ℕ) :
    qSequence sixCertificate n = 0 ∨ qSequence sixCertificate n = 1 := by
  rw [sixCertificate_sequence]
  have h2 : n % 2 = (n % 6) % 2 := by omega
  have h3 : n % 3 = (n % 6) % 3 := by omega
  have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
  rw [h2, h3]
  generalize n % 6 = k at hm ⊢
  interval_cases k <;> norm_num

theorem thirtyCertificate_binary (n : ℕ) :
    qSequence thirtyCertificate n = 0 ∨ qSequence thirtyCertificate n = 1 := by
  rw [thirtyCertificate_sequence]
  have h2 : n % 2 = (n % 30) % 2 := by omega
  have h3 : n % 3 = (n % 30) % 3 := by omega
  have h5 : n % 5 = (n % 30) % 5 := by omega
  have hm : n % 30 < 30 := Nat.mod_lt _ (by omega)
  rw [h2, h3, h5]
  generalize n % 30 = k at hm ⊢
  interval_cases k <;> norm_num

theorem sixCertificate_exact_head (n : ℕ) (hn : 0 < n) (hH : n ≤ 2) :
    qSequence sixCertificate n = 1 := by
  rw [sixCertificate_sequence]
  interval_cases n <;> norm_num

theorem thirtyCertificate_exact_head (n : ℕ) (hn : 0 < n) (hH : n ≤ 5) :
    qSequence thirtyCertificate n = 1 := by
  rw [thirtyCertificate_sequence]
  interval_cases n <;> norm_num

private theorem binary_energy_le_one (f : QHilbert)
    (hf : ∀ n, qSequence f n = 0 ∨ qSequence f n = 1) : ‖f‖ ^ 2 ≤ 1 := by
  rw [qNorm_weighted_sq, ← positiveQWeight_tsum]
  apply (qSequence_square_summable f).tsum_le_tsum _ positiveQWeight_summable
  intro n
  rcases hf n with hn | hn
  · simp only [hn, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact positiveQWeight_nonneg n
  · simp [hn]

theorem sixCertificate_energy_le_one : ‖sixCertificate‖ ^ 2 ≤ 1 :=
  binary_energy_le_one _ sixCertificate_binary

theorem thirtyCertificate_energy_le_one : ‖thirtyCertificate‖ ^ 2 ≤ 1 :=
  binary_energy_le_one _ thirtyCertificate_binary

theorem sixCertificate_mem_stage : sixCertificate ∈ divisorStage 6 := by
  exact (divisorStage 6).sub_mem
    ((divisorStage 6).add_mem
      (Submodule.subset_span ⟨2, by norm_num, rfl⟩)
      ((divisorStage 6).smul_mem _ (Submodule.subset_span ⟨3, by norm_num, rfl⟩)))
    (Submodule.subset_span ⟨6, dvd_refl _, rfl⟩)

theorem thirtyCertificate_mem_stage : thirtyCertificate ∈ divisorStage 30 := by
  exact (divisorStage 30).sub_mem
    ((divisorStage 30).add_mem
      ((divisorStage 30).add_mem
        (Submodule.subset_span ⟨2, by norm_num, rfl⟩)
        (Submodule.subset_span ⟨3, by norm_num, rfl⟩))
      (Submodule.subset_span ⟨5, by norm_num, rfl⟩))
    (Submodule.subset_span ⟨30, dvd_refl _, rfl⟩)

theorem sixCertificate_legal : sixCertificate ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan 6 (by norm_num)
    (by simpa only [show primorial 3 = 6 by decide] using squarefree_primorial 3)
    sixCertificate_mem_stage

theorem thirtyCertificate_legal : thirtyCertificate ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan 30 (by norm_num)
    (by simpa only [show primorial 6 = 30 by decide] using squarefree_primorial 6)
    thirtyCertificate_mem_stage

theorem minimumEnergyApproximant_one_le_one :
    ‖minimumEnergyApproximant 1‖ ^ 2 ≤ 1 := by
  have hp : primorial (1 + 2) = 6 := by decide
  have hmem : sixCertificate ∈ divisorStage (primorial (1 + 2)) := by
    simpa only [hp] using sixCertificate_mem_stage
  have h := (minimumEnergyApproximant_isLeast 1).2
    ⟨sixCertificate, hmem, sixCertificate_exact_head, rfl⟩
  exact h.trans sixCertificate_energy_le_one

theorem minimumEnergyApproximant_four_le_one :
    ‖minimumEnergyApproximant 4‖ ^ 2 ≤ 1 := by
  have hp : primorial (4 + 2) = 30 := by decide
  have hmem : thirtyCertificate ∈ divisorStage (primorial (4 + 2)) := by
    simpa only [hp] using thirtyCertificate_mem_stage
  have h := (minimumEnergyApproximant_isLeast 4).2
    ⟨thirtyCertificate, hmem, thirtyCertificate_exact_head, rfl⟩
  exact h.trans thirtyCertificate_energy_le_one

end RiemannResearch.RH.QCRTFiniteCertificates

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Residue tail certificates and their annihilators

The certificate condition and elementary coordinate and pairing identities are
independent of first-moment and signed-tail regularity obstructions. Those
obstructions remain in `ResidueTailCertificateRegularity`.

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`, Sections 15--16.
These declarations are moved unchanged from `ResidueTailCertificateRegularity`.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- A tail certificate is represented inside H with first coordinate zero.
Its pairings are precisely the reciprocal source from Section 15.3. -/
def IsResidueTailCertificate (z : ThresholdHilbert) : Prop :=
  hilbertSequence z 1 = 0 ∧
    ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ z (normalizedResidueHilbert d (by omega)) = 1 / (d : ℝ)

/-- Extending the tail by value -2 at physical coordinate one. -/
def tailCertificateAnnihilator (z : ThresholdHilbert) : ThresholdHilbert :=
  z - (2 : ℝ) • paretoPointHilbert 0

theorem tailCertificateAnnihilator_first (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    hilbertSequence (tailCertificateAnnihilator z) 1 = -2 := by
  simp only [tailCertificateAnnihilator, hilbertSequence_sub, hilbertSequence_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hilbertSequence_paretoPoint,
    paretoPointSequence, Nat.zero_add, ite_true, hz.1]
  norm_num

theorem tailCertificateAnnihilator_tail (z : ThresholdHilbert) (n : ℕ) (hn : 2 ≤ n) :
    hilbertSequence (tailCertificateAnnihilator z) n = hilbertSequence z n := by
  have hn1 : n ≠ 1 := by omega
  simp [tailCertificateAnnihilator, hilbertSequence_sub, hilbertSequence_smul,
    hilbertSequence_paretoPoint, paretoPointSequence, hn1]

theorem tailCertificateAnnihilator_orthogonal (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (d : ℕ) (hd : 1 < d) :
    inner ℝ (tailCertificateAnnihilator z)
      (normalizedResidueHilbert d (by omega)) = 0 := by
  have hpoint : inner ℝ (paretoPointHilbert 0)
      (normalizedResidueHilbert d (by omega)) = 1 / (2 * (d : ℝ)) := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq,
      normalizedResidueHilbert_sequence]
    simp only [Nat.zero_add, residueFraction, Nat.mod_eq_of_lt hd, Nat.cast_one]
    norm_num [paretoWeight]
    <;> field_simp
    <;> ring
  rw [tailCertificateAnnihilator, inner_sub_left, real_inner_smul_left, hz.2 d hd,
    hpoint]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end RiemannResearch.RH.Pareto

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAdditionalLegalDirections
import RiemannResearch.RH.QPeriodicTailEnergy
import RiemannResearch.RH.QFiniteEnergyBounds

/-!
# Complete rational certificates for the fifth and seventh legal trials

Source: Signed_Quadratic_Correction_Research_Note.pdf, 25 October 2026,
Section 9 and research agenda item 6. The two certificates retain the full
infinite tail by treating 540 and 1260 as (nonminimal) periods. Rational
arithmetic is reduced by the Lean kernel; no floating-point oracle is used.
These finite bounds do not assert convergence of the growing legal dictionary.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSignedCorrectionCertificates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative Pareto
open QAdditionalLegalDirections QSquarefreeLatticePackets QSixAtomTrialBound

/-- A reusable finite rational upper bound including the complete tail. -/
theorem periodic_energy_rational_majorant (L : ℕ) (hL : 0 < L)
    (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    inversePowerMean 0 (fun n => R n ^ 2) ≤
      (76 / 125 : ℝ) * crtReciprocalEnergy L R +
        periodSquareEnergy L R / (L : ℝ)^2 := by
  rw [periodic_qEnergy_first_tail L hL R hR hp]
  have htail := (periodicTailEnergy_bounds L hL R).2
  have hhead := mul_le_mul_of_nonneg_right
    QFiniteEnergyBounds.inverse_zetaTwo_rational_bounds.2.le
    (crtReciprocalEnergy_nonneg L R)
  have he : crtReciprocalEnergy L R / zetaTwo =
      (1 / zetaTwo) * crtReciprocalEnergy L R := by ring
  rw [he]
  exact add_le_add hhead htail

def fifthResidualRat (n : ℕ) : ℚ :=
  1 - ((n % 2 : ℕ) : ℚ)/2 - ((n % 3 : ℕ) : ℚ)/3 - ((n % 5 : ℕ) : ℚ)/5 + ((n % 6 : ℕ) : ℚ)/30

def seventhResidualRat (n : ℕ) : ℚ :=
  1 - ((n % 2 : ℕ) : ℚ)/2 - ((n % 3 : ℕ) : ℚ)/3 - ((n % 5 : ℕ) : ℚ)/5 +
    169 * ((n % 6 : ℕ) : ℚ)/1470 - 4 * ((n % 7 : ℕ) : ℚ)/49

def rationalMajorant (L : ℕ) (r : ℕ → ℚ) : ℚ :=
  (76 / 125 : ℚ) * (∑ a : Fin L, r (a.val + 1)^2 / (a.val + 1 : ℚ)^2) +
    (∑ a : Fin L, r (a.val + 1)^2) / (L : ℚ)^2

theorem rationalMajorant_cast (L : ℕ) (r : ℕ → ℚ) :
    (rationalMajorant L r : ℝ) =
      (76 / 125 : ℝ) * crtReciprocalEnergy L (fun n => (r n : ℝ)) +
        periodSquareEnergy L (fun n => (r n : ℝ)) / (L : ℝ)^2 := by
  unfold rationalMajorant crtReciprocalEnergy periodSquareEnergy
  push_cast
  rfl

theorem fifthResidual_cast (n : ℕ) :
    (fifthResidualRat n : ℝ) = additionalResidual 1 n := by
  unfold fifthResidualRat additionalResidual sixResidual fifthDirectionValue residueFraction
  push_cast
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction of the complete exact-rational finite certificate requires this budget.
theorem fifth_rational_certificate :
    rationalMajorant 540 fifthResidualRat < (7 / 250 : ℚ) := by
  decide +kernel

/-- Sharper unconditional complete-Q certificate requested in the note. -/
theorem fifth_error_lt_seven_two_hundred_fiftieths :
    ‖qOne - additionalTrial 1‖^2 < (7 / 250 : ℝ) := by
  have he : ‖qOne - additionalTrial 1‖^2 =
      inversePowerMean 0 (fun n => additionalResidual 1 n ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [additionalTrial_residual_sequence]
    ring
  have hp (n : ℕ) : additionalResidual 1 (n + 540) = additionalResidual 1 n := by
    simp [additionalResidual, sixResidual, fifthDirectionValue, residueFraction, Nat.add_mod]
  have hb := periodic_energy_rational_majorant 540 (by decide)
    (additionalResidual 1) (additionalResidual_abs_le 1) hp
  have hc0 : (rationalMajorant 540 fifthResidualRat : ℝ) < ((7 / 250 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr fifth_rational_certificate
  have hc : (rationalMajorant 540 fifthResidualRat : ℝ) < (7 / 250 : ℝ) := by
    simpa using hc0
  rw [rationalMajorant_cast] at hc
  simp_rw [fifthResidual_cast] at hc
  rw [he]
  exact hb.trans_lt hc

/-- The paper's seventh-conductor trial, preserving the first five sites. -/
def seventhTrial : QHilbert :=
  additionalTrial 1 + (4 / 7 : ℝ) • compensatedResidue 7 6

def seventhResidual (n : ℕ) : ℝ :=
  additionalResidual 1 n - (4 / 7 : ℝ) *
    (residueFraction 7 n - (6 / 7 : ℝ) * residueFraction 6 n)

theorem seventhResidual_cast (n : ℕ) :
    (seventhResidualRat n : ℝ) = seventhResidual n := by
  unfold seventhResidualRat seventhResidual additionalResidual sixResidual
    fifthDirectionValue residueFraction
  push_cast
  ring

theorem seventhTrial_sequence (n : ℕ) :
    qSequence seventhTrial n = qSequence (additionalTrial 1) n +
      (4 / 7 : ℝ) * (residueFraction 7 n - (6 / 7 : ℝ) * residueFraction 6 n) := by
  change qSequenceLinear (_ + _ • _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (additionalTrial 1) n +
    (4 / 7 : ℝ) * qSequence (compensatedResidue 7 6) n = _
  rw [compensatedResidue_sequence]
  norm_num

theorem seventhTrial_head_five (n : ℕ) (hn : 0 < n) (hn5 : n ≤ 5) :
    qSequence seventhTrial n = 1 := by
  rw [seventhTrial_sequence, additionalTrial_one_head_five n hn hn5]
  interval_cases n <;> norm_num [residueFraction]

theorem seventhTrial_mem_squarefreeSpan : seventhTrial ∈ qSquarefreeCRTSpan := by
  have h7 : qResidue 7 ∈ qSquarefreeCRTSpan :=
    Submodule.subset_span ⟨⟨7, by decide, (by norm_num : Nat.Prime 7).squarefree⟩, rfl⟩
  have h6 : qResidue 6 ∈ qSquarefreeCRTSpan := by
    have hsf : Squarefree (6 : ℕ) := by
      change Squarefree ((2 : ℕ) * 3)
      exact Nat.squarefree_mul_iff.mpr
        ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
    exact Submodule.subset_span ⟨⟨6, by decide, hsf⟩, rfl⟩
  exact qSquarefreeCRTSpan.add_mem (additionalTrial_mem_squarefreeSpan 1)
    (qSquarefreeCRTSpan.smul_mem _
      (qSquarefreeCRTSpan.sub_mem h7 (qSquarefreeCRTSpan.smul_mem _ h6)))

theorem seventhResidual_period (n : ℕ) :
    seventhResidual (n + 1260) = seventhResidual n := by
  simp [seventhResidual, additionalResidual, sixResidual, fifthDirectionValue,
    residueFraction, Nat.add_mod]

theorem seventhResidual_abs_le (n : ℕ) : |seventhResidual n| ≤ 3 := by
  have h2 : (0 : ℝ) ≤ (n % 2 : ℕ) ∧ ((n % 2 : ℕ) : ℝ) ≤ 1 := by
    constructor; positivity
    exact_mod_cast (show n % 2 ≤ 1 by omega)
  have h3 : (0 : ℝ) ≤ (n % 3 : ℕ) ∧ ((n % 3 : ℕ) : ℝ) ≤ 2 := by
    constructor; positivity
    exact_mod_cast (show n % 3 ≤ 2 by omega)
  have h5 : (0 : ℝ) ≤ (n % 5 : ℕ) ∧ ((n % 5 : ℕ) : ℝ) ≤ 4 := by
    constructor; positivity
    exact_mod_cast (show n % 5 ≤ 4 by omega)
  have h6 : (0 : ℝ) ≤ (n % 6 : ℕ) ∧ ((n % 6 : ℕ) : ℝ) ≤ 5 := by
    constructor; positivity
    exact_mod_cast (show n % 6 ≤ 5 by omega)
  have h7 : (0 : ℝ) ≤ (n % 7 : ℕ) ∧ ((n % 7 : ℕ) : ℝ) ≤ 6 := by
    constructor; positivity
    exact_mod_cast (show n % 7 ≤ 6 by omega)
  rw [← seventhResidual_cast]
  unfold seventhResidualRat
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem seventhTrial_residual_sequence (n : ℕ) :
    qSequence (qOne - seventhTrial) (n + 1) = seventhResidual (n + 1) := by
  change qSequenceLinear (qOne - seventhTrial) (n + 1) = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence qOne (n + 1) - qSequence seventhTrial (n + 1) = _
  rw [qSequence_qOne, seventhTrial_sequence, additionalTrial_sequence]
  simp only [qOneSequence, Nat.add_one_ne_zero, if_false, seventhResidual,
    additionalResidual, sixResidual]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction of the complete exact-rational finite certificate requires this budget.
theorem seventh_rational_certificate :
    rationalMajorant 1260 seventhResidualRat < (1 / 50 : ℚ) := by
  decide +kernel

/-- The entire Q norm is below one fiftieth, including every residue tail. -/
theorem seventh_error_lt_one_fiftieth :
    ‖qOne - seventhTrial‖^2 < (1 / 50 : ℝ) := by
  have he : ‖qOne - seventhTrial‖^2 =
      inversePowerMean 0 (fun n => seventhResidual n ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [seventhTrial_residual_sequence]
    ring
  have hb := periodic_energy_rational_majorant 1260 (by decide)
    seventhResidual seventhResidual_abs_le seventhResidual_period
  have hc0 : (rationalMajorant 1260 seventhResidualRat : ℝ) < ((1 / 50 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr seventh_rational_certificate
  have hc : (rationalMajorant 1260 seventhResidualRat : ℝ) < (1 / 50 : ℝ) := by
    simpa using hc0
  rw [rationalMajorant_cast] at hc
  simp_rw [seventhResidual_cast] at hc
  rw [he]
  exact hb.trans_lt hc

/-- The actual full-Q projection onto any space containing the five atoms
inherits the certified seventh-trial bound. -/
theorem projection_error_lt_one_fiftieth
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h5 : qResidue 5 ∈ V) (h6 : qResidue 6 ∈ V) (h7 : qResidue 7 ∈ V) :
    ‖qOne - V.starProjection qOne‖ ^ 2 < (1 / 50 : ℝ) := by
  have ht : seventhTrial ∈ V :=
    V.add_mem (additionalTrial_mem V 1 h2 h3 h5 h6)
      (V.smul_mem _ (V.sub_mem h7 (V.smul_mem _ h6)))
  have he : (qOne - seventhTrial) - V.starProjection (qOne - seventhTrial) =
      qOne - V.starProjection qOne := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr ht]
    abel
  have hn := RiemannResearch.Analysis.ProjectionCompression.defect_norm_le V
    (qOne - seventhTrial)
  rw [he] at hn
  exact lt_of_le_of_lt ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)
    seventh_error_lt_one_fiftieth

/-- The improved certified error strengthens the actual parity-leakage bound. -/
theorem seventh_optimizer_parity_leakage_bounds
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h5 : qResidue 5 ∈ V) (h6 : qResidue 6 ∈ V) (h7 : qResidue 7 ∈ V) :
    (23 / 25 : ℝ) * ‖qOne - V.starProjection qOne‖ ^ 2 ≤
      ‖V.starProjection qOne -
        QParityProjectionDefect.paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ∧
    ‖V.starProjection qOne -
      QParityProjectionDefect.paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ≤
        ‖qOne - V.starProjection qOne‖ ^ 2 := by
  rw [QParityProjectionDefect.optimizer_parity_leakage_exact V h2]
  have hb := (projection_error_lt_one_fiftieth V h2 h3 h5 h6 h7).le
  have hd : 0 ≤ ‖qOne - V.starProjection qOne‖ ^ 2 := sq_nonneg _
  have hm := mul_nonneg hd (sub_nonneg.mpr hb)
  constructor <;> nlinarith [sq_nonneg (‖qOne - V.starProjection qOne‖ ^ 2)]

end RiemannResearch.RH.QSignedCorrectionCertificates

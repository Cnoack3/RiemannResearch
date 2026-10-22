/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import Mathlib.Tactic.Linarith

/-!
# Finite Ramanujan inversion and the distinction from Q wavelet coordinates

Source: user-provided coefficient-inversion identity, 13 October 2026.
The inversion is proved for actual finite packet coefficients. It is not
an inverse formula for the orthogonal Q wavelet coefficients, and it does
not assert an infinite summation/limit interchange.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QRamanujanPackets
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability

/-- Finite multiple-transform inversion, for any two equal actual
residue/packet syntheses. The packet sum is finite; no interchange of
infinite limits or sums is used. -/
theorem finite_packet_coefficient_inversion
    (s t : Finset ℕ) (c a : ℕ → ℝ)
    (ht : ∀ q ∈ t, 0 < q)
    (h : (fun n => ∑ d ∈ s, c d * residueFraction d n) =
      (fun n => ∑ q ∈ t, a q * ramanujanPacket q n))
    (m : ℕ) (hm : 1 < m) :
    (if m ∈ s then c m else 0) =
      (m : ℝ) * ∑ q ∈ t,
        if m ∣ q then (ArithmeticFunction.moebius (q / m) : ℝ) * a q else 0 := by
  classical
  have hdual := congrArg (mobiusDifference m) h
  rw [residueFraction_sum_mobiusDifference s c m hm,
    mobiusDifference_sum] at hdual
  have hr :
      (∑ q ∈ t, a q * mobiusDifference m (ramanujanPacket q)) =
        -(m : ℝ) * ∑ q ∈ t,
          if m ∣ q then (ArithmeticFunction.moebius (q / m) : ℝ) * a q else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [mobiusDifference_packet m q hm (ht q hq)]
    split_ifs <;> ring
  rw [hr] at hdual
  linarith

theorem qResidueDivisorCoefficient_two_eq_neg_mean :
    qResidueDivisorCoefficient 2 2 = -inner ℝ qOne (qResidue 2) := by
  have hd : (2 : ℕ).divisors = {1, 2} := by decide
  have hm : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  simp [qResidueDivisorCoefficient, hd, hm,
    qTwistedResidueMean_eq_zero_of_dvd 2 2 (dvd_refl 2),
    qTwistedResidueMean_one]

theorem qResidue_mean_nonneg (d : ℕ) :
    0 ≤ inner ℝ qOne (qResidue d) := by
  rw [qResidue_mean_eq_inversePowerMean]
  unfold inversePowerMean
  apply tsum_nonneg
  intro n
  have hz : 0 < zetaTwo := zetaTwo_pos
  unfold residueFraction
  positivity

theorem qResidueDivisorCoefficient_two_nonpos :
    qResidueDivisorCoefficient 2 2 ≤ 0 := by
  rw [qResidueDivisorCoefficient_two_eq_neg_mean]
  exact neg_nonpos.mpr (qResidue_mean_nonneg 2)

/-- A single actual atom already distinguishes the two coefficient systems. -/
theorem qResidueDivisorCoefficient_two_ne_packetCoefficient :
    qResidueDivisorCoefficient 2 2 ≠
      packetCoefficient (fun _ : Fin 1 => 2) (fun _ => 1) 2 := by
  have hp : packetCoefficient (fun _ : Fin 1 => 2) (fun _ => (1 : ℝ)) 2 = 1 / 2 := by
    norm_num [packetCoefficient]
  rw [hp]
  have hn := qResidueDivisorCoefficient_two_nonpos
  linarith

private theorem audit_qSequence_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → QHilbert) :
    qSequence (∑ i ∈ s, f i) = fun n => ∑ i ∈ s, qSequence (f i) n := by
  funext n
  change (qSequenceLinear (∑ i ∈ s, f i)) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

private theorem audit_qSequence_smul (a : ℝ) (f : QHilbert) :
    qSequence (a • f) = fun n => a * qSequence f n := by
  change qSequenceLinear (a • f) = a • qSequenceLinear f
  exact qSequenceLinear.map_smul a f

/-- The finite inverse for the actual packet coefficients of an arbitrary
finite positive-conductor residue candidate. All synthesis equalities are
discharged using the actual Q Hilbert-space packet expansion. -/
theorem packetCoefficient_finite_inversion
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 0 < d)
    (m : ℕ) (hm : 1 < m) :
    (if m ∈ s then c m else 0) =
      (m : ℝ) * ∑ q ∈ packetSupport (fun i : s => i.val),
        if m ∣ q then (ArithmeticFunction.moebius (q / m) : ℝ) *
          packetCoefficient (fun i : s => i.val) (fun i => c i.val) q else 0 := by
  classical
  apply finite_packet_coefficient_inversion s
    (packetSupport (fun i : s => i.val)) c
    (packetCoefficient (fun i : s => i.val) (fun i => c i.val)) ?_ ?_ m hm
  · intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨i, _, hqi⟩
    exact Nat.pos_of_mem_divisors hqi
  · have hsum (f : ℕ → ℝ) : (∑ i : s, f i.val) = ∑ d ∈ s, f d := by
      apply Finset.sum_bij (fun i _ => i.val)
      · intro i _
        exact i.property
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro d hd
        exact ⟨⟨d, hd⟩, Finset.mem_univ _, rfl⟩
      · intro i _
        rfl
    have hphysical := congrArg qSequence
      (qSynthesis_eq_packets (fun i : s => i.val) (fun i => c i.val)
        (fun i => hs i.val i.property))
    unfold RiemannResearch.RH.QCovarianceInverse.qSynthesis at hphysical
    rw [audit_qSequence_finsetSum, audit_qSequence_finsetSum] at hphysical
    funext n
    have hn := congrFun hphysical n
    simp only [audit_qSequence_smul, qSequence_qResidue,
      qSequence_qRamanujanPacket] at hn
    rw [hsum (fun d => c d * residueFraction d n)] at hn
    exact hn

end RiemannResearch.RH.QRamanujanPackets

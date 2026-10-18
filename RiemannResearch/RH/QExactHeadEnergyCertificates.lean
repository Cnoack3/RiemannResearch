/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusWindowCancellation
import RiemannResearch.RH.CanonicalMobiusSublinearEnergy
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoSublinearResidualTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q energy certificates for actual canonical exact heads

Source: user-provided H=1 parity calculation, 18 October 2026, for the exact
quarter error. The general signed residual identity specializes the existing
finite Mobius floor-tail identity. The quantified window budget combines the
existing full Pareto cutoff estimate and actual Q/P transfer; both arithmetic
cancellation inputs remain explicit in its type.

Research consumer: QExactHeadEnergyAuditResearch20261018.md. No bounded or
subpolynomial complete energy, and no RH theorem, is asserted here. The halted
five-iteration sparse power-cost program is not resumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QExactHeadEnergyCertificates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
theorem exactHead_one : QMobiusExactHead.exactHead 1 = (2 : ℝ) • qResidue 2 := by
  norm_num [QMobiusExactHead.exactHead, Pareto.mobiusReciprocalSum]

theorem two_residue_error_sq : ‖qOne - (2 : ℝ) • qResidue 2‖ ^ 2 = (1 : ℝ) / 4 := by
  have hp (k : ℕ) : qSequence (qOne - (2 : ℝ) • qResidue 2) (k+1) =
      1 - 2 * (((k+1) % 2 : ℕ) : ℝ) / 2 := by
    change qSequenceLinear (qOne - (2 : ℝ) • qResidue 2) (k+1) = _
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change qSequence qOne (k+1) - 2 * qSequence (qResidue 2) (k+1) = _
    rw [qSequence_qOne, qSequence_qResidue]
    simp [qOneSequence, residueFraction]
    ring
  have hsq (k : ℕ) :
      qSequence (qOne - (2 : ℝ) • qResidue 2) (k+1) *
        qSequence (qOne - (2 : ℝ) • qResidue 2) (k+1) =
      if 2 ∣ k+1 then (1 : ℝ) else 0 := by
    rw [hp]
    have hm : (k+1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases hd : 2 ∣ k+1
    · simp [Nat.mod_eq_zero_of_dvd hd, hd]
    · have hm1 : (k+1) % 2 = 1 := by
        have hz : (k+1) % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
        omega
      simp [hm1, hd]
  have hid : ‖qOne - (2 : ℝ) • qResidue 2‖ ^ 2 =
      inversePowerMean 0 (fun n => if 2 ∣ n then (1 : ℝ) else 0) := by
    rw [← real_inner_self_eq_norm_sq, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro k
    change (qSequence (qOne - (2 : ℝ) • qResidue 2) (k+1) *
      qSequence (qOne - (2 : ℝ) • qResidue 2) (k+1)) / _ = _
    rw [hsq]
  rw [hid, inversePowerMean_dvd 2 (by norm_num)]
  have hconst : inversePowerMean 0 (fun _ => (1 : ℝ)) = 1 := by
    rw [inversePowerMean_zero_eq_pnat_tsum]
    simp only [mul_one]
    unfold positiveQWeight
    simp_rw [show ∀ k : ℕ+, 1 / (zetaTwo * (k : ℝ)^2) =
      (1 / (k : ℝ)^2) / zetaTwo by intro k; ring]
    rw [tsum_div_const, ← zetaTwo, div_self (ne_of_gt zetaTwo_pos)]
  norm_num [hconst]

theorem exactHead_one_error_sq :
    ‖qOne - QMobiusExactHead.exactHead 1‖ ^ 2 = (1 : ℝ) / 4 := by
  rw [exactHead_one, two_residue_error_sq]
theorem exactHead_residual_floor_tail (N n : ℕ) (hn : 0 < n) (hNn : N ≤ n) :
    1 - qSequence (QMobiusExactHead.exactHead N) n =
      (∑ k ∈ Finset.Icc 1 (n / (N+1)),
        ((∑ d ∈ Finset.Icc 1 (n/k), (ArithmeticFunction.moebius d : ℝ)) -
         (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)))) +
      (((N+1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum N) *
        ((n / (N+1) : ℕ) : ℝ) := by
  rw [QMobiusExactHead.exactHead_sequence,
    Pareto.canonicalMobiusHead_floor_expansion]
  have h := Pareto.finite_mobius_floor_tail_identity N n hn hNn
  linarith

/-- A quantified cancellation envelope gives a complete Q-error estimate.
The two arithmetic bounds remain displayed hypotheses; no RH premise occurs. -/
theorem exactHead_error_window_budget (N K : ℕ) (hN : 0 < N) (hK : 2 ≤ K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hM : ∀ t : ℕ, N ≤ t →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ))
    (hm : |Pareto.mobiusReciprocalSum N| ≤ ε) :
    ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (8 + 4 * (N : ℝ) *
        (1 / (N : ℝ) + 2 * ε * (K : ℝ) * ((K : ℝ) + 2)) ^ 2 +
        16 * (N : ℝ) / (K : ℝ)) / zetaTwo := by
  let a : ℝ := 1 / (N : ℝ) + 2 * ε * (K : ℝ) * ((K : ℝ) + 2)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hmid (n : ℕ) (hNn : N < n) (hnK : n ≤ K*N) :
      |Pareto.canonicalMobiusHead N n| ≤ a * (N : ℝ) := by
    have hb := Pareto.canonicalMobiusHead_window_bound N n K ε hε hNn
      (hnK.trans (by nlinarith : K*N ≤ K*(N+1))) hM hm
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : ((N+1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by push_cast; linarith
    have hc : 0 ≤ ε * (K : ℝ) * ((K : ℝ)+2) := by positivity
    have hh := mul_le_mul_of_nonneg_left hNp hc
    have heq : a * (N : ℝ) =
        1 + 2 * ε * (K : ℝ) * ((K : ℝ)+2) * (N : ℝ) := by
      dsimp [a]
      field_simp
    rw [heq]
    linarith
  have hp := Pareto.canonicalMobiusHilbert_cutoff_bound N K hN hK a hmid
  have hp' : ‖Pareto.canonicalMobiusHilbert N‖ ^ 2 ≤
      1 + a^2 * (N : ℝ) + 4 * (N : ℝ) / (K : ℝ) := by
    have hh := (div_le_iff₀ hNR).mp hp
    have heq : (1/(N:ℝ)+a^2+4/(K:ℝ))*(N:ℝ) =
        1 + a^2*(N:ℝ)+4*(N:ℝ)/(K:ℝ) := by field_simp
    simpa only [heq] using hh
  have hmap : ZetaTwoParetoTransfer.toPareto (qOne - QMobiusExactHead.exactHead N) =
      Pareto.hilbertOne - Pareto.canonicalMobiusHilbert N := by
    change ZetaTwoParetoTransfer.toParetoLinear (_ - _) = _
    rw [map_sub]
    change ZetaTwoParetoTransfer.toPareto qOne -
      ZetaTwoParetoTransfer.toPareto (QMobiusExactHead.exactHead N) = _
    rw [ZetaTwoParetoTransfer.toPareto_qOne, QSquarefreeSublinearHeads.toPareto_exactHead]
  have ht := ZetaTwoParetoTransfer.zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (qOne - QMobiusExactHead.exactHead N)
  rw [hmap] at ht
  have he := Pareto.one_sub_energy_le (Pareto.canonicalMobiusHilbert N)
  apply (le_div_iff₀ zetaTwo_pos).mpr
  change ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 * zetaTwo ≤
    8 + 4 * (N : ℝ) * a^2 + 16 * (N : ℝ) / (K : ℝ)
  have hdiv : 16 * (N : ℝ) / (K : ℝ) = 4 * (4 * (N : ℝ) / (K : ℝ)) := by ring
  rw [hdiv]
  nlinarith
end RiemannResearch.RH.QExactHeadEnergyCertificates

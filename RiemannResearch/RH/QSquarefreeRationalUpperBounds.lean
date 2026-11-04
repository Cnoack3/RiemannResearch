/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ParetoCRTReciprocalEnergy
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QTensorCertificateInfimum
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# A rational seven-atom complete-Q improvement

Source: user-requested extension of the three-atom benchmark. Coefficients
were selected using the complete-Q Gram matrix, then fixed rationally.
The proof strategy reuses `periodic_qEnergy_comparison`; its first-period
bound is weaker than the separate exact-rational infinite-tail enclosure.

Bagchi, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137--146,
Remark 8, https://arxiv.org/pdf/math/0607733, supports the squarefree
closure context, not the new numerical certificate.

The separate 121-atom certificate < 5873/1000000 is an exact arithmetic
calculation with an on-paper tail proof. It is NOT formalized here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeRationalUpperBounds
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative Pareto
open QCovarianceInverse QTensorCertificate

def errorVector : QHilbert :=
  qOne - ((985587/1000000 : ℝ) • qResidue 2 +
    (963419/1000000 : ℝ) • qResidue 3 +
    (823721/1000000 : ℝ) • qResidue 5 +
    (-158232/1000000 : ℝ) • qResidue 6 +
    (91952/1000000 : ℝ) • qResidue 10 +
    (138611/1000000 : ℝ) • qResidue 15 +
    (146439/1000000 : ℝ) • qResidue 30)

def residual (n : ℕ) : ℝ :=
  1 - ((985587/1000000 : ℝ) * residueFraction 2 n +
    (963419/1000000 : ℝ) * residueFraction 3 n +
    (823721/1000000 : ℝ) * residueFraction 5 n +
    (-158232/1000000 : ℝ) * residueFraction 6 n +
    (91952/1000000 : ℝ) * residueFraction 10 n +
    (138611/1000000 : ℝ) * residueFraction 15 n +
    (146439/1000000 : ℝ) * residueFraction 30 n)

theorem errorVector_coordinate (n : ℕ) (hn : n ≠ 0) :
    qSequence errorVector n = residual n := by
  change qSequenceLinear (qOne - ((985587/1000000 : ℝ) • qResidue 2 +
    (963419/1000000 : ℝ) • qResidue 3 +
    (823721/1000000 : ℝ) • qResidue 5 +
    (-158232/1000000 : ℝ) • qResidue 6 +
    (91952/1000000 : ℝ) • qResidue 10 +
    (138611/1000000 : ℝ) • qResidue 15 +
    (146439/1000000 : ℝ) • qResidue 30)) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence qOne n - ((985587/1000000 : ℝ) * qSequence (qResidue 2) n +
    (963419/1000000 : ℝ) * qSequence (qResidue 3) n +
    (823721/1000000 : ℝ) * qSequence (qResidue 5) n +
    (-158232/1000000 : ℝ) * qSequence (qResidue 6) n +
    (91952/1000000 : ℝ) * qSequence (qResidue 10) n +
    (138611/1000000 : ℝ) * qSequence (qResidue 15) n +
    (146439/1000000 : ℝ) * qSequence (qResidue 30) n) = _
  simp [qSequence_qOne, qOneSequence, hn, qSequence_qResidue, residual]

theorem residual_bound (n : ℕ) : |residual n| ≤ 5 := by
  have hb (d : ℕ) (hd : 0 < d) :
      0 ≤ residueFraction d n ∧ residueFraction d n ≤ 1 := by
    unfold residueFraction
    constructor
    · positivity
    · apply (div_le_one (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
      exact_mod_cast (Nat.mod_lt n hd).le
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide)
  have h10 := hb 10 (by decide)
  have h15 := hb 15 (by decide)
  have h30 := hb 30 (by decide)
  rw [abs_le]
  unfold residual
  constructor <;> nlinarith

theorem residual_periodic (n : ℕ) : residual (n + 30) = residual n := by
  simp [residual, residueFraction, Nat.add_mod]

set_option maxHeartbeats 8000000 in
-- Expanding the exact 30-residue sum evaluates seven rational atoms at each residue.
set_option maxRecDepth 4000 in
theorem complete_norm_lt : ‖errorVector‖ ^ 2 < (361 : ℝ) / 10000 := by
  have hn : ‖errorVector‖ ^ 2 = inversePowerMean 0 (fun n => residual n ^ 2) := by
    rw [qNorm_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    dsimp only
    rw [errorVector_coordinate (n+1) (by omega)]
  have hb := (periodic_qEnergy_comparison 30 (by decide)
    residual residual_bound residual_periodic).2
  have hr : crtReciprocalEnergy 30 residual < (361 : ℝ) / 10000 := by
    norm_num [crtReciprocalEnergy, Fin.sum_univ_succ, residual, residueFraction]
  rw [hn]
  exact hb.trans_lt hr

theorem legalErrorInfimum_lt : legalErrorInfimum < (361 : ℝ) / 10000 := by
  let d : Fin 7 → {d : ℕ // 2 ≤ d ∧ Squarefree d} :=
    ![⟨2, ⟨by decide, by decide +kernel⟩⟩,
      ⟨3, ⟨by decide, by decide +kernel⟩⟩,
      ⟨5, ⟨by decide, by decide +kernel⟩⟩,
      ⟨6, ⟨by decide, by decide +kernel⟩⟩,
      ⟨10, ⟨by decide, by decide +kernel⟩⟩,
      ⟨15, ⟨by decide, by decide +kernel⟩⟩,
      ⟨30, ⟨by decide, by decide +kernel⟩⟩]
  let c : Fin 7 → ℝ :=
    ![985587/1000000, 963419/1000000, 823721/1000000,
      -158232/1000000, 91952/1000000, 138611/1000000, 146439/1000000]
  have he : qOne - qSynthesis (fun i => (d i).val) c = errorVector := by
    simp [qSynthesis, d, c, Fin.sum_univ_succ, errorVector, add_assoc]
  have hi := legalErrorInfimum_le_error 7 d c
  rw [he] at hi
  exact hi.trans_lt complete_norm_lt

theorem anchoredInfimum_lt : anchoredInfimum < (361 : ℝ) / 10000 := by
  rw [anchoredInfimum_eq_legalErrorInfimum]
  exact legalErrorInfimum_lt

end RiemannResearch.RH.QSquarefreeRationalUpperBounds

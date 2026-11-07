/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTProjectedMellin
import RiemannResearch.RH.QGcdSampling
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QMellinWitness
import RiemannResearch.Analysis.MellinDifferenceBounds
import RiemannResearch.Analysis.WeightedComplexPairing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The exact multiples endpoint of the gcd-sampled CRT Mellin witness

Source: user-provided CRT collocation handoff, Section 7. The signed endpoint
is retained exactly as zeta(2) times the actual first Mellin difference.
This is the residual-error version; the orthogonal-leakage version has its
separate actual multiples Mellin endpoint.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTExactEndpoint
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QCRTFiniteCollocation QCRTZeroObstruction QCRTProjectedMellin
open QMellinTransfer QMellinWitness QGcdSampling
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.Analysis.WeightedPairing

/-- The full mass of multiples of L in the actual shifted Q coordinates. -/
theorem divisor_weight_hasSum (L : ℕ) (hL : 0 < L) :
    HasSum (fun n : ℕ => qWeight n * qSequence (qDivisor L) (n+1))
      (1/(L : ℝ)^2) := by
  have hfull := qSequence_product_summable qOne (qDivisor L)
  have hshift := (summable_nat_add_iff 1).mpr hfull
  have hp := hshift.hasSum
  have hval : (∑' n : ℕ, positiveQWeight (n+1) * qSequence qOne (n+1) *
      qSequence (qDivisor L) (n+1)) = 1/(L : ℝ)^2 := by
    have hi := qOne_inner_qDivisor L hL
    rw [qInner_weighted, hfull.tsum_eq_zero_add] at hi
    simpa only [qSequence_zero, mul_zero, zero_add] using hi
  rw [hval] at hp
  have hon (n : ℕ) : qSequence qOne (n+1) = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence]
  simpa only [qWeight, hon, mul_one] using hp

/-- The gcd sampler on the multiples cell is exactly its endpoint value. -/
theorem divisor_sample_pairing_hasSum (s : ℂ) (L : ℕ) (hL : 0 < L) :
    HasSum (fun n : ℕ => (qWeight n : ℂ) * rawWitness s (Nat.gcd (n+1) L) *
      (qSequence (qDivisor L) (n+1) : ℂ))
      ((zetaTwo : ℂ) * mellinFirst s L) := by
  have hp := (Complex.ofRealCLM.hasSum (divisor_weight_hasSum L hL)).mul_left
    (rawWitness s L)
  have hval : rawWitness s L * (((1/(L : ℝ)^2) : ℝ) : ℂ) =
      (zetaTwo : ℂ) * mellinFirst s L := by
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
    unfold rawWitness
    push_cast
    field_simp
  change HasSum (fun n : ℕ => rawWitness s L *
    ((qWeight n * qSequence (qDivisor L) (n+1) : ℝ) : ℂ))
      (rawWitness s L * (((1/(L : ℝ)^2) : ℝ) : ℂ)) at hp
  rw [hval] at hp
  apply hp.congr_fun
  intro n
  rw [qSequence_qDivisor]
  have hn0 : n+1 ≠ 0 := by omega
  simp only [positiveDivisor, if_neg hn0]
  by_cases hd : L ∣ n+1
  · rw [if_pos hd, Nat.gcd_eq_right hd]
    push_cast
    ring
  · rw [if_neg hd]
    simp

/-- Exact signed normalized boundary balance, as an actual convergent series. -/
theorem canonical_error_dualResidual_hasSum (L : ℕ) (hL : 2 ≤ L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s = 0) :
    HasSum (fun n : ℕ => dualResidual s L n *
      (qSequence (qOne-(canonical L hL : QHilbert)) (n+1) : ℂ))
      (1-(zetaTwo : ℂ)*mellinFirst s L) := by
  have hLp : 0 < L := by omega
  let z : QHilbert := (canonical L hL : QHilbert)-target L
  have ha : HasSum (fun n : ℕ => dualResidual s L n *
      (qSequence (qDivisor L) (n+1) : ℂ))
      (s*qMellin (qDivisor L) s-(zetaTwo : ℂ)*mellinFirst s L) := by
    have h := (qMellin_hasSum (qDivisor L) s hs).sub
      (divisor_sample_pairing_hasSum s L hLp)
    simpa only [dualResidual, sub_mul] using h
  have hz : conditionalProjection L z = 0 := canonical_leakage_projection_zero L hL
  have hb := dualResidual_pairing_hasSum s hs L hLp z hz
  have hp := ha.sub hb
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have he : s*qMellin (qDivisor L) s-(zetaTwo : ℂ)*mellinFirst s L-
      s*qMellin z s = 1-(zetaTwo : ℂ)*mellinFirst s L := by
    calc
      _ = s*(qMellin (qDivisor L) s-qMellin z s)-
          (zetaTwo : ℂ)*mellinFirst s L := by ring
      _ = _ := by
        rw [← canonical_mellin_balance L hL s hs hs1 hzeta]
        field_simp
  rw [he] at hp
  have hvec : qOne-(canonical L hL : QHilbert) = qDivisor L-z := by
    dsimp [z, target]
    abel
  have hseq (n : ℕ) : qSequence (qDivisor L-z) n =
      qSequence (qDivisor L) n-qSequence z n := by
    change qSequenceLinear (qDivisor L-z) n = _
    rw [map_sub]
    rfl
  rw [hvec]
  simpa only [hseq, Complex.ofReal_sub, mul_sub] using hp

/-- Exact endpoint-sensitive residual obstruction before any endpoint estimate. -/
theorem canonical_error_endpoint_sq_le (L : ℕ) (hL : 2 ≤ L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re ≤ 1) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s = 0) :
    ‖1-(zetaTwo : ℂ)*mellinFirst s L‖^2 ≤
      defectEnergy s L * ‖qOne-(canonical L hL : QHilbert)‖^2 := by
  let e : QHilbert := qOne-(canonical L hL : QHilbert)
  have hb : Summable (fun n : ℕ => ‖dualResidual s L n‖^2/qWeight n) := by
    simpa only [dualResidual_energy] using defectTerm_summable s hs hslt L
  have hM : Summable (fun n : ℕ => qWeight n * ‖(qSequence e (n+1) : ℂ)‖^2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, qWeight,
      qSequence_weighted_square] using qCoordinate_square_summable e
  have h := pairing_norm_sq_le qWeight qWeight_pos (dualResidual s L)
    (fun n => (qSequence e (n+1) : ℂ)) hb hM
  rw [(canonical_error_dualResidual_hasSum L hL s hs hs1 hzeta).tsum_eq] at h
  simp_rw [dualResidual_energy] at h
  simpa only [defectEnergy, Complex.norm_real, Real.norm_eq_abs, sq_abs, qWeight,
    qSequence_weighted_square, ← qNorm_sq] using h

/-- The exact endpoint has the stronger L^(-1-Re(s)) decay. -/
theorem endpoint_norm_le (s : ℂ) (hs : 0 < s.re) (L : ℕ) (hL : 0 < L) :
    ‖(zetaTwo : ℂ)*mellinFirst s L‖ ≤
      zetaTwo * ‖s‖ * (L : ℝ)^(-s.re-1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos zetaTwo_pos]
  exact (mul_le_mul_of_nonneg_left (mellinFirst_norm_le s hs L hL)
    zetaTwo_pos.le).trans_eq (by ring)

/-- The handoff's endpoint rate with the improved proper-divisor coefficient.
The exact signed endpoint was retained in canonical_error_endpoint_sq_le. -/
theorem canonical_residual_explicit_obstruction (L : ℕ) (hL : 2 ≤ L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re ≤ 1) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s = 0) :
    1/‖s‖ ≤ escapeFactor s *
      Real.sqrt (zetaTwo * RiemannResearch.NumberTheory.DivisorEscapeTail.tail (2*s.re) L) *
        ‖qOne-(canonical L hL : QHilbert)‖ +
      zetaTwo * (L : ℝ)^(-s.re-1) := by
  have hZ := zetaTwo_pos
  have hD := RiemannResearch.NumberTheory.DivisorEscapeTail.tail_nonneg (2*s.re) L
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  let e : QHilbert := qOne-(canonical L hL : QHilbert)
  let D : ℝ := RiemannResearch.NumberTheory.DivisorEscapeTail.tail (2*s.re) L
  have hsq := (canonical_error_endpoint_sq_le L hL s hs hslt hs1 hzeta).trans
    (mul_le_mul_of_nonneg_right (defectEnergy_le_sharp s hs hslt L) (sq_nonneg ‖e‖))
  change ‖1-(zetaTwo : ℂ)*mellinFirst s L‖^2 ≤
    ((escapeFactor s)^2 * zetaTwo * ‖s‖^2) * D * ‖e‖^2 at hsq
  have hcoef : 0 ≤ escapeFactor s * ‖s‖ * Real.sqrt (zetaTwo * D) * ‖e‖ := by
    positivity
  have he : (escapeFactor s * ‖s‖ * Real.sqrt (zetaTwo * D) * ‖e‖)^2 =
      ((escapeFactor s)^2 * zetaTwo * ‖s‖^2) * D * ‖e‖^2 := by
    have hZD : 0 ≤ zetaTwo * D := mul_nonneg hZ.le hD
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hZD]
    ring
  have hroot : ‖1-(zetaTwo : ℂ)*mellinFirst s L‖ ≤
      escapeFactor s * ‖s‖ * Real.sqrt (zetaTwo * D) * ‖e‖ := by
    nlinarith [norm_nonneg (1-(zetaTwo : ℂ)*mellinFirst s L)]
  have htri := norm_add_le ((1 : ℂ)-(zetaTwo : ℂ)*mellinFirst s L)
    ((zetaTwo : ℂ)*mellinFirst s L)
  rw [sub_add_cancel, norm_one] at htri
  have htotal := htri.trans
    (add_le_add hroot (endpoint_norm_le s (by linarith) L (by omega)))
  apply (div_le_iff₀ (norm_pos_iff.mpr hs0)).mpr
  convert htotal using 1 <;> ring

end RiemannResearch.RH.QCRTExactEndpoint

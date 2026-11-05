/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeOddLift
import RiemannResearch.RH.QCompositeCarryDetection

/-! # The last composite charge of a sum of floor carries

Section 3.1 of *Prime trees, fractional parts, and zeta zeros* gives the finite
boundary and the vanishing of every fixed composite charge of the infinite
physical signal. Finite-site continuity suffices, without a Hilbert-norm limit.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
open ArithmeticCumulative Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QCompositeCarryDetection

variable (s : NormalizedCarryChain)

private def primeVector (K : ℕ) : QHilbert :=
  s.w 0 • qResidue (s.D 0) +
    ∑ k ∈ Finset.range K, (s.w (k+1) * (s.b k : ℝ)) • qResidue (s.p k)

private theorem primeVector_sequence (K n : ℕ) :
    qSequence (primeVector s K) n = s.parentTerm n 0 + ∑ k ∈ Finset.range K, s.primeTerm n k := by
  change qSequenceLinear _ n = _
  simp only [primeVector, map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change s.w 0 * qSequence (qResidue (s.D 0)) n +
    ∑ k ∈ Finset.range K, s.w (k+1) * (s.b k : ℝ) * qSequence (qResidue (s.p k)) n = _
  simp only [qSequence_qResidue, parentTerm, primeTerm]

private theorem primeVector_charge (m K : ℕ) (hm : 1 < m) (hn : ¬m.Prime)
    (hD : (s.D 0).Prime) (hp : ∀ k, (s.p k).Prime) :
    mobiusDifference m (qSequence (primeVector s K)) = 0 := by
  let L := (mobiusDifferenceCLM m).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference m (qSequence f) := by simp [L]
  have hz (p : ℕ) (h : p.Prime) : L (qResidue p) = 0 := by
    have hmp : m ≠ p := by
      rintro rfl
      exact hn h
    rw [he, charge_residue m p hm h.pos, if_neg hmp]
  rw [← he, primeVector, map_add, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul, hz _ hD, hz _ (hp _), mul_zero, Finset.sum_const_zero, add_zero]

/-- Exactly one composite boundary can survive in a finite partial sum. -/
theorem charge_partial_floors (m K : ℕ) (hm : 1 < m) (hn : ¬m.Prime)
    (hD : (s.D 0).Prime) (hp : ∀ k, (s.p k).Prime) :
    mobiusDifference m (fun n => ∑ k ∈ Finset.range K, s.carryTerm n k) =
      if m = s.D K then s.w K else 0 := by
  let L := (mobiusDifferenceCLM m).comp toParetoCLM
  have he (f : QHilbert) : L f = mobiusDifference m (qSequence f) := by simp [L]
  have hid : (fun n => ∑ k ∈ Finset.range K, s.carryTerm n k) =
      qSequence (primeVector s K - s.w K • qResidue (s.D K)) := by
    funext n
    rw [s.sum_carries]
    change _ = qSequenceLinear _ n
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change _ = qSequence (primeVector s K) n - s.w K * qSequence (qResidue (s.D K)) n
    rw [primeVector_sequence, qSequence_qResidue]
    rfl
  have hd : 0 < s.D K := (pow_pos (by decide : 0 < 2) K).trans_le (s.modulus_growth K)
  rw [hid, ← he, map_sub, map_smul, he, he, primeVector_charge s m K hm hn hD hp,
    charge_residue m (s.D K) hm hd]
  by_cases hmK : m = s.D K <;> simp [hmK]

/-- Every fixed composite charge of the infinite physical carry vanishes. -/
theorem charge_infinite_floors (m : ℕ) (hm : 1 < m) (hn : ¬m.Prime)
    (hD : (s.D 0).Prime) (hp : ∀ k, (s.p k).Prime) :
    mobiusDifference m (fun n => ∑' k, s.carryTerm n k) = 0 := by
  have hs (n : ℕ) : Tendsto (fun K => qSequence (primeVector s K) n) atTop
      (𝓝 (∑' k, s.carryTerm n k)) := by
    simp only [primeVector_sequence, (s.infinite_carry_expansion n).2.2]
    exact tendsto_const_nhds.add (s.infinite_carry_expansion n).1.hasSum.tendsto_sum_nat
  have hl := charge_tendsto_of_sites m (fun K => qSequence (primeVector s K))
    (fun n => ∑' k, s.carryTerm n k) (fun k _ => ⟨hs k, hs (k-1)⟩)
  apply tendsto_nhds_unique hl
  simpa only [primeVector_charge s m _ hm hn hD hp] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain

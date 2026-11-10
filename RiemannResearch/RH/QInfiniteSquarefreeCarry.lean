/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QInfiniteRecursiveCarry
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QPrimeCarryProjection
import RiemannResearch.RH.QCompositeCarryDetection
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Bertrand
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Absolute Hilbert convergence of squarefree CRT carry paths

Source: user-provided argument strengthening §13.3 by adjoining a prime
factor of `D + 1`. The proof retains the full finite boundary and identifies
the projected limit by the physical Möbius charges.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QCRTCarry
open QPrimeCarryProjection QCompositeCarryDetection Pareto

variable (s : NormalizedCarryChain)

/-- The remaining parent atom after the first `k` steps. -/
def qParentTerm (k : ℕ) : QHilbert := s.w k • qResidue (s.D k)

/-- The signed prime term on the synthesis side of the identity. -/
def qPrimeContribution (k : ℕ) : QHilbert :=
  (-(s.w (k + 1) * (s.b k : ℝ))) • qResidue (s.p k)

/-- The actual integer floor carry with its transport weight. -/
def qCarryTerm (k : ℕ) : QHilbert :=
  s.w (k + 1) • qCarry (s.D k) (s.p k) (s.a k) (s.b k)

private theorem root_mul_pow_le (k : ℕ) : s.D 0 * 2 ^ k ≤ s.D k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [s.next, pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_le_mul ih (s.radix_ge k)

private theorem conductor_pos (k : ℕ) : 0 < s.D k :=
  (Nat.mul_pos s.start_pos (pow_pos (by decide) k)).trans_le (s.root_mul_pow_le k)

theorem qCarry_step (k : ℕ) :
    s.qParentTerm k = s.qPrimeContribution k + s.qCarryTerm k + s.qParentTerm (k + 1) := by
  rw [qCarryTerm, qCarry_eq_linear (s.D k) (s.p k) (s.a k) (s.b k) 0
    (s.conductor_pos k) (lt_of_lt_of_le (by decide) (s.radix_ge k))
    (by simpa using s.bezout k), ← s.next k]
  simp only [qParentTerm, qPrimeContribution, smul_sub, smul_add, smul_smul,
    s.normalize, neg_smul]
  abel

/-- All intermediate parent atoms cancel, leaving the exact terminal boundary. -/
theorem qCarry_telescope (K : ℕ) :
    (∑ k ∈ Finset.range K, s.qPrimeContribution k) +
      (∑ k ∈ Finset.range K, s.qCarryTerm k) + s.qParentTerm K = s.qParentTerm 0 := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, s.qCarry_step k]
    abel

theorem qParentTerm_norm_sq_le (hroot : 2 ≤ s.D 0) (k : ℕ) :
    ‖s.qParentTerm k‖ ^ 2 ≤ 2 / (zetaTwo * (s.D k : ℝ)) := by
  have hd : 2 ≤ s.D k := by
    have hp : 1 ≤ (2 : ℕ) ^ k := pow_pos (by decide : 0 < (2 : ℕ)) k
    have h := Nat.mul_le_mul_left (s.D 0) hp
    rw [Nat.mul_one] at h
    exact hroot.trans (h.trans (s.root_mul_pow_le k))
  have hw : |s.w k| ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ (abs_nonneg (s.w k)) zero_le_one).mpr (s.weight_bound k)
  rw [qParentTerm, norm_smul, Real.norm_eq_abs, mul_pow]
  calc
    _ ≤ 1 * ‖qResidue (s.D k)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using qResidue_norm_sq_le_two_div (s.D k) hd

private theorem qPrimeCoefficient_bound (k : ℕ) :
    |s.w (k + 1) * (s.b k : ℝ)| ≤ 2 * (s.p k : ℝ) / (s.D k : ℝ) := by
  have hd : 0 < (s.D k : ℝ) := by exact_mod_cast s.conductor_pos k
  have hp : (2 : ℝ) ≤ s.p k := by exact_mod_cast s.radix_ge k
  have he : s.w (k + 1) * (s.b k : ℝ) * (s.D k : ℝ) =
      s.w (k + 1) - s.w k * (s.p k : ℝ) := by
    linear_combination s.w (k + 1) * s.bezout k - (s.p k : ℝ) * s.normalize k
  apply (le_div_iff₀ hd).2
  rw [← abs_of_nonneg hd.le, ← abs_mul, he]
  calc
    _ ≤ |s.w (k + 1)| + |s.w k * (s.p k : ℝ)| := abs_sub _ _
    _ ≤ 1 + (s.p k : ℝ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (s.p k) : (0 : ℝ) ≤ s.p k)]
      simpa only [one_mul] using add_le_add (s.weight_bound (k + 1))
        (mul_le_mul_of_nonneg_right (s.weight_bound k) (Nat.cast_nonneg (s.p k)))
    _ ≤ _ := by linarith

theorem qPrimeContribution_norm_sq_le (k : ℕ) (hradix : s.p k ≤ 2 * s.D k) :
    ‖s.qPrimeContribution k‖ ^ 2 ≤ 16 / (zetaTwo * (s.D k : ℝ)) := by
  have hZ := zetaTwo_pos
  have hd : 0 < (s.D k : ℝ) := by exact_mod_cast s.conductor_pos k
  have hp : 0 < (s.p k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (s.radix_ge k))
  have hle : (s.p k : ℝ) ≤ 2 * (s.D k : ℝ) := by exact_mod_cast hradix
  have hb := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (s.qPrimeCoefficient_bound k)
  rw [qPrimeContribution, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow]
  calc
    _ ≤ (2 * (s.p k : ℝ) / (s.D k : ℝ)) ^ 2 * (2 / (zetaTwo * (s.p k : ℝ))) :=
      mul_le_mul hb (qResidue_norm_sq_le_two_div (s.p k) (s.radix_ge k))
        (sq_nonneg _) (by positivity)
    _ = 8 * (s.p k : ℝ) / (zetaTwo * (s.D k : ℝ) ^ 2) := by
      field_simp [hZ.ne', hd.ne', hp.ne']
      ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hle
        (show 0 ≤ zetaTwo * (s.D k : ℝ) by positivity)]

private theorem norm_le_geometric {x : QHilbert} {A : ℝ} (hA : 0 ≤ A) (k : ℕ)
    (h : ‖x‖ ^ 2 ≤ A / (zetaTwo * (s.D k : ℝ))) :
    ‖x‖ ≤ Real.sqrt (A / (zetaTwo * (s.D 0 : ℝ))) * (Real.sqrt (1 / 2 : ℝ)) ^ k := by
  have hZ := zetaTwo_pos
  have hD : (s.D 0 : ℝ) * (2 : ℝ) ^ k ≤ s.D k := by exact_mod_cast s.root_mul_pow_le k
  have hroot : 0 < (s.D 0 : ℝ) := by exact_mod_cast s.start_pos
  have hr : ((Real.sqrt (1 / 2 : ℝ)) ^ k) ^ 2 = (1 / 2 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), hr]
  calc
    _ ≤ _ := h
    _ ≤ A / ((zetaTwo * (s.D 0 : ℝ)) * (2 : ℝ) ^ k) := by
      apply div_le_div_of_nonneg_left hA (by positivity)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hD zetaTwo_pos.le
    _ = _ := by
      have hp : (1 / (2 : ℝ)) ^ k = ((2 : ℝ) ^ k)⁻¹ := by rw [one_div, inv_pow]
      rw [hp]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem geometric_summable : Summable (fun k : ℕ => (Real.sqrt (1 / 2 : ℝ)) ^ k) := by
  apply summable_geometric_of_lt_one (Real.sqrt_nonneg _)
  simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)

/-- The terminal boundary decays at least as fast as `(1/√2)^k`. -/
theorem qParentTerm_norm_le (hroot : 2 ≤ s.D 0) (k : ℕ) :
    ‖s.qParentTerm k‖ ≤
      Real.sqrt (2 / (zetaTwo * (s.D 0 : ℝ))) * (Real.sqrt (1 / 2 : ℝ)) ^ k :=
  s.norm_le_geometric (by norm_num) k (s.qParentTerm_norm_sq_le hroot k)

theorem qParentTerm_norm_summable (hroot : 2 ≤ s.D 0) :
    Summable (fun k => ‖s.qParentTerm k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (s.qParentTerm_norm_le hroot)
    (geometric_summable.mul_left (Real.sqrt (2 / (zetaTwo * (s.D 0 : ℝ)))))

theorem qParentTerm_tendsto_zero (hroot : 2 ≤ s.D 0) :
    Tendsto s.qParentTerm atTop (𝓝 0) :=
  (s.qParentTerm_norm_summable hroot).of_norm.tendsto_atTop_zero

/-- Both signed series converge absolutely in the complete physical Q norm. -/
theorem qInfinite_carry_expansion (hroot : 2 ≤ s.D 0) (hradix : ∀ k, s.p k ≤ 2 * s.D k) :
    Summable (fun k => ‖s.qPrimeContribution k‖) ∧ Summable (fun k => ‖s.qCarryTerm k‖) ∧
      (∑' k, s.qPrimeContribution k) + (∑' k, s.qCarryTerm k) = s.qParentTerm 0 := by
  have hparent := s.qParentTerm_norm_summable hroot
  have hprime : Summable (fun k => ‖s.qPrimeContribution k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => s.norm_le_geometric (by norm_num) k (s.qPrimeContribution_norm_sq_le k (hradix k)))
      (geometric_summable.mul_left (Real.sqrt (16 / (zetaTwo * (s.D 0 : ℝ)))))
  have hshift : Summable (fun k => ‖s.qParentTerm (k + 1)‖) :=
    (summable_nat_add_iff 1).mpr hparent
  have hcarry : Summable (fun k => ‖s.qCarryTerm k‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((hparent.add hprime).add hshift)
    intro k
    have he : s.qCarryTerm k =
        (s.qParentTerm k - s.qPrimeContribution k) - s.qParentTerm (k + 1) := by
      rw [s.qCarry_step k]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  refine ⟨hprime, hcarry, ?_⟩
  have hl := (hprime.of_norm.hasSum.tendsto_sum_nat.add
    hcarry.of_norm.hasSum.tendsto_sum_nat).add (s.qParentTerm_tendsto_zero hroot)
  rw [add_zero] at hl
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr'
    (Eventually.of_forall fun K => (s.qCarry_telescope K).symm))

/-- The same prime and carry series converge absolutely in the complete Pareto norm. -/
theorem paretoInfinite_carry_expansion (hroot : 2 ≤ s.D 0)
    (hradix : ∀ k, s.p k ≤ 2 * s.D k) :
    Summable (fun k => ‖toPareto (s.qPrimeContribution k)‖) ∧
      Summable (fun k => ‖toPareto (s.qCarryTerm k)‖) ∧
      (∑' k, toPareto (s.qPrimeContribution k)) + (∑' k, toPareto (s.qCarryTerm k)) =
        toPareto (s.qParentTerm 0) := by
  obtain ⟨hp, hc, he⟩ := s.qInfinite_carry_expansion hroot hradix
  have hs (f : ℕ → QHilbert) (hf : Summable (fun k => ‖f k‖)) :
      Summable (fun k => ‖toPareto (f k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => toPareto_norm_le (f k))
      (hf.mul_left (Real.sqrt zetaTwo))
  refine ⟨hs _ hp, hs _ hc, ?_⟩
  change (∑' k, toParetoCLM (s.qPrimeContribution k)) +
    (∑' k, toParetoCLM (s.qCarryTerm k)) = toParetoCLM (s.qParentTerm 0)
  rw [← toParetoCLM.map_tsum hp.of_norm, ← toParetoCLM.map_tsum hc.of_norm, ← map_add, he]

/-- The prime projection removes the entire prime synthesis, so the projected
carry series retains the projected root. -/
theorem projected_qCarry_sum (hroot : 2 ≤ s.D 0) (hradix : ∀ k, s.p k ≤ 2 * s.D k)
    (hprime : ∀ k, (s.p k).Prime) :
    (∑' k, primeClosureᗮ.starProjection (s.qCarryTerm k)) =
      primeClosureᗮ.starProjection (s.qParentTerm 0) := by
  obtain ⟨hp, hc, he⟩ := s.qInfinite_carry_expansion hroot hradix
  let P := primeClosureᗮ.starProjection
  have hz (k : ℕ) : P (s.qPrimeContribution k) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero
      (primeClosure.smul_mem _ (qResidue_mem_primeClosure (s.p k) (hprime k)))
  have h := congrArg P he
  rw [map_add, P.map_tsum hp.of_norm, P.map_tsum hc.of_norm] at h
  simpa only [hz, tsum_zero, zero_add] using h

private def qCharge (d : ℕ) : QHilbert →L[ℝ] ℝ :=
  (mobiusDifferenceCLM d).comp toParetoCLM

private theorem qCharge_apply (d : ℕ) (f : QHilbert) :
    qCharge d f = mobiusDifference d (qSequence f) := by
  simp [qCharge]

private theorem primeClosure_le_charge_ker (d : ℕ) (hd : 1 < d) (hn : ¬d.Prime) :
    primeClosure ≤ (qCharge d).ker := by
  have hspan : QSimultaneousCRT.primeSpan ≤ (qCharge d).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    have hne : d ≠ p := fun h => hn (h.symm ▸ hp)
    change qCharge d (qResidue p) = 0
    rw [qCharge_apply, charge_residue d p hd hp.pos, if_neg hne]
  exact QSimultaneousCRT.primeSpan.topologicalClosure_minimal hspan (qCharge d).isClosed_ker

/-- Every composite charge is unchanged when the prime projection is removed. -/
theorem composite_charge_projected_qResidue (d r : ℕ) (hd : 1 < d) (hn : ¬d.Prime)
    (hr : 0 < r) :
    mobiusDifference d (qSequence (primeClosureᗮ.starProjection (qResidue r))) =
      if d = r then -1 else 0 := by
  have hz : qCharge d (primeClosure.starProjection (qResidue r)) = 0 :=
    primeClosure_le_charge_ker d hd hn (primeClosure.starProjection_apply_mem (qResidue r))
  rw [← qCharge_apply, Submodule.starProjection_orthogonal_val, map_sub, hz, sub_zero,
    qCharge_apply, charge_residue d r hd hr]

/-- For a unit initial weight, the projected carry sum vanishes exactly at prime roots. -/
theorem projected_qCarry_sum_eq_zero_iff (hroot : 2 ≤ s.D 0)
    (hradix : ∀ k, s.p k ≤ 2 * s.D k) (hprime : ∀ k, (s.p k).Prime) (hw : s.w 0 = 1) :
    (∑' k, primeClosureᗮ.starProjection (s.qCarryTerm k)) = 0 ↔ (s.D 0).Prime := by
  rw [s.projected_qCarry_sum hroot hradix hprime, qParentTerm, hw, one_smul]
  refine ⟨?_, fun hp => Submodule.starProjection_orthogonal_apply_eq_zero
    (qResidue_mem_primeClosure (s.D 0) hp)⟩
  intro hz
  by_contra hn
  have he := composite_charge_projected_qResidue (s.D 0) (s.D 0) hroot hn s.start_pos
  rw [← qCharge_apply, hz, map_zero, if_pos rfl] at he
  norm_num at he

/-- A squarefree root stays squarefree when each incoming prime is fresh. -/
theorem squarefree_conductors (hroot : Squarefree (s.D 0))
    (hprime : ∀ k, (s.p k).Prime) (hfresh : ∀ k, ¬s.p k ∣ s.D k) (k : ℕ) :
    Squarefree (s.D k) := by
  induction k with
  | zero => exact hroot
  | succ k ih =>
    rw [s.next]
    exact Nat.squarefree_mul_iff.mpr
      ⟨((hprime k).coprime_iff_not_dvd.mpr (hfresh k)).symm,
        ih, Irreducible.squarefree (hprime k)⟩

end RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain

namespace RiemannResearch.RH.CRTCarryArithmetic

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QPrimeCarryProjection

private def pathConductor (radix : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => r
  | k + 1 => pathConductor radix r k * radix (pathConductor radix r k)

private theorem pathConductor_two_le (radix : ℕ → ℕ) (hpos : ∀ d, 0 < radix d)
    (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : 2 ≤ pathConductor radix r k := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    rw [pathConductor]
    exact ih.trans (Nat.le_mul_of_pos_right _ (hpos _))

private def pathWeight (a : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pathWeight a k / (a k : ℝ)

private theorem pathWeight_pos (a : ℕ → ℕ) (ha : ∀ k, 0 < a k) (k : ℕ) :
    0 < pathWeight a k := by
  induction k with
  | zero => norm_num [pathWeight]
  | succ k ih => exact div_pos ih (Nat.cast_pos.mpr (ha k))

private theorem pathWeight_succ_le (a : ℕ → ℕ) (ha : ∀ k, 0 < a k) (k : ℕ) :
    pathWeight a (k + 1) ≤ pathWeight a k := by
  apply div_le_self (pathWeight_pos a ha k).le
  exact_mod_cast ha k

private theorem pathWeight_abs_le_one (a : ℕ → ℕ) (ha : ∀ k, 0 < a k) (k : ℕ) :
    |pathWeight a k| ≤ 1 := by
  induction k with
  | zero => simp [pathWeight]
  | succ k ih =>
    rw [abs_of_pos (pathWeight_pos a ha _)] at ih ⊢
    exact (pathWeight_succ_le a ha k).trans ih

private abbrev euclidConductor := pathConductor (fun d => (d + 1).minFac)

private def euclidPrime (r k : ℕ) : ℕ := (euclidConductor r k + 1).minFac

private def euclidMultiplier (r k : ℕ) : ℕ := (euclidConductor r k + 1) / euclidPrime r k

private theorem euclidConductor_two_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    2 ≤ euclidConductor r k :=
  pathConductor_two_le _ (fun _ => Nat.minFac_pos _) r hr k

private theorem euclidPrime_prime (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : (euclidPrime r k).Prime := by
  have := euclidConductor_two_le r hr k
  exact Nat.minFac_prime (by omega)

private theorem euclidMultiplier_mul (r k : ℕ) :
    euclidMultiplier r k * euclidPrime r k = euclidConductor r k + 1 :=
  Nat.div_mul_cancel (Nat.minFac_dvd _)

private theorem euclidMultiplier_pos (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    0 < euclidMultiplier r k := by
  apply Nat.div_pos _ (euclidPrime_prime r hr k).pos
  exact Nat.le_of_dvd (by omega) (Nat.minFac_dvd _)

/-- Adjoin the smallest prime factor of `D + 1` and use the integral pair
`((D + 1) / p, -1)` at every step. -/
def euclidChain (r : ℕ) (hr : 2 ≤ r) : NormalizedCarryChain where
  D := euclidConductor r
  p := euclidPrime r
  a := fun k => (euclidMultiplier r k : ℤ)
  b := fun _ => -1
  w := pathWeight (euclidMultiplier r)
  start_pos := lt_of_lt_of_le (by decide) hr
  radix_ge k := (euclidPrime_prime r hr k).two_le
  next _ := rfl
  bezout k := by
    have h : (euclidMultiplier r k : ℝ) * (euclidPrime r k : ℝ) =
        (euclidConductor r k : ℝ) + 1 := by exact_mod_cast euclidMultiplier_mul r k
    push_cast
    linarith only [h]
  normalize k := by
    rw [pathWeight, Int.cast_natCast, div_mul_cancel₀ _
      (Nat.cast_pos.mpr (euclidMultiplier_pos r hr k)).ne']
  weight_bound := pathWeight_abs_le_one _ (euclidMultiplier_pos r hr)

@[simp] theorem euclidChain_D_zero (r : ℕ) (hr : 2 ≤ r) : (euclidChain r hr).D 0 = r := rfl

@[simp] theorem euclidChain_w_zero (r : ℕ) (hr : 2 ≤ r) : (euclidChain r hr).w 0 = 1 := rfl

theorem euclidChain_prime (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : ((euclidChain r hr).p k).Prime :=
  euclidPrime_prime r hr k

theorem euclidChain_prime_dvd (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (euclidChain r hr).p k ∣ (euclidChain r hr).D k + 1 :=
  Nat.minFac_dvd _

theorem euclidChain_prime_not_dvd (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ¬(euclidChain r hr).p k ∣ (euclidChain r hr).D k := by
  intro h
  have h1 : (euclidChain r hr).p k ∣ 1 := by
    simpa using Nat.dvd_sub (euclidChain_prime_dvd r hr k) h
  exact (euclidChain_prime r hr k).ne_one (Nat.dvd_one.mp h1)

theorem euclidChain_squarefree (r : ℕ) (hr : 2 ≤ r) (hsq : Squarefree r) (k : ℕ) :
    Squarefree ((euclidChain r hr).D k) :=
  (euclidChain r hr).squarefree_conductors hsq
    (euclidChain_prime r hr) (euclidChain_prime_not_dvd r hr) k

theorem euclidChain_radix_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (euclidChain r hr).p k ≤ 2 * (euclidChain r hr).D k := by
  have hd := euclidConductor_two_le r hr k
  have hp : euclidPrime r k ≤ euclidConductor r k + 1 :=
    Nat.le_of_dvd (by omega) (euclidChain_prime_dvd r hr k)
  change euclidPrime r k ≤ 2 * euclidConductor r k
  omega

theorem euclidChain_weight_pos (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : 0 < (euclidChain r hr).w k :=
  pathWeight_pos _ (euclidMultiplier_pos r hr) k

theorem euclidChain_weight_succ_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (euclidChain r hr).w (k + 1) ≤ (euclidChain r hr).w k :=
  pathWeight_succ_le _ (euclidMultiplier_pos r hr) k

theorem euclidChain_primeContribution (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (euclidChain r hr).qPrimeContribution k =
      (euclidChain r hr).w (k + 1) • qResidue ((euclidChain r hr).p k) := by
  simp [NormalizedCarryChain.qPrimeContribution, euclidChain]

/-- The `D + 1` construction has the sharper prime bound of the explicit path. -/
theorem euclidChain_prime_norm_sq_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    let s := euclidChain r hr
    ‖s.qPrimeContribution k‖ ^ 2 ≤ 2 / (zetaTwo * ((s.D k : ℝ) + 1)) := by
  let s := euclidChain r hr
  change ‖s.qPrimeContribution k‖ ^ 2 ≤ _
  have hZ := ZetaTwoProbability.zetaTwo_pos
  have hd : 0 < (s.D k : ℝ) + 1 := by positivity
  have hp : 0 < (s.p k : ℝ) := by exact_mod_cast (euclidChain_prime r hr k).pos
  have hpd : s.p k ≤ s.D k + 1 :=
    Nat.le_of_dvd (Nat.succ_pos _) (euclidChain_prime_dvd r hr k)
  have hle : (s.p k : ℝ) ≤ (s.D k : ℝ) + 1 := by exact_mod_cast hpd
  have hmul : (s.a k : ℝ) * (s.p k : ℝ) = (s.D k : ℝ) + 1 := by
    change ((euclidMultiplier r k : ℤ) : ℝ) * (euclidPrime r k : ℝ) =
      (euclidConductor r k : ℝ) + 1
    rw [Int.cast_natCast]
    exact_mod_cast euclidMultiplier_mul r k
  have hw (j : ℕ) : s.w j ≤ 1 :=
    (le_abs_self _).trans (s.weight_bound j)
  have hw' : s.w (k + 1) ≤ (s.p k : ℝ) / ((s.D k : ℝ) + 1) := by
    apply (le_div_iff₀ hd).mpr
    rw [← hmul, ← mul_assoc, s.normalize k]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw k) hp.le
  have hpos : 0 < s.w (k + 1) := euclidChain_weight_pos r hr (k + 1)
  have hsq := (sq_le_sq₀ hpos.le (by positivity)).mpr hw'
  rw [euclidChain_primeContribution, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, mul_pow]
  calc
    _ ≤ ((s.p k : ℝ) / ((s.D k : ℝ) + 1)) ^ 2 * (2 / (zetaTwo * (s.p k : ℝ))) :=
      mul_le_mul hsq (qResidue_norm_sq_le_two_div _ (s.radix_ge k))
        (sq_nonneg _) (by positivity)
    _ = 2 * (s.p k : ℝ) / (zetaTwo * ((s.D k : ℝ) + 1) ^ 2) := by
      field_simp [hZ.ne', hp.ne', hd.ne'] <;> ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hle
        (show 0 ≤ zetaTwo * ((s.D k : ℝ) + 1) by positivity)]

/-- The concrete `D + 1` path expands its root with absolute convergence in Q. -/
theorem euclidChain_q_expansion (r : ℕ) (hr : 2 ≤ r) :
    let s := euclidChain r hr
    Summable (fun k => ‖s.qPrimeContribution k‖) ∧ Summable (fun k => ‖s.qCarryTerm k‖) ∧
      (∑' k, s.qPrimeContribution k) + (∑' k, s.qCarryTerm k) = qResidue r := by
  simpa only [NormalizedCarryChain.qParentTerm, euclidChain_D_zero, euclidChain_w_zero,
    one_smul] using (euclidChain r hr).qInfinite_carry_expansion hr (euclidChain_radix_le r hr)

/-- The concrete expansion in the complete Pareto norm. -/
theorem euclidChain_pareto_expansion (r : ℕ) (hr : 2 ≤ r) :
    let s := euclidChain r hr
    Summable (fun k => ‖toPareto (s.qPrimeContribution k)‖) ∧
      Summable (fun k => ‖toPareto (s.qCarryTerm k)‖) ∧
      (∑' k, toPareto (s.qPrimeContribution k)) + (∑' k, toPareto (s.qCarryTerm k)) =
        toPareto (qResidue r) := by
  simpa only [NormalizedCarryChain.qParentTerm, euclidChain_D_zero, euclidChain_w_zero,
    one_smul] using
    (euclidChain r hr).paretoInfinite_carry_expansion hr (euclidChain_radix_le r hr)

theorem euclidChain_projected_carry_sum (r : ℕ) (hr : 2 ≤ r) :
    (∑' k, primeClosureᗮ.starProjection ((euclidChain r hr).qCarryTerm k)) =
      primeClosureᗮ.starProjection (qResidue r) := by
  simpa only [NormalizedCarryChain.qParentTerm, euclidChain_D_zero, euclidChain_w_zero,
    one_smul] using (euclidChain r hr).projected_qCarry_sum hr
      (euclidChain_radix_le r hr) (euclidChain_prime r hr)

theorem euclidChain_projected_carry_eq_zero_iff (r : ℕ) (hr : 2 ≤ r) :
    (∑' k, primeClosureᗮ.starProjection ((euclidChain r hr).qCarryTerm k)) = 0 ↔ r.Prime :=
  (euclidChain r hr).projected_qCarry_sum_eq_zero_iff hr
    (euclidChain_radix_le r hr) (euclidChain_prime r hr) (euclidChain_w_zero r hr)

private def PrimeAboveFactors (d p : ℕ) : Prop :=
  p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ d → q < p

private theorem exists_primeAboveFactors_le {d : ℕ} (hd : 0 < d) :
    ∃ p, PrimeAboveFactors d p ∧ p ≤ 2 * d := by
  obtain ⟨p, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul d hd.ne'
  exact ⟨p, ⟨hp, fun _ _ hq => (Nat.le_of_dvd hd hq).trans_lt hgt⟩, hle⟩

private theorem exists_primeAboveFactors {d : ℕ} (hd : 0 < d) :
    ∃ p, PrimeAboveFactors d p :=
  (exists_primeAboveFactors_le hd).imp fun _ h => h.1

private def orderedRadix (d : ℕ) : ℕ := by
  classical
  exact if hd : 0 < d then Nat.find (exists_primeAboveFactors hd) else 2

private theorem orderedRadix_spec {d : ℕ} (hd : 0 < d) :
    PrimeAboveFactors d (orderedRadix d) := by
  classical
  rw [orderedRadix, dif_pos hd]
  exact Nat.find_spec (exists_primeAboveFactors hd)

private theorem orderedRadix_min {d p : ℕ} (hd : 0 < d) (hp : PrimeAboveFactors d p) :
    orderedRadix d ≤ p := by
  classical
  rw [orderedRadix, dif_pos hd]
  exact Nat.find_min' (exists_primeAboveFactors hd) hp

private theorem orderedRadix_pos (d : ℕ) : 0 < orderedRadix d := by
  by_cases hd : 0 < d
  · exact (orderedRadix_spec hd).1.pos
  · simp [orderedRadix, hd]

private abbrev orderedConductor := pathConductor orderedRadix

private theorem orderedConductor_two_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    2 ≤ orderedConductor r k :=
  pathConductor_two_le orderedRadix orderedRadix_pos r hr k

private theorem orderedConductor_pos (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    0 < orderedConductor r k :=
  lt_of_lt_of_le (by decide) (orderedConductor_two_le r hr k)

private theorem orderedInverse_exists (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ∃ a : ℕ, a < orderedConductor r k ∧
      orderedRadix (orderedConductor r k) * a % orderedConductor r k = 1 := by
  have hp := orderedRadix_spec (orderedConductor_pos r hr k)
  have hcop := hp.1.coprime_iff_not_dvd.mpr fun h => (lt_irrefl _) (hp.2 _ hp.1 h)
  exact Nat.exists_mul_mod_eq_one_of_coprime hcop (orderedConductor_two_le r hr k)

private def orderedMultiplier (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : ℕ :=
  Nat.find (orderedInverse_exists r hr k)

private theorem orderedMultiplier_mod (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    orderedRadix (orderedConductor r k) * orderedMultiplier r hr k % orderedConductor r k = 1 :=
  (Nat.find_spec (orderedInverse_exists r hr k)).2

private theorem orderedMultiplier_pos (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    0 < orderedMultiplier r hr k := by
  by_contra! h
  have hz : orderedMultiplier r hr k = 0 := by omega
  simpa [hz] using orderedMultiplier_mod r hr k

/-- The path taking the least prime above every prime factor of its current
conductor. Deleting that largest factor recovers the parent. -/
def orderedChain (r : ℕ) (hr : 2 ≤ r) : NormalizedCarryChain where
  D := orderedConductor r
  p := fun k => orderedRadix (orderedConductor r k)
  a := fun k => (orderedMultiplier r hr k : ℤ)
  b := fun k => -((orderedRadix (orderedConductor r k) * orderedMultiplier r hr k /
    orderedConductor r k : ℕ) : ℤ)
  w := pathWeight (orderedMultiplier r hr)
  start_pos := lt_of_lt_of_le (by decide) hr
  radix_ge k := (orderedRadix_spec (orderedConductor_pos r hr k)).1.two_le
  next _ := rfl
  bezout k := by
    have hn := Nat.mod_add_div (orderedRadix (orderedConductor r k) * orderedMultiplier r hr k)
      (orderedConductor r k)
    rw [orderedMultiplier_mod r hr k] at hn
    have he := congrArg (fun n : ℕ => (n : ℝ)) hn
    push_cast at he
    simp only [Int.cast_natCast, Int.cast_neg]
    linarith only [he]
  normalize k := by
    rw [pathWeight, Int.cast_natCast, div_mul_cancel₀ _
      (Nat.cast_pos.mpr (orderedMultiplier_pos r hr k)).ne']
  weight_bound := pathWeight_abs_le_one _ (orderedMultiplier_pos r hr)

@[simp] theorem orderedChain_D_zero (r : ℕ) (hr : 2 ≤ r) : (orderedChain r hr).D 0 = r := rfl

@[simp] theorem orderedChain_w_zero (r : ℕ) (hr : 2 ≤ r) : (orderedChain r hr).w 0 = 1 := rfl

theorem orderedChain_least_prime (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    let s := orderedChain r hr
    (s.p k).Prime ∧ (∀ q : ℕ, q.Prime → q ∣ s.D k → q < s.p k) ∧
      ∀ p : ℕ, p.Prime → (∀ q : ℕ, q.Prime → q ∣ s.D k → q < p) → s.p k ≤ p := by
  have hd := orderedConductor_pos r hr k
  have h := orderedRadix_spec hd
  exact ⟨h.1, h.2, fun _ hp hf => orderedRadix_min hd ⟨hp, hf⟩⟩

theorem orderedChain_radix_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (orderedChain r hr).p k ≤ 2 * (orderedChain r hr).D k := by
  have hd := orderedConductor_pos r hr k
  obtain ⟨p, hp, hle⟩ := exists_primeAboveFactors_le hd
  exact (orderedRadix_min hd hp).trans hle

theorem orderedChain_squarefree (r : ℕ) (hr : 2 ≤ r) (hsq : Squarefree r) (k : ℕ) :
    Squarefree ((orderedChain r hr).D k) := by
  apply (orderedChain r hr).squarefree_conductors hsq
    (fun j => (orderedChain_least_prime r hr j).1) _ k
  intro j h
  obtain ⟨hp, hgt, _⟩ := orderedChain_least_prime r hr j
  exact (lt_irrefl _) (hgt _ hp h)

/-- Absolute convergence on the largest-prime deletion tree. -/
theorem orderedChain_q_expansion (r : ℕ) (hr : 2 ≤ r) :
    let s := orderedChain r hr
    Summable (fun k => ‖s.qPrimeContribution k‖) ∧ Summable (fun k => ‖s.qCarryTerm k‖) ∧
      (∑' k, s.qPrimeContribution k) + (∑' k, s.qCarryTerm k) = qResidue r := by
  simpa only [NormalizedCarryChain.qParentTerm, orderedChain_D_zero, orderedChain_w_zero,
    one_smul] using (orderedChain r hr).qInfinite_carry_expansion hr (orderedChain_radix_le r hr)

theorem orderedChain_pareto_expansion (r : ℕ) (hr : 2 ≤ r) :
    let s := orderedChain r hr
    Summable (fun k => ‖toPareto (s.qPrimeContribution k)‖) ∧
      Summable (fun k => ‖toPareto (s.qCarryTerm k)‖) ∧
      (∑' k, toPareto (s.qPrimeContribution k)) + (∑' k, toPareto (s.qCarryTerm k)) =
        toPareto (qResidue r) := by
  simpa only [NormalizedCarryChain.qParentTerm, orderedChain_D_zero, orderedChain_w_zero,
    one_smul] using
    (orderedChain r hr).paretoInfinite_carry_expansion hr (orderedChain_radix_le r hr)

end RiemannResearch.RH.CRTCarryArithmetic

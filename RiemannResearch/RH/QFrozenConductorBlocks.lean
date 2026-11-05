/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MobiusHeadCoercivity
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.RH.QDivisorHeadCoercivity
import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QPhysicalTailEnergy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecificLimits.Normed
import RiemannResearch.RH.QSquarefreeResponseSeries

/-! # Frozen conductor estimates on physical LCM blocks

Source: user-proposed LCM cutoffs. Möbius coercivity and the elementary Chebyshev
bound give summable eighth-power masses across matched finite fits. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.Analysis.FiniteDivisorCoercivity
open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability

/-- A finite conductor stage controls all physical sites by its own finite head. -/
theorem frozen_conductor_site_sq_le (M : ℕ) (hM : 1 ≤ M)
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ M) (n : ℕ) :
    normalizedResidueSynthesis s c n ^ 2 ≤
      ((headDifferenceFactor M * mobiusMass M) ^ 2 *
        energy M (fun k => normalizedResidueSynthesis s c k / (k : ℝ))) *
        ∑ d ∈ s, (d : ℝ) ^ 2 := by
  let a := fun d : ℕ => c d / (d : ℝ)
  let b := fun d : ℕ => (d : ℝ) * residueFraction d n
  have hid : normalizedResidueSynthesis s c n = ∑ d ∈ s, a d * b d := by
    apply Finset.sum_congr rfl
    intro d hd
    have h : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by have := (hs d hd).1; omega)
    dsimp only [a, b]
    field_simp
  have ha := normalizedResidueSynthesis_full_coercivity M hM s c hs
  have ha' : (∑ d ∈ s, a d ^ 2) ≤ (headDifferenceFactor M * mobiusMass M) ^ 2 *
        energy M (fun k => normalizedResidueSynthesis s c k / (k : ℝ)) := by
    exact (le_add_of_nonneg_left (sq_nonneg _)).trans ha
  have hb : (∑ d ∈ s, b d ^ 2) ≤ ∑ d ∈ s, (d : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have h0 := CRTCarryArithmetic.residueFraction_nonneg d n
    have h1 := (CRTCarryArithmetic.residueFraction_lt_one d n (by have := (hs d hd).1; omega)).le
    have hle : b d ≤ (d : ℝ) := by
      simpa only [b, mul_one] using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d (α := ℝ))
    exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) h0) hle 2
  rw [hid]
  exact (Finset.sum_mul_sq_le_sq_mul_sq s a b).trans <|
    mul_le_mul ha' hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (energy_nonneg _ _))

end RiemannResearch.RH.CRTBlock

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.Analysis.FiniteDivisorCoercivity
open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QDivisorHeadCoercivity QHeadGramCoercivity QFiniteSupportDualCriterion
open QSquarefreeFiniteDisplacement

private theorem stage_frozen_synthesis (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    ∃ c : ℕ → ℝ, QDivisorHeadCoercivity.qSynthesis (Finset.Icc 2 (N + 1)) c = v := by
  classical
  rw [← QSquarefreeInverseCapacity.residue_span_eq_stage] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    let m := QSquarefreeInverseCapacity.conductor N i
    have hm : m ∈ Finset.Icc 2 (N + 1) := Finset.mem_Icc.mpr ⟨by
      dsimp [m, QSquarefreeInverseCapacity.conductor]; omega, by
      dsimp [m, QSquarefreeInverseCapacity.conductor]; have := i.val.isLt; omega⟩
    refine ⟨fun d => if m = d then 1 else 0, ?_⟩
    change (∑ d ∈ Finset.Icc 2 (N + 1), (if m = d then (1 : ℝ) else 0) • qResidue d) = qResidue m
    simpa [ite_smul, hm]
  | zero => exact ⟨fun _ => 0, by simp [QDivisorHeadCoercivity.qSynthesis]⟩
  | add x y hx hy ix iy =>
    obtain ⟨a, rfl⟩ := ix
    obtain ⟨b, rfl⟩ := iy
    exact ⟨fun d => a d + b d, by simp only [QDivisorHeadCoercivity.qSynthesis, add_smul,
      Finset.sum_add_distrib]⟩
  | smul c x hx ix =>
    obtain ⟨a, rfl⟩ := ix
    exact ⟨fun d => c * a d, by simp only [QDivisorHeadCoercivity.qSynthesis, mul_smul,
      Finset.smul_sum]⟩

def frozenStageFactor (N : ℕ) : ℝ :=
  (headDifferenceFactor (N + 1) * mobiusMass (N + 1)) ^ 2 *
    zetaTwo * ∑ d ∈ Finset.Icc 2 (N + 1), (d : ℝ) ^ 2

theorem frozen_stage_site (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) (n : ℕ) :
    (qSequence v n) ^ 2 ≤ frozenStageFactor N * ‖v‖ ^ 2 := by
  obtain ⟨c, hc⟩ := stage_frozen_synthesis N v hv
  have hseq := qSequence_qSynthesis (Finset.Icc 2 (N + 1)) c
  rw [hc] at hseq
  have h := frozen_conductor_site_sq_le (N + 1) (by omega) _ c
    (fun d hd => Finset.mem_Icc.mp hd) n
  rw [← hseq] at h
  unfold energy at h
  rw [physical_head_energy] at h
  have hnorm := QFiniteSupportDualCriterion.finiteHead_norm_le (N + 1) v
  let u := (headDifferenceFactor (N + 1) * mobiusMass (N + 1)) ^ 2
  let w := ∑ d ∈ Finset.Icc 2 (N + 1), (d : ℝ) ^ 2
  have hu : 0 ≤ u := sq_nonneg _
  have hz : 0 ≤ zetaTwo := zetaTwo_pos.le
  have hw : 0 ≤ w := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ (u * (zetaTwo * ‖finiteHead (N + 1) v‖ ^ 2)) * w := h
    _ ≤ (u * (zetaTwo * ‖v‖ ^ 2)) * w := by gcongr
    _ = _ := by dsimp only [frozenStageFactor, u, w]; ring

/-- Physical block [A, A + T), including the first point A. -/
theorem frozen_stage_eighth_block (N A T : ℕ) (hA : 0 < A) (v : QHilbert)
    (hv : v ∈ stage N) :
    (∑ k ∈ Finset.range T, |qSequence v (k + A)| ^ 8 / ((k + A : ℕ) : ℝ) ^ 2) ≤
      (frozenStageFactor N * ‖v‖ ^ 2) ^ 4 * (2 / (A : ℝ)) := by
  let C := (frozenStageFactor N * ‖v‖ ^ 2) ^ 4
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have summ (n : ℕ) (hn : 0 < n) : 1 / (n : ℝ) ^ 2 ≤ 2 * Pareto.positiveWeight n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hp : 0 < (n : ℝ) := by exact_mod_cast hn
    have hp' : 0 < (n : ℝ) + 1 := by positivity
    simp only [Pareto.positiveWeight]
    field_simp
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h1)]
  have hmass := ((summable_nat_add_iff A).mpr Pareto.positiveWeight_summable).sum_le_tsum
    (Finset.range T) (fun k _ => Pareto.positiveWeight_nonneg (k + A))
  rw [Pareto.positiveWeight_tail_tsum A hA] at hmass
  calc
    _ ≤ ∑ k ∈ Finset.range T, C * (2 * Pareto.positiveWeight (k + A)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpow := pow_le_pow_left₀ (sq_nonneg (qSequence v (k + A)))
        (frozen_stage_site N v hv (k + A)) 4
      have h8 : |qSequence v (k + A)| ^ 8 ≤ C := by
        rw [Even.pow_abs (by decide : Even 8)]
        simpa only [C, ← pow_mul] using hpow
      rw [div_eq_mul_one_div]
      exact mul_le_mul h8 (summ (k + A) (by omega)) (by positivity) hC
    _ = C * (2 * ∑ k ∈ Finset.range T, Pareto.positiveWeight (k + A)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
      change C * _ ≤ C * _
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hmass (by norm_num : (0: ℝ) ≤ 2)

/-- An unconditional block bound for the matched displacement at fixed stage N. -/
theorem frozen_finiteDisplacement_eighth_block (N A T : ℕ) (hA : 0 < A) :
    (∑ k ∈ Finset.range T, |qSequence (finiteDisplacement N) (k + A)| ^ 8 /
      ((k + A : ℕ) : ℝ) ^ 2) ≤
      (frozenStageFactor N * ‖finiteDisplacement N‖ ^ 2) ^ 4 * (2 / (A : ℝ)) :=
  frozen_stage_eighth_block N A T hA _ (finiteDisplacement_mem N)

end RiemannResearch.RH.CRTBlock

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.Analysis.FiniteDivisorCoercivity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSquarefreeFiniteDisplacement

theorem frozenStageFactor_polynomial (N : ℕ) :
    frozenStageFactor N ≤ (4 * zetaTwo) * ((N + 1 : ℕ) : ℝ) ^ 5 := by
  have hz : 0 ≤ zetaTwo := zetaTwo_pos.le
  let M := N + 1
  have hm : 1 ≤ M := by dsimp [M]; omega
  have hmp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hμ : mobiusMass M ≤ (M : ℝ) :=
    (mobiusMass_le_log M).trans (by linarith [Real.log_le_sub_one_of_pos hmp])
  have hprod : headDifferenceFactor M * mobiusMass M ≤ 2 * (M : ℝ) :=
    mul_le_mul (headDifferenceFactor_bounds M hm).2.le hμ (mobiusMass_nonneg M) (by norm_num)
  have hprod0 : 0 ≤ headDifferenceFactor M * mobiusMass M :=
    mul_nonneg (by linarith [(headDifferenceFactor_bounds M hm).1]) (mobiusMass_nonneg M)
  have hsum : (∑ d ∈ Finset.Icc 2 M, (d : ℝ) ^ 2) ≤ (M : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 2 M, (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact pow_le_pow_left₀ (Nat.cast_nonneg d)
          (by exact_mod_cast (Finset.mem_Icc.mp hd).2) 2
      _ = ((Finset.Icc 2 M).card : ℝ) * (M : ℝ) ^ 2 := by simp
      _ ≤ (M : ℝ) * (M : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast (show (Finset.Icc 2 M).card ≤ M by rw [Nat.card_Icc]; omega)
      _ = _ := by ring
  change (headDifferenceFactor M * mobiusMass M) ^ 2 * zetaTwo *
    (∑ d ∈ Finset.Icc 2 M, (d : ℝ) ^ 2) ≤ _
  calc
    _ ≤ (2 * (M: ℝ)) ^ 2 * zetaTwo * (M: ℝ) ^ 3 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hprod0 hprod 2) zetaTwo_pos.le)
        hsum (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by positivity)
    _ = _ := by change _ = 4 * zetaTwo * (M : ℝ) ^ 5; ring

/-- Even the sum over all successive frozen stages is finite, for arbitrary
block lengths. The physical eighth moment is always that of its own stage. -/
theorem frozen_lcm_displacement_summable (T : ℕ → ℕ) :
    Summable (fun N : ℕ => ∑ k ∈ Finset.range (T N),
      |qSequence (finiteDisplacement N) (k + Nat.lcmUpto (N + 1))| ^ 8 /
        ((k + Nat.lcmUpto (N + 1) : ℕ) : ℝ) ^ 2) := by
  have hz : 0 ≤ zetaTwo := zetaTwo_pos.le
  let C := 4 * (4 * zetaTwo) ^ 4
  have hs : Summable (fun m : ℕ => C * ((m : ℝ) ^ 21 * (1 / 2: ℝ) ^ m)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 21 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C
  apply Summable.of_nonneg_of_le (fun N => Finset.sum_nonneg fun n _ => by positivity)
    _ ((summable_nat_add_iff 1).mpr hs)
  intro N
  let M := N + 1
  let A := Nat.lcmUpto M
  have hm : 1 ≤ M := by dsimp [M]; omega
  have hmR : (1 : ℝ) ≤ M := by exact_mod_cast hm
  have hL : (2: ℝ) ^ M ≤ ((M: ℝ) + 1) * A := by
    exact_mod_cast Chebyshev.two_pow_le_mul_lcmUpto M
  have hpow : (0 : ℝ) < (2: ℝ) ^ M := by positivity
  have hA : 0 < A := by
    by_contra! hn
    have he : A = 0 := by omega
    rw [he, Nat.cast_zero, mul_zero] at hL
    exact (not_lt_of_ge hL) hpow
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hrec : 2 / (A : ℝ) ≤ (4 * (M : ℝ)) * (1 / 2: ℝ) ^ M := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hAR hpow).mpr
    have h1 := mul_le_mul_of_nonneg_right (show (M: ℝ) + 1 ≤ 2 * M by linarith) hAR.le
    nlinarith
  have hres : ‖residual N‖ ^ 2 ≤ 1 := QCanonicalInnovation.error_le_one N
  have hnorm : ‖finiteDisplacement N‖ ^ 2 ≤ 1 := by nlinarith [finiteDisplacement_energy_bound N]
  have hscale : frozenStageFactor N * ‖finiteDisplacement N‖ ^ 2 ≤ (4 * zetaTwo) * (M: ℝ) ^ 5 := by
    calc
      _ ≤ ((4 * zetaTwo) * (M: ℝ) ^ 5) * 1 := mul_le_mul (frozenStageFactor_polynomial N)
        hnorm (sq_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hscale0 : 0 ≤ frozenStageFactor N * ‖finiteDisplacement N‖ ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hz)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) (sq_nonneg _)
  calc
    _ ≤ (frozenStageFactor N * ‖finiteDisplacement N‖ ^ 2) ^ 4 * (2 / (A : ℝ)) :=
      frozen_finiteDisplacement_eighth_block N A (T N) hA
    _ ≤ ((4 * zetaTwo) * (M: ℝ) ^ 5) ^ 4 * ((4 * (M: ℝ)) * (1 / 2: ℝ) ^ M) :=
      mul_le_mul (pow_le_pow_left₀ hscale0 hscale 4) hrec (by positivity) (by positivity)
    _ = C * ((M : ℝ) ^ 21 * (1 / 2: ℝ) ^ M) := by dsimp [C]; ring

end RiemannResearch.RH.CRTBlock

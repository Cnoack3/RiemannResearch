/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.IntegratedRamanujanRankTwo
import RiemannResearch.RH.ParetoFiniteSchur
import RiemannResearch.RH.ParetoFiniteErrorObstruction
import RiemannResearch.RH.ResidueSmallGram
import RiemannResearch.LinearAlgebra.RankTwoResidualMean
import RiemannResearch.LinearAlgebra.MeanOneCoreInertia

/-!
# The derived core of the actual complete Pareto packet Gram matrix

The core here is derived from the actual full-tail Gram and its actual
von Mangoldt and totient vectors. The exact rank-two identity and its
positivity on the totient kernel are unconditional. A quantitative negative diagonal entry at every odd prime supplies the
negative direction for every squarefree conductor greater than two.

This file does not identify the derived core with the explicit cotangent
double-divisor formula in `IntegerDPPPacketRankTwo`, and does not assert
that these entries are algebraic or provide any limiting RH estimate.
Source: user-directed continuation of `CriticalZeroMeanOneAdvance20261008.md`.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalPacketCore
open RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.RankTwoWoodbury
open RiemannResearch.LinearAlgebra.RankTwoResidualMean

/-- Synthesis using the genuine divisor-sum packets. -/
def synthesis (s : Finset ℕ) (c : s → ℝ) : ℕ → ℝ :=
  FiniteSchur.combination (fun q : s => ramanujanPacket q.val) c

theorem synthesis_bounded (s : Finset ℕ) (c : s → ℝ) :
    ∀ k, |synthesis s c k| ≤ ∑ q : s, |c q| *
      (∑ d ∈ q.val.divisors,
        |(ArithmeticFunction.moebius (q.val / d) : ℝ)| * (d : ℝ)) := by
  exact FiniteSchur.combination_bounded (fun q k => ramanujanPacket_abs_le q.val k) c

/-- The logarithmic source is the actual full Pareto pairing with one. -/
theorem synthesis_mean (s : Finset ℕ) (c : s → ℝ) :
    paretoMean (synthesis s c) = ramanujanVonMangoldtVector s ⬝ᵥ c := by
  rw [← paretoInner_one_right]
  rw [synthesis, FiniteSchur.inner_combination_left
    (fun q k => ramanujanPacket_abs_le q.val k)
    (by intro k; norm_num : ∀ k : ℕ, |(1 : ℝ)| ≤ (1 : ℝ))]
  simp only [paretoInner_one_right, paretoMean_ramanujanPacket,
    ramanujanVonMangoldtVector, dotProduct]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Complete signed Gram expansion, including the infinite physical tail. -/
theorem synthesis_gram (s : Finset ℕ) (c : s → ℝ) :
    paretoInner (synthesis s c) (synthesis s c) =
      c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
  unfold synthesis FiniteSchur.combination
  rw [paretoInner_finsetCombination Finset.univ c
    (fun q k => ramanujanPacket_abs_le q.val k)]
  simp only [dotProduct, Matrix.mulVec, ramanujanGramMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Strict positivity is discharged by actual packet independence. -/
theorem gram_quadratic_pos (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (c : s → ℝ) (hc : c ≠ 0) :
    0 < c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
  have hn : 0 ≤ c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
    rw [← synthesis_gram]
    exact paretoInner_self_nonneg _
  by_contra hp
  have hz : c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) = 0 :=
    le_antisymm (le_of_not_gt hp) hn
  rw [← synthesis_gram] at hz
  have hvals := (paretoInner_self_zero_iff_positive (synthesis_bounded s c)).mp hz
  have hf : synthesis s c = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [synthesis, FiniteSchur.combination, ramanujanPacket, residue]
    · exact hvals k (Nat.pos_of_ne_zero hk)
  have hker : ramanujanGramAction s c = 0 := by
    funext i
    change FiniteSchur.gramApply (fun q : s => ramanujanPacket q.val) c i = 0
    rw [FiniteSchur.gramApply_eq_inner (fun q k => ramanujanPacket_abs_le q.val k)]
    change paretoInner (ramanujanPacket i.val) (synthesis s c) = 0
    rw [hf]
    simp [paretoInner]
  exact hc (ramanujanGramAction_eq_zero s hs c hker)

/-- Derived from the genuine Gram. This is not the proposed cotangent core. -/
def derivedCore (s : Finset ℕ) : Matrix s s ℝ := fun i j =>
  (ramanujanGramMatrix s i j -
    (ramanujanVonMangoldtVector s i * ramanujanTotientVector s j +
     ramanujanTotientVector s i * ramanujanVonMangoldtVector s j) / 2) / Real.pi

theorem derivedCore_transpose (s : Finset ℕ) :
    (derivedCore s)ᵀ = derivedCore s := by
  ext i j
  simp only [Matrix.transpose_apply, derivedCore, ramanujanGramMatrix]
  rw [paretoInner_comm (ramanujanPacket j.val) (ramanujanPacket i.val)]
  ring

/-- Unconditional rank-two realization of the actual physical Gram. -/
theorem gram_eq_rankTwo_derivedCore (s : Finset ℕ) :
    ramanujanGramMatrix s = rankTwoMatrix Real.pi (derivedCore s)
      (ramanujanVonMangoldtVector s) (ramanujanTotientVector s) := by
  ext i j
  simp only [rankTwoMatrix, derivedCore, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring

theorem gram_quadratic_eq_core (s : Finset ℕ) (c : s → ℝ) :
    c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) =
      Real.pi * (c ⬝ᵥ (derivedCore s *ᵥ c)) +
        (ramanujanVonMangoldtVector s ⬝ᵥ c) *
          (ramanujanTotientVector s ⬝ᵥ c) := by
  rw [gram_eq_rankTwo_derivedCore, rankTwoMatrix_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_comm c (ramanujanVonMangoldtVector s),
    dotProduct_comm c (ramanujanTotientVector s)]
  ring

/-- The full actual core is strictly positive on the totient kernel. -/
theorem derivedCore_pos_on_totient_kernel (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (c : s → ℝ) (hc : c ≠ 0)
    (hphi : ramanujanTotientVector s ⬝ᵥ c = 0) :
    0 < c ⬝ᵥ (derivedCore s *ᵥ c) := by
  have hg := gram_quadratic_pos s hs c hc
  rw [gram_quadratic_eq_core, hphi, mul_zero, add_zero] at hg
  exact (mul_pos_iff_of_pos_left Real.pi_pos).mp hg

/-- Literal physical error, with both linear and all quadratic terms retained. -/
theorem synthesis_error (s : Finset ℕ) (c : s → ℝ) :
    paretoError (synthesis s c) =
      1 - 2 * (ramanujanVonMangoldtVector s ⬝ᵥ c) +
        c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
  have h := paretoInner_residual_polynomial
    (r := fun _ : ℕ => (1 : ℝ)) (g := synthesis s c)
    (by intro k; norm_num : ∀ k : ℕ, |(1 : ℝ)| ≤ (1 : ℝ))
    (synthesis_bounded s c) (1 : ℝ)
  simpa only [one_mul, mul_one, one_pow, paretoInner_one, paretoInner_one_left,
    paretoMean_one, synthesis_mean, synthesis_gram, paretoError] using h

/-- Actual synthesis realizes the already verified algebraic complete error. -/
theorem synthesis_error_eq_fullError (s : Finset ℕ) (c : s → ℝ) :
    paretoError (synthesis s c) =
      fullError Real.pi (derivedCore s) (ramanujanVonMangoldtVector s)
        (ramanujanTotientVector s) c := by
  rw [synthesis_error]
  unfold fullError
  rw [← gram_eq_rankTwo_derivedCore]

theorem synthesis_error_of_totient_constraint (s : Finset ℕ) (c : s → ℝ)
    (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    paretoError (synthesis s c) =
      1 + Real.pi * (c ⬝ᵥ (derivedCore s *ᵥ c)) := by
  rw [synthesis_error_eq_fullError]
  exact fullError_eq_core_of_mean_one _ _ _ _ _ hc

/-- Exact negative arithmetic entry from the existing complete conductor-3 norm. -/
theorem packet_three_norm :
    paretoInner (ramanujanPacket 3) (ramanujanPacket 3) =
      2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3) := by
  rw [ramanujanPacket_prime_eq_residue 3 (by norm_num)]
  have h : ‖CoefficientStabilization.residueAtom 1‖ ^ 2 =
      paretoInner (residue 3) (residue 3) / 9 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (normalizedResidueHilbert 3 _) (normalizedResidueHilbert 3 _) = _
    rw [normalizedResidueHilbert_inner]
    norm_num
  rw [residueAtom_one_norm_sq] at h
  calc
    _ = 9 * (2 * Real.log 3 / 9 - Real.pi / (27 * Real.sqrt 3)) := by
      linarith only [h]
    _ = _ := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      ring

theorem derivedCore_three_entry (s : Finset ℕ) (h3 : 3 ∈ s) :
    derivedCore s ⟨3, h3⟩ ⟨3, h3⟩ = -1 / (3 * Real.sqrt 3) := by
  change (paretoInner (ramanujanPacket 3) (ramanujanPacket 3) -
    (ArithmeticFunction.vonMangoldt 3 * (Nat.totient 3 : ℝ) +
      (Nat.totient 3 : ℝ) * ArithmeticFunction.vonMangoldt 3) / 2) / Real.pi = _
  rw [packet_three_norm, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num),
    show Nat.totient 3 = 2 by decide]
  norm_num
  field_simp [Real.pi_ne_zero,
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
  ring

theorem derivedCore_three_entry_neg (s : Finset ℕ) (h3 : 3 ∈ s) :
    derivedCore s ⟨3, h3⟩ ⟨3, h3⟩ < 0 := by
  rw [derivedCore_three_entry]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

/-- An explicit negative direction, with no arithmetic-core premise. -/
theorem derivedCore_has_negative_direction (s : Finset ℕ) (h3 : 3 ∈ s) :
    ∃ c : s → ℝ, c ⬝ᵥ (derivedCore s *ᵥ c) < 0 := by
  classical
  refine ⟨Pi.single ⟨3, h3⟩ 1, ?_⟩
  simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col,
    Matrix.transpose_apply]
    using derivedCore_three_entry_neg s h3

open RiemannResearch.LinearAlgebra.MeanOneCoreInertia

/-- A quantitative complete-norm gap, with the strict first physical site retained. -/
theorem residue_norm_period_mean_gap (p : ℕ) (hp : 0 < p) :
    paretoInner (residue p) (residue p) ≤
      ((p : ℝ) - 1) * Real.log p - ((p : ℝ) - 2) / 2 := by
  have hr : ∀ k, |residue p k| ≤ (p : ℝ) := fun k => residue_abs_le p k hp
  let d : ℕ → ℝ := fun k => ((p : ℝ) - 1) * residue p k - residue p k * residue p k
  have hd : ∀ k, |d k| ≤ |(p : ℝ) - 1| * (p : ℝ) + (p : ℝ) * (p : ℝ) :=
    bounded_sub (bounded_const_mul hr ((p : ℝ) - 1)) (bounded_product hr hr)
  have hdnonneg (k : ℕ) : 0 ≤ d k := by
    have hnonneg : 0 ≤ residue p k := Nat.cast_nonneg (k % p)
    have hle : residue p k ≤ (p : ℝ) - 1 := by
      have hnat : k % p ≤ p - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt k hp)
      have hcast : ((k % p : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa only [residue, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using hcast
    have hproduct := mul_nonneg hnonneg (sub_nonneg.mpr hle)
    dsimp only [d]
    nlinarith only [hproduct]
  have hmean : paretoMean d = ((p : ℝ) - 1) * Real.log p -
      paretoInner (residue p) (residue p) := by
    have hlin : paretoMean (fun k => ((p : ℝ) - 1) * residue p k) =
        ((p : ℝ) - 1) * Real.log p := by
      rw [← paretoInner_one_right,
        paretoInner_const_mul_left hr
          (by intro k; norm_num : ∀ k : ℕ, |(1 : ℝ)| ≤ (1 : ℝ)),
        paretoInner_one_right, paretoMean_residue p hp]
    have hnorm : paretoMean (fun k => residue p k * residue p k) =
        paretoInner (residue p) (residue p) := rfl
    dsimp only [d]
    rw [paretoMean_sub (bounded_const_mul hr ((p : ℝ) - 1))
      (bounded_product hr hr), hlin, hnorm]
  have hsum := weighted_summable_of_bounded hd
  have hle := hsum.sum_le_tsum ({1} : Finset ℕ)
    (fun k hk => mul_nonneg (positiveWeight_nonneg k) (hdnonneg k))
  change (∑ k ∈ ({1} : Finset ℕ), positiveWeight k * d k) ≤ paretoMean d at hle
  rw [Finset.sum_singleton, hmean] at hle
  by_cases hp1 : p = 1
  · subst p
    norm_num [residue, Nat.mod_one, paretoInner]
  · have hpone : 1 < p := by omega
    have hfirst : positiveWeight 1 * d 1 = ((p : ℝ) - 2) / 2 := by
      dsimp only [d]
      simp only [positiveWeight, residue, Nat.mod_eq_of_lt hpone]
      norm_num
      ring
    rw [hfirst] at hle
    linarith only [hle]

/-- Every odd prime has a strictly negative diagonal core entry, quantitatively. -/
theorem derivedCore_prime_entry_le (s : Finset ℕ) (p : ℕ)
    (hp : p.Prime) (hps : p ∈ s) :
    derivedCore s ⟨p, hps⟩ ⟨p, hps⟩ ≤ -((p : ℝ) - 2) / (2 * Real.pi) := by
  have htot : Nat.totient p = p - 1 := by
    simpa using (Nat.totient_prime_pow_succ hp 0)
  have hgap := residue_norm_period_mean_gap p hp.pos
  change (paretoInner (ramanujanPacket p) (ramanujanPacket p) -
    (ArithmeticFunction.vonMangoldt p * (Nat.totient p : ℝ) +
      (Nat.totient p : ℝ) * ArithmeticFunction.vonMangoldt p) / 2) / Real.pi ≤ _
  rw [ramanujanPacket_prime_eq_residue p hp,
    ArithmeticFunction.vonMangoldt_apply_prime hp, htot,
    Nat.cast_sub (le_of_lt hp.one_lt), Nat.cast_one]
  have hnum : paretoInner (residue p) (residue p) -
      (((p : ℝ) - 1) * Real.log p) ≤ -((p : ℝ) - 2) / 2 := by
    linarith only [hgap]
  calc
    _ = (paretoInner (residue p) (residue p) -
        ((p : ℝ) - 1) * Real.log p) / Real.pi := by ring
    _ ≤ (-((p : ℝ) - 2) / 2) / Real.pi :=
      div_le_div_of_nonneg_right hnum Real.pi_pos.le
    _ = -((p : ℝ) - 2) / (2 * Real.pi) := by ring

theorem derivedCore_prime_entry_neg (s : Finset ℕ) (p : ℕ)
    (hp : p.Prime) (hpodd : 2 < p) (hps : p ∈ s) :
    derivedCore s ⟨p, hps⟩ ⟨p, hps⟩ < 0 := by
  have hpR : 2 < (p : ℝ) := by exact_mod_cast hpodd
  apply (derivedCore_prime_entry_le s p hp hps).trans_lt
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem derivedCore_has_negative_prime_direction (s : Finset ℕ)
    (p : ℕ) (hp : p.Prime) (hpodd : 2 < p) (hps : p ∈ s) :
    ∃ c : s → ℝ, c ⬝ᵥ (derivedCore s *ᵥ c) < 0 := by
  classical
  refine ⟨Pi.single ⟨p, hps⟩ 1, ?_⟩
  simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col,
    Matrix.transpose_apply]
    using derivedCore_prime_entry_neg s p hp hpodd hps


theorem derivedCore_positiveOnMeanKernel (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) :
    PositiveOnMeanKernel (derivedCore s) (ramanujanTotientVector s) := by
  intro c hphi hc
  exact derivedCore_pos_on_totient_kernel s hs c hc hphi

/-- Actual invertibility for every legal packet set containing an odd prime. -/
theorem derivedCore_det_ne_zero (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) : (derivedCore s).det ≠ 0 := by
  obtain ⟨p, hps, hp, hpodd⟩ := hodd
  obtain ⟨v, hv⟩ := derivedCore_has_negative_prime_direction s p hp hpodd hps
  exact RiemannResearch.LinearAlgebra.MeanOneCoreInertia.det_ne_zero
    (derivedCore s) (ramanujanTotientVector s)
    (derivedCore_transpose s) (derivedCore_positiveOnMeanKernel s hs) v hv

theorem derivedCore_mul_inverse (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    derivedCore s * (derivedCore s)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (derivedCore_det_ne_zero s hs hodd))

/-- The inverse-core scalar is derived from the genuine complete Pareto matrix. -/
def inverseCharge (s : Finset ℕ) : ℝ :=
  ramanujanTotientVector s ⬝ᵥ ((derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s)

theorem inverseCharge_neg (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) : inverseCharge s < 0 := by
  obtain ⟨p, hps, hp, hpodd⟩ := hodd
  obtain ⟨v, hv⟩ := derivedCore_has_negative_prime_direction s p hp hpodd hps
  exact inverse_charge_neg (derivedCore s) (derivedCore s)⁻¹ (ramanujanTotientVector s)
    (derivedCore_mul_inverse s hs ⟨p, hps, hp, hpodd⟩) (derivedCore_transpose s)
    (derivedCore_positiveOnMeanKernel s hs) v hv

def constrainedOptimizer (s : Finset ℕ) : s → ℝ :=
  (2 / inverseCharge s) • ((derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s)

theorem constrainedOptimizer_totient (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanTotientVector s ⬝ᵥ constrainedOptimizer s = 2 := by
  unfold constrainedOptimizer
  rw [dotProduct_smul, smul_eq_mul]
  change (2 / inverseCharge s) * inverseCharge s = 2
  exact div_mul_cancel₀ 2 (ne_of_lt (inverseCharge_neg s hs hodd))

/-- Actual physical error at the explicit constrained optimizer. -/
theorem constrainedOptimizer_error (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (constrainedOptimizer s)) =
      1 + 4 * Real.pi / inverseCharge s := by
  rw [synthesis_error_of_totient_constraint s _ (constrainedOptimizer_totient s hs hodd)]
  have hnormal : derivedCore s *ᵥ constrainedOptimizer s =
      (2 / inverseCharge s) • ramanujanTotientVector s := by
    unfold constrainedOptimizer
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      derivedCore_mul_inverse s hs hodd, Matrix.one_mulVec]
  rw [hnormal, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (constrainedOptimizer s) (ramanujanTotientVector s),
    constrainedOptimizer_totient s hs hodd]
  ring

/-- Full square completion for actual physical competitors on the affine constraint. -/
theorem constrainedOptimizer_completion (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ)
    (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    paretoError (synthesis s c) = 1 + 4 * Real.pi / inverseCharge s +
      Real.pi * ((c - constrainedOptimizer s) ⬝ᵥ
        (derivedCore s *ᵥ (c - constrainedOptimizer s))) := by
  obtain ⟨_, he⟩ := constrained_mean_completion Real.pi (derivedCore s) (derivedCore s)⁻¹
    (ramanujanGramMatrix s) (ramanujanTotientVector s)
    (ramanujanVonMangoldtVector s) c (derivedCore_mul_inverse s hs hodd)
    (derivedCore_transpose s) (gram_eq_rankTwo_derivedCore s)
    (ne_of_lt (inverseCharge_neg s hs hodd)) hc
  rw [synthesis_error]
  exact he

/-- The exact minimum is uniquely attained by the actual packet coefficient vector. -/
theorem constrainedOptimizer_unique_minimum (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ)
    (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    1 + 4 * Real.pi / inverseCharge s ≤ paretoError (synthesis s c) ∧
      (paretoError (synthesis s c) = 1 + 4 * Real.pi / inverseCharge s ↔
        c = constrainedOptimizer s) := by
  have h := constrained_unique_minimum Real.pi (derivedCore s) (derivedCore s)⁻¹
    (ramanujanGramMatrix s) (ramanujanTotientVector s)
    (ramanujanVonMangoldtVector s) c Real.pi_pos (derivedCore_mul_inverse s hs hodd)
    (derivedCore_transpose s) (gram_eq_rankTwo_derivedCore s)
    (ne_of_lt (inverseCharge_neg s hs hodd))
    (derivedCore_positiveOnMeanKernel s hs) hc
  simpa only [synthesis_error, inverseCharge, constrainedOptimizer] using h

theorem synthesis_zero_at_common_multiple (s : Finset ℕ) (c : s → ℝ) (L : ℕ)
    (hL : ∀ q ∈ s, q ∣ L) : synthesis s c L = 0 := by
  unfold synthesis FiniteSchur.combination
  apply Finset.sum_eq_zero
  intro q hq
  change c q * ramanujanPacket q.val L = 0
  rw [ramanujanPacket_eq_zero_of_dvd (hL q.val q.property), mul_zero]

/-- The complete physical atom at a common-period site forces a positive error floor. -/
theorem synthesis_error_floor (s : Finset ℕ) (c : s → ℝ) (L : ℕ)
    (hL : ∀ q ∈ s, q ∣ L) :
    positiveWeight L ≤ paretoError (synthesis s c) := by
  exact positiveWeight_le_error_of_zero (synthesis_bounded s c)
    (synthesis_zero_at_common_multiple s c L hL)

/-- The inverse-core charge stays strictly below the saturation endpoint at every finite stage. -/
theorem inverseCharge_lt_neg_four_pi (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (L : ℕ) (hL0 : 0 < L)
    (hL : ∀ q ∈ s, q ∣ L) : inverseCharge s < -4 * Real.pi := by
  have hweight : 0 < positiveWeight L := by unfold positiveWeight; positivity
  have he := synthesis_error_floor s (constrainedOptimizer s) L hL
  rw [constrainedOptimizer_error s hs hodd] at he
  have hC := inverseCharge_neg s hs hodd
  have hpositive : 0 < 1 + 4 * Real.pi / inverseCharge s := by linarith
  have hmul := mul_pos hpositive (neg_pos.mpr hC)
  have hcancel : (1 + 4 * Real.pi / inverseCharge s) * (-inverseCharge s) =
      -inverseCharge s - 4 * Real.pi := by
    field_simp [ne_of_lt hC]
    ring
  rw [hcancel] at hmul
  linarith

/-- Every nontrivial squarefree conductor beyond 2 has an odd prime divisor. -/
theorem squarefree_exists_odd_prime_divisor (L : ℕ) (hL : 2 < L)
    (hsq : Squarefree L) : ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ L := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : L ≠ 1)
  by_cases hp2 : p = 2
  · subst p
    have hLeq : 2 * (L / 2) = L := Nat.mul_div_cancel' hpd
    have hquot : L / 2 ≠ 1 := by
      intro h
      rw [h] at hLeq
      norm_num at hLeq
      omega
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hquot
    have hq2 : q ≠ 2 := by
      intro he
      subst q
      have hfour : 2 * 2 ∣ L := by
        rw [← hLeq]
        exact Nat.mul_dvd_mul_left 2 hqd
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hfour
    refine ⟨q, hq, ?_, dvd_trans hqd (Nat.div_dvd_of_dvd hpd)⟩
    have := hq.two_le
    omega
  · refine ⟨p, hp, ?_, hpd⟩
    have := hp.two_le
    omega

/-- Full divisor packet dictionary at a conductor. -/
def divisorPackets (L : ℕ) : Finset ℕ := L.divisors.filter (fun d => 1 < d)

theorem divisorPackets_legal (L : ℕ) : ∀ q ∈ divisorPackets L, 1 < q := by
  intro q hq
  exact (Finset.mem_filter.mp hq).2

theorem divisorPackets_period (L : ℕ) : ∀ q ∈ divisorPackets L, q ∣ L := by
  intro q hq
  exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1

theorem divisorPackets_odd (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    ∃ p ∈ divisorPackets L, p.Prime ∧ 2 < p := by
  obtain ⟨p, hp, hpodd, hpd⟩ := squarefree_exists_odd_prime_divisor L hL hsq
  exact ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hpd, by omega⟩, by omega⟩,
    hp, hpodd⟩

/-- Physical squarefree stages discharge every finite inverse hypothesis. -/
theorem divisorPackets_optimizer (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    ramanujanTotientVector (divisorPackets L) ⬝ᵥ constrainedOptimizer (divisorPackets L) = 2 ∧
    paretoError (synthesis (divisorPackets L) (constrainedOptimizer (divisorPackets L))) =
      1 + 4 * Real.pi / inverseCharge (divisorPackets L) ∧
    inverseCharge (divisorPackets L) < -4 * Real.pi := by
  have hs := divisorPackets_legal L
  have ho := divisorPackets_odd L hL hsq
  exact ⟨constrainedOptimizer_totient _ hs ho, constrainedOptimizer_error _ hs ho,
    inverseCharge_lt_neg_four_pi _ hs ho L (by omega) (divisorPackets_period L)⟩

end RiemannResearch.RH.Pareto.PhysicalPacketCore

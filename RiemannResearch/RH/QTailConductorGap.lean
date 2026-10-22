/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTailConstrainedMinimum
import RiemannResearch.RH.QTailGram
import RiemannResearch.RH.QSquarefreeConstrainedMinimum
import RiemannResearch.RH.QLargeConductorCapacity
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic obstructions from a gap before the first free conductor

Source: continuation of the user's complete-tail formulation, 16 October 2026.
Before any free residue wraps, normalization fixes every residual value.
The exact floor defect and complete tail remainder are retained. These
identities give necessary arithmetic tests, not an RH estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTailConductorGap
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QTailGram QTailConstrainedMinimum QLargeConductorCapacity
open QSquarefreeConstrainedMinimum
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

variable {ι : Type*} [Fintype ι]

/-- Removing H sites does not remove the mandatory linear energy on H<n<=J. -/
theorem inverse_tail_capacity_gap [Nonempty ι] (H J : ℕ) (hHJ : H ≤ J)
    (d : ι → ℕ) (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hdJ : ∀ i, J < d i) :
    1 / tailCapacity H d hd2 hinj =
      ((J : ℝ) - H) / zetaTwo +
        tailEnergy J (Fintype.linearCombination ℝ (fun i => qResidue (d i))
          ((tailCapacity H d hd2 hinj)⁻¹ •
            inverseSource (tailResidue_linearIndependent H d hd2 hinj)
              (normalizationSource d))) := by
  let ht := tailResidue_linearIndependent H d hd2 hinj
  let b := normalizationSource d
  let c := (tailCapacity H d hd2 hinj)⁻¹ • inverseSource ht b
  have hb : b ≠ 0 := normalizationSource_ne_zero d
    (fun i => lt_trans Nat.zero_lt_one (hd2 i))
  have hc : (∑ i, c i * normalizationSource d i) = 1 :=
    normalized_source ht b hb
  have hH := synthesis_energy d H (fun i => lt_of_le_of_lt hHJ (hdJ i)) c
  have hJ := synthesis_energy d J hdJ c
  rw [hc, one_pow, mul_one] at hH hJ
  have htE : ‖tailMap H (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)‖ ^ 2 =
      1 / tailCapacity H d hd2 hinj := by
    rw [tailMap_synthesis]
    change ‖Fintype.linearCombination ℝ (tailResidue H d)
      ((capacity ht b)⁻¹ • inverseSource ht b)‖ ^ 2 = _
    rw [map_smul]
    exact normalized_energy ht b hb
  rw [tailMap_norm_sq] at htE
  change 1 / tailCapacity H d hd2 hinj =
    ((J : ℝ) - H) / zetaTwo +
      tailEnergy J (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)
  rw [sub_div]
  linarith only [hH, hJ, htE]

theorem tailCapacity_le_gap [Nonempty ι] (H J : ℕ) (hHJ : H < J)
    (d : ι → ℕ) (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hdJ : ∀ i, J < d i) :
    tailCapacity H d hd2 hinj ≤ zetaTwo / ((J : ℝ) - H) := by
  have hp := tailCapacity_pos H d hd2 hinj
  have hgap : (0 : ℝ) < (J : ℝ) - H := sub_pos.mpr (by exact_mod_cast hHJ)
  have he := inverse_tail_capacity_gap H J hHJ.le d hd2 hinj hdJ
  have htail := tailEnergy_nonneg J (Fintype.linearCombination ℝ (fun i => qResidue (d i))
    ((tailCapacity H d hd2 hinj)⁻¹ •
      inverseSource (tailResidue_linearIndependent H d hd2 hinj) (normalizationSource d)))
  have hh : ((J : ℝ) - H) / zetaTwo ≤ 1 / tailCapacity H d hd2 hinj := by
    linarith only [he, htail]
  have hm := (le_div_iff₀ hp).mp hh
  rw [div_mul_eq_mul_div] at hm
  have hn := (div_le_iff₀ zetaTwo_pos).mp hm
  apply (le_div_iff₀ hgap).mpr
  simpa only [one_mul, mul_one, mul_comm] using hn

/-- A squarefree family cannot fill a nonsquarefree immediate successor site.
In particular, tail capacity cannot diverge along every possible head. -/
theorem tailCapacity_le_zetaTwo_of_next_not_squarefree [Nonempty ι]
    (H : ℕ) (d : ι → ℕ) (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hdH : ∀ i, H < d i) (hsf : ∀ i, Squarefree (d i))
    (hnext : ¬ Squarefree (H + 1)) :
    tailCapacity H d hd2 hinj ≤ zetaTwo := by
  have hdJ : ∀ i, H + 1 < d i := by
    intro i
    have hi := hdH i
    by_contra h
    have he : d i = H + 1 := by omega
    exact hnext (he ▸ hsf i)
  have he := tailCapacity_le_gap H (H + 1) (Nat.lt_succ_self H) d hd2 hinj hdJ
  have hr : (((H + 1 : ℕ) : ℝ) - H) = 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
  simpa only [hr, div_one] using he

/-- Signed arithmetic residual forced before the first free wrap. -/
def floorDefect (H n : ℕ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius k : ℝ) * ((n / k : ℕ) : ℝ)

theorem seedResidual_minus_linear (H n : ℕ) (hn : 0 < n) :
    qSequence (qOne - mobiusSeed H) n - (n : ℝ) * Pareto.mobiusReciprocalSum H =
      floorDefect H n := by
  have hseed : qSequence (mobiusSeed H) n =
      -(∑ k ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius k : ℝ) *
        residueFraction k n) := by
    change qSequenceLinear (mobiusSeed H) n = _
    unfold mobiusSeed
    rw [map_neg, map_sum]
    simp only [map_smul, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change -(∑ k ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius k : ℝ) *
      qSequence (qResidue k) n) = _
    simp only [qSequence_qResidue]
  have hsum : (∑ k ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius k : ℝ) *
      residueFraction k n) =
      (n : ℝ) * Pareto.mobiusReciprocalSum H -
        ∑ k ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius k : ℝ) *
          ((n / k : ℕ) : ℝ) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 H,
          ((n : ℝ) * ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ)) -
            (ArithmeticFunction.moebius k : ℝ) * ((n / k : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Pareto.residueFraction_eq_div_sub_floor k n (Finset.mem_Icc.mp hk).1]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  change qSequenceLinear (qOne - mobiusSeed H) n - _ = _
  rw [map_sub]
  change qSequence qOne n - qSequence (mobiusSeed H) n - _ = _
  rw [qSequence_qOne, hseed, hsum]
  simp only [qOneSequence, if_neg (ne_of_gt hn)]
  unfold floorDefect
  ring

/-- On the first dyadic window the forced floor defect is an exact Mertens increment. -/
theorem floorDefect_first_window (H n : ℕ) (hn : 0 < n)
    (hHn : H ≤ n) (hn2 : n ≤ 2 * H + 1) :
    floorDefect H n = ∑ k ∈ Finset.Icc (H + 1) n, (ArithmeticFunction.moebius k : ℝ) := by
  classical
  have hu : Finset.Icc 1 H ∪ Finset.Icc (H + 1) n = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc 1 H) (Finset.Icc (H + 1) n) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have := Finset.mem_Icc.mp hk
    have := Finset.mem_Icc.mp hk'
    omega
  have hsplit := Finset.sum_union hd (f := fun k =>
    (ArithmeticFunction.moebius k : ℝ) * ((n / k : ℕ) : ℝ))
  rw [hu, Pareto.finite_mobius_floor_sum n n hn le_rfl] at hsplit
  have ht : (∑ k ∈ Finset.Icc (H + 1) n,
      (ArithmeticFunction.moebius k : ℝ) * ((n / k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc (H + 1) n, (ArithmeticFunction.moebius k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hq : n / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hq, Nat.cast_one, mul_one]
  rw [ht] at hsplit
  unfold floorDefect
  linarith only [hsplit]

theorem feasible_residual_before_wrap (H J : ℕ) (d : ι → ℕ)
    (hdJ : ∀ i, J < d i) (c : ι → ℝ)
    (hc : (∑ i, c i * normalizationSource d i) = Pareto.mobiusReciprocalSum H)
    (n : ℕ) (hn : 0 < n) (hnJ : n ≤ J) :
    qSequence (qOne - (mobiusSeed H +
      Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)) n = floorDefect H n := by
  rw [sub_add_eq_sub_sub]
  change qSequenceLinear ((qOne - mobiusSeed H) -
    Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n = _
  rw [map_sub]
  change qSequence (qOne - mobiusSeed H) n -
    qSequence (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n = _
  rw [synthesis_head d J hdJ c n hnJ, hc, seedResidual_minus_linear H n hn]

/-- All coefficients, including the optimizer, incur this exact arithmetic block.
The remainder includes every physical site beyond J. -/
theorem feasible_error_block (H J : ℕ) (d : ι → ℕ) (hdJ : ∀ i, J < d i)
    (c : ι → ℝ)
    (hc : (∑ i, c i * normalizationSource d i) = Pareto.mobiusReciprocalSum H) :
    ‖qOne - (mobiusSeed H + Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)‖ ^ 2 =
      (∑ n ∈ Finset.range J, positiveQWeight (n + 1) * floorDefect H (n + 1) ^ 2) +
        tailEnergy J (qOne - (mobiusSeed H +
          Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)) := by
  let r := qOne - (mobiusSeed H + Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)
  change ‖r‖ ^ 2 = _ + tailEnergy J r
  rw [qNorm_sq, ← (qCoordinate_square_summable r).sum_add_tsum_nat_add J]
  change (∑ n ∈ Finset.range J, (r n) ^ 2) + tailEnergy J r = _
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [← qSequence_weighted_square]
  have hs := feasible_residual_before_wrap H J d hdJ c hc (n + 1) (Nat.succ_pos n)
    (by have := Finset.mem_range.mp hn; omega)
  change qSequence r (n + 1) = floorDefect H (n + 1) at hs
  rw [hs]

theorem minimumError_block [Nonempty ι] (H J : ℕ) (d : ι → ℕ)
    (hdJ : ∀ i, J < d i)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd0 : ∀ i, 0 < d i) :
    minimumError H d hv =
      (∑ n ∈ Finset.range J, positiveQWeight (n + 1) * floorDefect H (n + 1) ^ 2) +
        tailEnergy J (qOne - optimizer H d hv) :=
  feasible_error_block H J d hdJ _
    (scalarCoefficients_source hv (normalizationSource d)
      (normalizationSource_ne_zero d hd0) _ _)

theorem minimumError_ge_block [Nonempty ι] (H J : ℕ) (d : ι → ℕ)
    (hdJ : ∀ i, J < d i)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd0 : ∀ i, 0 < d i) :
    (∑ n ∈ Finset.range J, positiveQWeight (n + 1) * floorDefect H (n + 1) ^ 2) ≤
      minimumError H d hv := by
  rw [minimumError_block H J d hdJ hv hd0]
  exact le_add_of_nonneg_right (tailEnergy_nonneg J _)

theorem optimizer_residual_first_window [Nonempty ι] (H J : ℕ) (d : ι → ℕ)
    (hdJ : ∀ i, J < d i)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd0 : ∀ i, 0 < d i)
    (n : ℕ) (hn : 0 < n) (hHn : H ≤ n) (hnJ : n ≤ J) (hn2 : n ≤ 2 * H + 1) :
    qSequence (qOne - optimizer H d hv) n =
      ∑ k ∈ Finset.Icc (H + 1) n, (ArithmeticFunction.moebius k : ℝ) := by
  have he := feasible_residual_before_wrap H J d hdJ
    (scalarCoefficients hv (normalizationSource d) (qOne - mobiusSeed H)
      (Pareto.mobiusReciprocalSum H))
    (scalarCoefficients_source hv (normalizationSource d)
      (normalizationSource_ne_zero d hd0) (qOne - mobiusSeed H)
        (Pareto.mobiusReciprocalSum H)) n hn hnJ
  change qSequence (qOne - optimizer H d hv) n = floorDefect H n at he
  rw [he, floorDefect_first_window H n hn hHn hn2]

end RiemannResearch.RH.QTailConductorGap

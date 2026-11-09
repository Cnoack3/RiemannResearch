/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.CriticalLineZeros
import RiemannResearch.RH.ParetoResidueClassMellin

/-!
# Finite zero-coordinate normal equations in the Pareto norm

The finite projection onto zero-indexed tests follows the strategy of
Burnol, Adv. Math. 170 (2002), 56–70, Section 5,
https://arxiv.org/abs/math/0103058. The actual test rows here come from the
discrete bounded-step Mellin formula on the user's LCM residue classes.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*}

/-- A complex Mellin test gives two real rows for the real residual. -/
def part (imaginary : Bool) (x : ℂ) : ℝ := if imaginary then x.im else x.re

/-- A zero row in the physical, nonzero residue coordinates. -/
def rowEntry (N : ℕ) (z : ι → ℂ) (i : ι × Bool) (r : Fin N) : ℝ :=
  part i.2 (classMellin N (z i.1) r.castSucc)

/-- The signed source after separating the entire multiples class. -/
def source (N : ℕ) (z : ι → ℂ) (i : ι × Bool) : ℝ :=
  part i.2 (1 - classMellin N (z i.1) (Fin.last N))

/-- The Riesz row after making the positive class metric Euclidean. -/
def rowVector (N : ℕ) (z : ι → ℂ) (i : ι × Bool) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun r => rowEntry N z i r / Real.sqrt (classWeight N r.castSucc))

/-- Weighted error on the nonzero classes. The last class is kept separately. -/
def errorVector (N : ℕ) (f : ThresholdHilbert) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun r => Real.sqrt (classWeight N r.castSucc) * error N f r.castSucc)

theorem error_norm_sq_split {N : ℕ} {f : ThresholdHilbert} (hf : f ∈ trialSpace (N + 1)) :
    ‖hilbertOne - f‖ ^ 2 = classWeight N (Fin.last N) + ‖errorVector N f‖ ^ 2 := by
  have hv : ‖errorVector N f‖ ^ 2 =
      ∑ r : Fin N, classWeight N r.castSucc * (error N f r.castSucc) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro r _
    change ‖Real.sqrt (classWeight N r.castSucc) * error N f r.castSucc‖ ^ 2 = _
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (classWeight_pos N _).le]
  rw [error_norm_sq_eq_classes hf, Fin.sum_univ_castSucc, error_multiples hf, one_pow, mul_one,
    hv, add_comm]

/-- The entries of the genuine finite Gram matrix, with all signed products. -/
theorem zero_gram_entry (N : ℕ) (z : ι → ℂ) (i j : ι × Bool) :
    gramMatrix (rowVector N z) i j =
      ∑ r : Fin N, rowEntry N z i r * rowEntry N z j r / classWeight N r.castSucc := by
  rw [gramMatrix, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  apply Finset.sum_congr rfl
  intro r _
  change (rowEntry N z j r / Real.sqrt (classWeight N r.castSucc)) *
    (rowEntry N z i r / Real.sqrt (classWeight N r.castSucc)) = _
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (classWeight_pos N _).le, mul_comm]

/-- The real and imaginary observations have the same prescribed source for
every legal error. -/
theorem error_observation {N : ℕ} {f : ThresholdHilbert} (hf : f ∈ trialSpace (N + 1))
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1)
    (hz : riemannZeta (z i.1) = 0) :
    inner ℝ (rowVector N z i) (errorVector N f) = source N z i := by
  have hdot : inner ℝ (rowVector N z i) (errorVector N f) =
      ∑ r : Fin N, rowEntry N z i r * error N f r.castSucc := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    apply Finset.sum_congr rfl
    intro r _
    change (Real.sqrt (classWeight N r.castSucc) * error N f r.castSucc) *
      (rowEntry N z i r / Real.sqrt (classWeight N r.castSucc)) = _
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (classWeight_pos N _))]
  rw [hdot]
  have h := congrArg (part i.2) (error_zero_moment hf (z i.1) hs hs1 hz)
  rcases i with ⟨j, b⟩
  cases b <;> simpa [rowEntry, source, part, Complex.mul_re, Complex.mul_im] using h

variable [Fintype ι]

/-- Feasibility from the zero competitor gives a solution even for singular
Gram matrices. Projection gives the same synthesized certificate for any solution. -/
theorem exists_zero_normal (N : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    ∃ a, (gramMatrix (rowVector N z)).mulVec a = source N z := by
  let x := errorVector N (0 : ThresholdHilbert)
  let S := synthesisSpan (rowVector N z)
  have hp := S.starProjection_apply_mem x
  change S.starProjection x ∈ Submodule.span ℝ (Set.range (rowVector N z)) at hp
  rw [← Fintype.range_linearCombination] at hp
  obtain ⟨a, ha⟩ := hp
  refine ⟨a, ?_⟩
  rw [gramMatrix_mulVec]
  funext i
  change inner ℝ (rowVector N z i) (Fintype.linearCombination ℝ (rowVector N z) a) = _
  have hi : rowVector N z i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  rw [ha, real_inner_comm, S.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hi, real_inner_comm]
  exact error_observation ((trialSpace (N + 1)).zero_mem) z i (hs _) (hs1 _) (hz _)

/-- All normal-equation solutions synthesize the same orthogonal projection,
even when the finite Gram matrix is singular. -/
theorem certificate_eq_projection {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (a : ι × Bool → ℝ) (ha : (gramMatrix (rowVector N z)).mulVec a = source N z) :
    Fintype.linearCombination ℝ (rowVector N z) a =
      (synthesisSpan (rowVector N z)).starProjection (errorVector N f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (synthesis_mem _ _)
  intro v hv
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  rw [real_inner_comm, inner_synthesis_left]
  rw [gramMatrix_mulVec] at ha
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_sub_right, error_observation hf z i (hs _) (hs1 _) (hz _)]
  change c i * (source N z i - gram (rowVector N z) a i) = 0
  rw [congrFun ha i, sub_self, mul_zero]

/-- Exact Pareto error as compulsory multiples mass, zero-certificate energy,
and the full remaining square. All terms are complete, and no inverse is assumed. -/
theorem legal_error_completion {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (a : ι × Bool → ℝ) (ha : (gramMatrix (rowVector N z)).mulVec a = source N z) :
    ‖hilbertOne - f‖ ^ 2 =
      classWeight N (Fin.last N) + dotProduct a (source N z) +
        ‖errorVector N f - Fintype.linearCombination ℝ (rowVector N z) a‖ ^ 2 := by
  let y := Fintype.linearCombination ℝ (rowVector N z) a
  have hy : ‖y‖ ^ 2 = dotProduct a (source N z) := by
    rw [show y = Fintype.linearCombination ℝ (rowVector N z) a from rfl,
      gramMatrix_quadratic, ha]
  have hxy : inner ℝ (errorVector N f) y = dotProduct a (source N z) := by
    rw [real_inner_comm, show y = Fintype.linearCombination ℝ (rowVector N z) a from rfl,
      inner_synthesis_left]
    simp_rw [error_observation hf z _ (hs _) (hs1 _) (hz _)]
    rfl
  rw [error_norm_sq_split hf, norm_sub_sq_real, hy, hxy]
  ring

/-- If the rows are independent, the energy is literally the inverse-Gram
quadratic, with the same complete square. -/
theorem legal_error_completion_inverse {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    [DecidableEq ι] (hi : LinearIndependent ℝ (rowVector N z)) :
    let a := (gramMatrix (rowVector N z))⁻¹.mulVec (source N z)
    ‖hilbertOne - f‖ ^ 2 =
      classWeight N (Fin.last N) + dotProduct (source N z) a +
        ‖errorVector N f - Fintype.linearCombination ℝ (rowVector N z) a‖ ^ 2 := by
  intro a
  have ha : (gramMatrix (rowVector N z)).mulVec a = source N z := by
    dsimp only [a]
    rw [gramMatrix_inverseSource hi, gramMatrix_mulVec]
    funext i
    exact RiemannResearch.Analysis.FiniteGramCapacity.inverseSource_normal hi _ i
  rw [legal_error_completion hf z hs hs1 hz a ha]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- At each running LCM and for any prescribed finite family of critical-line
zeros, there is a common solution of the normal equations for every legal trial. -/
theorem lcm_critical_line_completion (M : ℕ) (z : ι → ℂ)
    (hre : ∀ i, (z i).re = 1 / 2) (hz : ∀ i, riemannZeta (z i) = 0) :
    let N := Nat.lcmUpto M - 1
    ∃ a, (gramMatrix (rowVector N z)).mulVec a = source N z ∧
      ∀ f ∈ trialSpace (Nat.lcmUpto M),
        ‖hilbertOne - f‖ ^ 2 =
          classWeight N (Fin.last N) + dotProduct a (source N z) +
            ‖errorVector N f - Fintype.linearCombination ℝ (rowVector N z) a‖ ^ 2 := by
  intro N
  have hN : N + 1 = Nat.lcmUpto M := Nat.sub_add_cancel (Nat.lcmUpto_pos M)
  have hs (i : ι) : 0 < (z i).re := by rw [hre i]; norm_num
  have hs1 (i : ι) : z i ≠ 1 := by
    intro hi
    have h := hre i
    norm_num [hi] at h
  obtain ⟨a, ha⟩ := exists_zero_normal N z hs hs1 hz
  refine ⟨a, ha, fun f hf => ?_⟩
  exact legal_error_completion (hN.symm ▸ hf) z hs hs1 hz a ha

private theorem exists_distinct_critical_zeros (k : ℕ) :
    ∃ z : Fin k → ℂ, Function.Injective z ∧
      ∀ i, riemannZeta (z i) = 0 ∧ (z i).re = 1 / 2 ∧
        0 < (z i).im ∧ Zeta23.zeroMult (z i) = 1 := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨z, hzinj, hz⟩ := ih
    let H := ∑ i, |(z i).im|
    obtain ⟨ρ, hρ, hρre, hρim, hρsimple⟩ := exists_simple_critical_zero_above H
    let next : Fin (k + 1) → ℂ := Fin.snoc z ρ
    have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ => abs_nonneg (z i).im)
    have hne (i : Fin k) : z i ≠ ρ := by
      have hle : (z i).im ≤ H := (le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (z j).im) (Finset.mem_univ i))
      intro he
      exact (ne_of_lt (hle.trans_lt hρim)) (congrArg Complex.im he)
    refine ⟨next, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j
        refine Fin.lastCases (fun _ => rfl) (fun j hj => ?_) j
        exact False.elim ((hne j).symm (by simpa [next] using hj))
      · intro j
        refine Fin.lastCases (fun hj => ?_) (fun j hj => ?_) j
        · exact False.elim ((hne i) (by simpa [next] using hj))
        · exact congrArg Fin.castSucc (hzinj (by simpa [next] using hj))
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [next] using And.intro hρ (And.intro hρre (And.intro (hH.trans_lt hρim) hρsimple))
      · simpa [next] using hz j

/-- Every running LCM admits any prescribed number of distinct simple
positive-height critical-line zeros and a common normal-equation solution. -/
theorem exists_lcm_critical_line_family (M k : ℕ) :
    let N := Nat.lcmUpto M - 1
    ∃ (z : Fin k → ℂ) (a : Fin k × Bool → ℝ),
      Function.Injective z ∧
      (∀ i, riemannZeta (z i) = 0 ∧ (z i).re = 1 / 2 ∧
        0 < (z i).im ∧ Zeta23.zeroMult (z i) = 1) ∧
      (gramMatrix (rowVector N z)).mulVec a = source N z ∧
      ∀ f ∈ trialSpace (Nat.lcmUpto M),
        ‖hilbertOne - f‖ ^ 2 =
          classWeight N (Fin.last N) + dotProduct a (source N z) +
            ‖errorVector N f - Fintype.linearCombination ℝ (rowVector N z) a‖ ^ 2 := by
  obtain ⟨z, hzinj, hz⟩ := exists_distinct_critical_zeros k
  obtain ⟨a, ha, he⟩ := lcm_critical_line_completion M z (fun i => (hz i).2.1)
    (fun i => (hz i).1)
  exact ⟨z, a, hzinj, hz, ha, he⟩

end RiemannResearch.RH.Pareto.ResidueMellin

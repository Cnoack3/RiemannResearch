import RiemannResearch.RH.DyadicStepGram
import RiemannResearch.RH.DyadicBoundaryCompleteness

/-!
# Exact finite coordinates of the actual dyadic quotient

Source: user-provided `DyadicRegularizedVerificationContinuation20260910 (2).md`,
September 10, 2026, Appendix §1. This module formalizes the exact finite
orthogonal expansion and its Gram and signed-energy consequences in canonical
boundary coordinates. Identifying these coordinates with the explicit real
dyadic tents is a separate remaining step. No arithmetic bound is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Positive physical boundary indices, numbered from zero for finite sums. -/
def dyadicBoundaryVector (i : ℕ) : ThresholdHilbert :=
  dyadicQuotientProjection (dyadicStepBoundary (i+1) (by positivity))

/-- The canonical coefficient dual to a boundary of squared norm `1/4`. -/
def dyadicBoundaryCoordinate (f : ThresholdHilbert) (i : ℕ) : ℝ :=
  4 * inner ℝ (dyadicBoundaryVector i) f

def dyadicBoundaryFiniteSum (N : ℕ) (a : ℕ → ℝ) : ThresholdHilbert :=
  ∑ i ∈ Finset.range N, a i • dyadicBoundaryVector i

@[simp] theorem dyadicBoundaryVector_inner_one (i : ℕ) :
    inner ℝ (dyadicBoundaryVector i) hilbertOne = 0 :=
  dyadicProjectedBoundary_inner_one (i+1) (by positivity)

@[simp] theorem dyadicBoundaryVector_one_inner (i : ℕ) :
    inner ℝ hilbertOne (dyadicBoundaryVector i) = 0 := by
  rw [real_inner_comm, dyadicBoundaryVector_inner_one]

theorem dyadicBoundaryVector_inner (i j : ℕ) :
    inner ℝ (dyadicBoundaryVector i) (dyadicBoundaryVector j) =
      if i = j then (1/4 : ℝ) else 0 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, real_inner_self_eq_norm_sq]
    exact dyadicProjectedBoundary_norm_sq (i+1) (by positivity)
  · rw [if_neg h]
    exact dyadicProjectedBoundary_inner_boundary (i+1) (j+1)
      (by positivity) (by positivity) (by omega)

@[simp] theorem dyadicBoundaryVector_projection (i : ℕ) :
    dyadicQuotientProjection (dyadicBoundaryVector i) = dyadicBoundaryVector i :=
  Submodule.starProjection_eq_self_iff.mpr (dyadicQuotientProjection_mem _)

@[simp] theorem dyadicBoundaryFiniteSum_inner_one (N : ℕ) (a : ℕ → ℝ) :
    inner ℝ (dyadicBoundaryFiniteSum N a) hilbertOne = 0 := by
  unfold dyadicBoundaryFiniteSum
  rw [sum_inner]
  simp only [real_inner_smul_left, dyadicBoundaryVector_inner_one,
    mul_zero, Finset.sum_const_zero]

@[simp] theorem dyadicBoundaryFiniteSum_one_inner (N : ℕ) (a : ℕ → ℝ) :
    inner ℝ hilbertOne (dyadicBoundaryFiniteSum N a) = 0 := by
  rw [real_inner_comm, dyadicBoundaryFiniteSum_inner_one]

@[simp] theorem dyadicBoundaryFiniteSum_projection (N : ℕ) (a : ℕ → ℝ) :
    dyadicQuotientProjection (dyadicBoundaryFiniteSum N a) =
      dyadicBoundaryFiniteSum N a := by
  unfold dyadicBoundaryFiniteSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, dyadicBoundaryVector_projection]

theorem dyadicBoundaryFiniteSum_boundary_inner (N : ℕ) (a : ℕ → ℝ) (i : ℕ) :
    inner ℝ (dyadicBoundaryVector i) (dyadicBoundaryFiniteSum N a) =
      if i < N then (1/4 : ℝ) * a i else 0 := by
  classical
  unfold dyadicBoundaryFiniteSum
  rw [inner_sum]
  by_cases hi : i < N
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [real_inner_smul_right, dyadicBoundaryVector_inner, if_pos rfl]
      ring
    · intro j hj hji
      rw [real_inner_smul_right, dyadicBoundaryVector_inner,
        if_neg (Ne.symm hji), mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hi))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i ≠ j := by
      intro h
      subst j
      exact hi (Finset.mem_range.mp hj)
    rw [real_inner_smul_right, dyadicBoundaryVector_inner, if_neg hij, mul_zero]

/-- A finite boundary support hypothesis reconstructs the actual projection
exactly. There is no unobserved quotient component. -/
theorem dyadicQuotientProjection_eq_finite_boundary
    (f : ThresholdHilbert) (N : ℕ)
    (htail : ∀ i, N ≤ i → inner ℝ (dyadicBoundaryVector i) f = 0) :
    dyadicQuotientProjection f =
      (inner ℝ hilbertOne f) • hilbertOne +
        dyadicBoundaryFiniteSum N (dyadicBoundaryCoordinate f) := by
  let g := (inner ℝ hilbertOne f) • hilbertOne +
    dyadicBoundaryFiniteSum N (dyadicBoundaryCoordinate f)
  have heq : dyadicQuotientProjection f = dyadicQuotientProjection g := by
    apply dyadicQuotientProjection_eq_of_boundary_inner
    · dsimp [g]
      rw [inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
        dyadicBoundaryFiniteSum_one_inner]
      ring
    · intro l hl
      have hl1 : l-1+1 = l := by omega
      have hv : dyadicQuotientProjection (dyadicStepBoundary l hl) =
          dyadicBoundaryVector (l-1) := by
        unfold dyadicBoundaryVector
        simp only [hl1]
      rw [hv]
      dsimp [g]
      rw [inner_add_right, real_inner_smul_right,
        dyadicBoundaryVector_inner_one, mul_zero, zero_add,
        dyadicBoundaryFiniteSum_boundary_inner]
      by_cases h : l-1 < N
      · rw [if_pos h]
        unfold dyadicBoundaryCoordinate
        ring
      · rw [if_neg h]
        exact htail (l-1) (by omega)
  dsimp [g] at heq
  simpa only [map_add, map_smul, dyadicQuotientProjection_one,
    dyadicBoundaryFiniteSum_projection] using heq

theorem dyadicBoundaryFiniteSum_inner (N : ℕ) (a b : ℕ → ℝ) :
    inner ℝ (dyadicBoundaryFiniteSum N a) (dyadicBoundaryFiniteSum N b) =
      (1/4 : ℝ) * ∑ i ∈ Finset.range N, a i * b i := by
  exact dyadicProjectedBoundary_finite_inner (Finset.range N) a b
    (fun i => i+1) (fun _ => by positivity) (fun _ _ h => Nat.add_right_cancel h)

/-- Exact finite Parseval identity in canonical physical boundary coordinates. -/
theorem dyadicQuotientProjection_finite_boundary_norm_sq
    (f : ThresholdHilbert) (N : ℕ)
    (htail : ∀ i, N ≤ i → inner ℝ (dyadicBoundaryVector i) f = 0) :
    ‖dyadicQuotientProjection f‖^2 =
      (inner ℝ hilbertOne f)^2 +
        (1/4 : ℝ) * ∑ i ∈ Finset.range N, (dyadicBoundaryCoordinate f i)^2 := by
  rw [dyadicQuotientProjection_eq_finite_boundary f N htail]
  exact dyadicProjectedBoundary_finite_mean_energy (Finset.range N)
    (dyadicBoundaryCoordinate f) (fun i => i+1) (fun _ => by positivity)
    (fun _ _ h => Nat.add_right_cancel h) (inner ℝ hilbertOne f)

/-- Exact finite Gram formula, retaining every signed coordinate product. -/
theorem dyadicQuotientProjection_finite_boundary_inner
    (f g : ThresholdHilbert) (N : ℕ)
    (hf : ∀ i, N ≤ i → inner ℝ (dyadicBoundaryVector i) f = 0)
    (hg : ∀ i, N ≤ i → inner ℝ (dyadicBoundaryVector i) g = 0) :
    inner ℝ (dyadicQuotientProjection f) (dyadicQuotientProjection g) =
      inner ℝ hilbertOne f * inner ℝ hilbertOne g +
        (1/4 : ℝ) * ∑ i ∈ Finset.range N,
          dyadicBoundaryCoordinate f i * dyadicBoundaryCoordinate g i := by
  rw [dyadicQuotientProjection_eq_finite_boundary f N hf,
    dyadicQuotientProjection_eq_finite_boundary g N hg,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    real_inner_smul_left, dyadicBoundaryFiniteSum_one_inner,
    real_inner_smul_right, dyadicBoundaryFiniteSum_inner_one,
    dyadicBoundaryFiniteSum_inner]
  ring

theorem dyadicProjectedStep_boundary_tail (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hmN : m ≤ 2*(N+1)) :
    ∀ i, N ≤ i → inner ℝ (dyadicBoundaryVector i) (dyadicProjectedStep m hm) = 0 := by
  intro i hi
  exact dyadicProjectedBoundary_inner_step (i+1) (by positivity) m hm (by omega)

/-- The actual integer step has an exact finite boundary expansion. -/
theorem dyadicProjectedStep_eq_finite_boundary (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hmN : m ≤ 2*(N+1)) :
    dyadicProjectedStep m hm = hilbertOne +
      dyadicBoundaryFiniteSum N (dyadicBoundaryCoordinate (dyadicProjectedStep m hm)) := by
  have h := dyadicQuotientProjection_eq_finite_boundary (dyadicProjectedStep m hm) N
    (dyadicProjectedStep_boundary_tail m hm N hmN)
  have hfix : dyadicQuotientProjection (dyadicProjectedStep m hm) =
      dyadicProjectedStep m hm :=
    Submodule.starProjection_eq_self_iff.mpr (dyadicQuotientProjection_mem _)
  have hmean : inner ℝ hilbertOne (dyadicProjectedStep m hm) = 1 := by
    rw [real_inner_comm, dyadicProjectedStep_inner_one]
  simpa only [hfix, hmean, one_smul] using h

/-- An unconditional finite exact kernel for any two positive integer steps. -/
theorem dyadicProjectedStep_finite_boundary_inner
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (N : ℕ)
    (hmN : m ≤ 2*(N+1)) (hnN : n ≤ 2*(N+1)) :
    inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) =
      1 + (1/4 : ℝ) * ∑ i ∈ Finset.range N,
        dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
          dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i := by
  have h := dyadicQuotientProjection_finite_boundary_inner
    (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) N
    (dyadicProjectedStep_boundary_tail m hm N hmN)
    (dyadicProjectedStep_boundary_tail n hn N hnN)
  have hfix (k : ℕ) (hk : 0 < k) :
      dyadicQuotientProjection (dyadicProjectedStep k hk) =
        dyadicProjectedStep k hk :=
    Submodule.starProjection_eq_self_iff.mpr (dyadicQuotientProjection_mem _)
  have hmean (k : ℕ) (hk : 0 < k) :
      inner ℝ hilbertOne (dyadicProjectedStep k hk) = 1 := by
    rw [real_inner_comm, dyadicProjectedStep_inner_one]
  simpa only [hfix, hmean, one_mul] using h

@[simp] theorem dyadicBoundaryCoordinate_one (i : ℕ) :
    dyadicBoundaryCoordinate hilbertOne i = 0 := by
  simp only [dyadicBoundaryCoordinate, dyadicBoundaryVector_inner_one, mul_zero]

theorem dyadicBoundaryCoordinate_step_zero (m : ℕ) (hm : 0 < m) (i : ℕ)
    (hmi : m ≤ 2*(i+1)) :
    dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i = 0 := by
  unfold dyadicBoundaryCoordinate
  rw [dyadicProjectedStep_boundary_tail m hm i hmi i (le_refl i), mul_zero]

theorem dyadicBoundaryCoordinate_step_double (m : ℕ) (hm : 0 < m) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicProjectedStep (2*m) (by positivity)) i =
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i := by
  rw [dyadicProjectedStep_double m hm]

theorem dyadicBoundaryCoordinate_boundary (l : ℕ) (hl : 0 < l) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicQuotientProjection (dyadicStepBoundary l hl)) i =
      if i+1 = l then 1 else 0 := by
  unfold dyadicBoundaryCoordinate dyadicBoundaryVector
  by_cases h : i+1 = l
  · subst l
    rw [if_pos rfl, real_inner_self_eq_norm_sq,
      dyadicProjectedBoundary_norm_sq]
    norm_num
  · rw [if_neg h, dyadicProjectedBoundary_inner_boundary (i+1) l
      (by positivity) hl h, mul_zero]

/-- Canonical boundary coefficients satisfy the same midpoint recursion as
the finite dyadic tents, including the new unit-height boundary coefficient. -/
theorem dyadicBoundaryCoordinate_step_odd (l : ℕ) (hl : 0 < l) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicProjectedStep (2*l+1) (by positivity)) i =
      (if i+1 = l then 1 else 0) + (1/2 : ℝ) *
        (dyadicBoundaryCoordinate (dyadicProjectedStep l hl) i +
          dyadicBoundaryCoordinate (dyadicProjectedStep (l+1) (by positivity)) i) := by
  have hb := dyadicBoundaryCoordinate_boundary l hl i
  unfold dyadicBoundaryCoordinate at hb ⊢
  rw [dyadicProjectedStep_odd_recurrence l hl, inner_add_right,
    real_inner_smul_right, inner_add_right]
  linarith

/-- Actual finite boundary coefficients lie in `[0,1]`; this is proved from
the physical refinement, without assuming the geometric tent formula. -/
theorem dyadicBoundaryCoordinate_step_mem_unit (m : ℕ) (hm : 0 < m) (i : ℕ) :
    0 ≤ dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i ∧
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h1 : m = 1
    · subst m
      simp only [dyadicProjectedStep_one, dyadicBoundaryCoordinate_one]
      norm_num
    have hm2 : 2 ≤ m := by omega
    have hl : 0 < m/2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    by_cases he : m % 2 = 0
    · have hmform : m = 2*(m/2) := by omega
      have hv : dyadicProjectedStep m hm = dyadicProjectedStep (m/2) hl := by
        simpa only [← hmform] using dyadicProjectedStep_double (m/2) hl
      rw [hv]
      exact ih (m/2) (by omega) hl
    · have hmform : m = 2*(m/2)+1 := by omega
      have hv : dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i =
          (if i+1 = m/2 then 1 else 0) + (1/2 : ℝ) *
            (dyadicBoundaryCoordinate (dyadicProjectedStep (m/2) hl) i +
              dyadicBoundaryCoordinate
                (dyadicProjectedStep (m/2+1) (by positivity)) i) := by
        simpa only [← hmform] using dyadicBoundaryCoordinate_step_odd (m/2) hl i
      rw [hv]
      by_cases hi : i+1 = m/2
      · rw [if_pos hi,
          dyadicBoundaryCoordinate_step_zero (m/2) hl i (by omega),
          dyadicBoundaryCoordinate_step_zero (m/2+1) (by positivity) i (by omega)]
        norm_num
      · rw [if_neg hi]
        have ha := ih (m/2) (by omega) hl
        have hb := ih (m/2+1) (by omega) (by positivity)
        constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- The exact actual step kernel is at least one. Absolute values therefore
do not alter it in the off-diagonal majorant problem. -/
theorem dyadicProjectedStep_inner_ge_one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    1 ≤ inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) := by
  rw [dyadicProjectedStep_finite_boundary_inner m n hm hn (m+n) (by omega) (by omega)]
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m+n),
      dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i *
        dyadicBoundaryCoordinate (dyadicProjectedStep n hn) i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (dyadicBoundaryCoordinate_step_mem_unit m hm i).1
      (dyadicBoundaryCoordinate_step_mem_unit n hn i).1
  linarith

/-- All signed mixed step energies are retained inside exact boundary squares.
The common cutoff is finite and may be chosen for any finite index family. -/
theorem dyadicProjectedStep_finite_boundary_error_sq
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (c : ι → ℝ) (N : ℕ) (hmN : ∀ i ∈ s, m i ≤ 2*(N+1)) :
    ‖(∑ i ∈ s, c i • dyadicProjectedStep (m i) (hm i)) - hilbertOne‖^2 =
      ((∑ i ∈ s, c i)-1)^2 + (1/4 : ℝ) * ∑ j ∈ Finset.range N,
        (∑ i ∈ s, c i *
          dyadicBoundaryCoordinate (dyadicProjectedStep (m i) (hm i)) j)^2 := by
  let f := (∑ i ∈ s, c i • dyadicProjectedStep (m i) (hm i)) - hilbertOne
  have hstep (k : ℕ) (hk : 0 < k) :
      dyadicQuotientProjection (dyadicProjectedStep k hk) =
        dyadicProjectedStep k hk :=
    Submodule.starProjection_eq_self_iff.mpr (dyadicQuotientProjection_mem _)
  have hfix : dyadicQuotientProjection f = f := by
    dsimp [f]
    simp only [map_sub, map_sum, map_smul, hstep, dyadicQuotientProjection_one]
  have htail : ∀ j, N ≤ j → inner ℝ (dyadicBoundaryVector j) f = 0 := by
    intro j hj
    dsimp [f]
    rw [inner_sub_right, inner_sum, dyadicBoundaryVector_inner_one, sub_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [real_inner_smul_right,
      dyadicProjectedStep_boundary_tail (m i) (hm i) N (hmN i hi) j hj, mul_zero]
  have hmean : inner ℝ hilbertOne f = (∑ i ∈ s, c i)-1 := by
    dsimp [f]
    rw [real_inner_comm, inner_sub_left, dyadicProjectedStep_sum_inner_one,
      real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  have hcoord (j : ℕ) : dyadicBoundaryCoordinate f j =
      ∑ i ∈ s, c i *
        dyadicBoundaryCoordinate (dyadicProjectedStep (m i) (hm i)) j := by
    dsimp [f, dyadicBoundaryCoordinate]
    rw [inner_sub_right, inner_sum, dyadicBoundaryVector_inner_one, sub_zero,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_right]
    ring
  have h := dyadicQuotientProjection_finite_boundary_norm_sq f N htail
  simpa only [hfix, hmean, hcoord] using h

end
end RiemannResearch.RH.Pareto

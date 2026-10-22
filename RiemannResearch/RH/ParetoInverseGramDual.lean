import RiemannResearch.Analysis.FiniteHilbertGramDual
import RiemannResearch.RH.ResidueClosureDensity

/-!
# Pareto inverse Gram entries and their exact limits
Source: user-provided Pareto_Lean_Research_Connections_2026-09-23(1).md,
equations (1)--(5). Stage n means g_2,...,g_(n+1).
The dual is the negative of the project's positive Mobius Riesz vector.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk

def coefficientDual (i : ℕ) : ThresholdHilbert := -mobiusRieszHilbert (i + 2)

theorem coefficientDual_pair (i j : ℕ) :
    inner ℝ (residueAtom i) (coefficientDual j) = if i = j then 1 else 0 := by
  rw [real_inner_comm]
  simpa only [coefficientDual, inner_neg_left, mobiusRieszHilbert_inner,
    coefficientCLM, neg_apply, eq_comm] using coefficientCLM_biorthogonal j i

theorem finiteResidue_independent (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => residueAtom i.val) :=
  residueAtom_linearIndependent.comp _ Fin.val_injective

theorem finiteResidue_dual (n : ℕ) (i j : Fin n) :
    inner ℝ (residueAtom i.val) (coefficientDual j.val) = if i = j then 1 else 0 := by
  simpa only [Fin.ext_iff] using coefficientDual_pair i.val j.val

def residueInverseEntry (n : ℕ) (i j : Fin n) : ℝ :=
  inverseEntry (finiteResidue_independent n) i j

theorem residueInverseEntry_projection (n : ℕ) (i j : Fin n) :
    residueInverseEntry n i j =
      inner ℝ ((finiteSpace n).starProjection (coefficientDual i.val))
        ((finiteSpace n).starProjection (coefficientDual j.val)) := by
  rw [residueInverseEntry, inverseEntry_symm_of_dual
    (finiteResidue_independent n) (finiteResidue_dual n) i j]
  exact (projection_dual_inner (finiteResidue_independent n) (finiteResidue_dual n) i j).symm

theorem residueInverseEntry_residual (n : ℕ) (i j : Fin n) :
    inner ℝ (coefficientDual i.val - (finiteSpace n).starProjection (coefficientDual i.val))
      (coefficientDual j.val - (finiteSpace n).starProjection (coefficientDual j.val)) =
      inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
        residueInverseEntry n i j :=
  residual_dual_bilinear (finiteResidue_independent n) (finiteResidue_dual n) i j

theorem residueInverseEntry_diagonal (n : ℕ) (i : Fin n) :
    ‖coefficientDual i.val - (finiteSpace n).starProjection (coefficientDual i.val)‖ ^ 2 =
      ‖coefficientDual i.val‖ ^ 2 - residueInverseEntry n i i :=
  residual_dual_norm_sq (finiteResidue_independent n) (finiteResidue_dual n) i

/-- Zero padding only affects the finitely many stages before both indices occur. -/
def fixedInverseEntry (n i j : ℕ) : ℝ :=
  if hij : i < n ∧ j < n then
    residueInverseEntry n ⟨i, hij.1⟩ ⟨j, hij.2⟩ else 0

theorem fixedInverseEntry_eventually (i j : ℕ) :
    ∀ᶠ n in atTop, fixedInverseEntry n i j =
      inner ℝ ((finiteSpace n).starProjection (coefficientDual i))
        ((finiteSpace n).starProjection (coefficientDual j)) := by
  filter_upwards [eventually_ge_atTop (max i j + 1)] with n hn
  have hi : i < n := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left i j)) hn
  have hj : j < n := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right i j)) hn
  simp only [fixedInverseEntry, dif_pos (And.intro hi hj), residueInverseEntry_projection]

theorem fixedInverseEntry_tendsto (i j : ℕ) :
    Tendsto (fun n => fixedInverseEntry n i j) atTop
      (𝓝 (inner ℝ (closedSpace.starProjection (coefficientDual i))
        (closedSpace.starProjection (coefficientDual j)))) := by
  have ht := (walkProjection_tendsto residueAtom id Function.surjective_id
    (coefficientDual i)).inner (𝕜 := ℝ)
    (walkProjection_tendsto residueAtom id Function.surjective_id (coefficientDual j))
  exact ht.congr' (Filter.EventuallyEq.symm (fixedInverseEntry_eventually i j))

theorem coefficientDual_norm_sq (i : ℕ) :
    ‖coefficientDual i‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 (i + 2),
        (k : ℝ) * ((k : ℝ) + 1) *
          (dualCoeff (i + 2) k : ℝ) ^ 2 := by
  rw [coefficientDual, norm_neg, mobiusRieszHilbert_norm,
    mobiusDifferenceCLM_norm_sq (i + 2) (by omega)]

theorem fixedInverseEntry_diagonal_iff_mem (i : ℕ) :
    Tendsto (fun n => fixedInverseEntry n i i) atTop (𝓝 (‖coefficientDual i‖ ^ 2)) ↔
      coefficientDual i ∈ closedSpace := by
  constructor
  · intro ht
    have he := tendsto_nhds_unique (fixedInverseEntry_tendsto i i) ht
    rw [real_inner_self_eq_norm_sq] at he
    have ho : inner ℝ (coefficientDual i - closedSpace.starProjection (coefficientDual i))
        (closedSpace.starProjection (coefficientDual i)) = 0 := by
      rw [real_inner_comm]
      exact (closedSpace.mem_orthogonal _).mp
        (Submodule.sub_starProjection_mem_orthogonal (coefficientDual i)) _
        (closedSpace.starProjection_apply_mem _)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
    have hz : ‖coefficientDual i - closedSpace.starProjection (coefficientDual i)‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real]
      linarith
    have hp : closedSpace.starProjection (coefficientDual i) = coefficientDual i := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
    exact Submodule.starProjection_eq_self_iff.mp hp
  · intro hm
    simpa only [Submodule.starProjection_eq_self_iff.mpr hm, real_inner_self_eq_norm_sq]
      using fixedInverseEntry_tendsto i i

theorem one_mem_iff_all_dual_mem :
    hilbertOne ∈ closedSpace ↔ ∀ i, coefficientDual i ∈ closedSpace := by
  constructor
  · intro h i
    rw [closedSpace_eq_top_iff_one_mem.mpr h]
    trivial
  · intro h
    apply limitEnergy_zero_iff_mem.mp
    apply limitResidual_zero_iff_energy_zero.mp
    apply residual_zero_of_mobiusRiesz_mem
    intro m hm
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
    simpa only [coefficientDual, neg_neg] using closedSpace.neg_mem (h i)

theorem one_mem_iff_inverse_diagonals :
    hilbertOne ∈ closedSpace ↔ ∀ i,
      Tendsto (fun n => fixedInverseEntry n i i) atTop (𝓝 (‖coefficientDual i‖ ^ 2)) := by
  rw [one_mem_iff_all_dual_mem]
  exact forall_congr' fun i => (fixedInverseEntry_diagonal_iff_mem i).symm


theorem coefficientDual_two_norm_sq : ‖coefficientDual 0‖ ^ 2 = 14 := by
  rw [coefficientDual_norm_sq]
  norm_num [show Finset.Icc 1 (0 + 2) = {1, 2} by decide, dualCoeff,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem coefficientDual_three_norm_sq : ‖coefficientDual 1‖ ^ 2 = 20 := by
  rw [coefficientDual_norm_sq]
  norm_num [show Finset.Icc 1 (1 + 2) = {1, 2, 3} by decide, dualCoeff,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

theorem coefficientDual_two_three_inner :
    inner ℝ (coefficientDual 0) (coefficientDual 1) = -2 := by
  simp only [coefficientDual, inner_neg_left, inner_neg_right, neg_neg,
    mobiusRieszHilbert_inner, mobiusDifferenceCLM_apply]
  norm_num only
  unfold mobiusDifference
  simp_rw [mobiusRieszHilbert_sequence 3 _ (by omega)]
  norm_num [show Nat.divisors 2 = {1, 2} by decide, dualCoeff,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

theorem inverse_two_tendsto_iff_mem :
    Tendsto (fun n => fixedInverseEntry n 0 0) atTop (𝓝 14) ↔
      coefficientDual 0 ∈ closedSpace := by
  simpa only [coefficientDual_two_norm_sq] using fixedInverseEntry_diagonal_iff_mem 0

theorem inverse_three_tendsto_iff_mem :
    Tendsto (fun n => fixedInverseEntry n 1 1) atTop (𝓝 20) ↔
      coefficientDual 1 ∈ closedSpace := by
  simpa only [coefficientDual_three_norm_sq] using fixedInverseEntry_diagonal_iff_mem 1


end RiemannResearch.RH.Pareto.CoefficientStabilization

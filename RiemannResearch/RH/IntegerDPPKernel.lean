import RiemannResearch.RH.IntegerDPPHazards
import RiemannResearch.RH.IntegerDPPClosure

/-!
Source: user-provided DPP Markdown handoff (2026-09-20), Section 1. The counting kernel is
defined directly by the actual arithmetic orthogonal projections. No generic
projection-kernel theorem is needed for the first-site marginal identity.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

def countingBasis (n : ℕ) : ThresholdHilbert := lp.single 2 n (1 : ℝ)

def integerKernel (n i j : ℕ) : ℝ :=
  inner ℝ ((finiteSpace n).starProjection (countingBasis i))
    ((finiteSpace n).starProjection (countingBasis j))

def limitingKernel (i j : ℕ) : ℝ :=
  inner ℝ (closedSpace.starProjection (countingBasis i))
    (closedSpace.starProjection (countingBasis j))

private theorem countingBasis_apply_aux (n k : ℕ) :
    countingBasis n k = if k = n then 1 else 0 := by
  by_cases hk : k = n
  · subst k
    simp [countingBasis]
  · simp [countingBasis, hk]

theorem countingBasis_norm_sq (n : ℕ) :
    ‖countingBasis n‖ ^ 2 = 1 := by
  rw [hilbert_norm_sq]
  simp [countingBasis_apply_aux]

theorem paretoPoint_eq_sqrt_smul_countingBasis (n : ℕ) :
    paretoPointHilbert n = Real.sqrt (paretoWeight n) • countingBasis n := by
  apply Subtype.ext
  funext k
  by_cases hk : k = n
  · subst k
    simp [paretoPointHilbert, sequenceHilbert, paretoPointSequence, countingBasis]
  · simp [paretoPointHilbert, sequenceHilbert, paretoPointSequence, countingBasis, hk]

theorem first_site_projection_complement (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] :
    1 - inner ℝ (S.starProjection (countingBasis 0))
      (S.starProjection (countingBasis 0)) =
      2 * ‖paretoPointHilbert 0 - S.starProjection (paretoPointHilbert 0)‖ ^ 2 := by
  have henergy : (1 : ℝ) =
      ‖countingBasis 0 - S.starProjection (countingBasis 0)‖ ^ 2 +
      ‖S.starProjection (countingBasis 0)‖ ^ 2 := by
    have ht := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
      S bot_le (countingBasis 0)
    simpa [countingBasis_norm_sq] using ht
  have hscale :
      ‖paretoPointHilbert 0 - S.starProjection (paretoPointHilbert 0)‖ ^ 2 =
      paretoWeight 0 *
        ‖countingBasis 0 - S.starProjection (countingBasis 0)‖ ^ 2 := by
    rw [paretoPoint_eq_sqrt_smul_countingBasis, map_smul, ← smul_sub,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (paretoWeight_pos 0).le]
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at hscale
  rw [real_inner_self_eq_norm_sq]
  linarith

theorem vacancy_eq_kernel_complement (n : ℕ) :
    vacancy n = 1 - integerKernel n 0 0 := by
  exact (first_site_projection_complement (finiteSpace n)).symm

theorem limitingVacancy_eq_kernel_complement :
    limitingVacancy = 1 - limitingKernel 0 0 := by
  exact (first_site_projection_complement closedSpace).symm

theorem integerKernel_tendsto (i j : ℕ) :
    Tendsto (fun n => integerKernel n i j) atTop (𝓝 (limitingKernel i j)) := by
  exact (walkProjection_tendsto residueAtom id Function.surjective_id (countingBasis i)).inner
    (walkProjection_tendsto residueAtom id Function.surjective_id (countingBasis j))

theorem limitingKernel_first_site_one_iff_odd_carry :
    limitingKernel 0 0 = 1 ↔
      (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
        doublingCarryHilbert d (by omega) ∈ closedSpace) := by
  have he : limitingKernel 0 0 = 1 ↔ limitingVacancy = 0 := by
    rw [limitingVacancy_eq_kernel_complement]
    constructor <;> intro h <;> linarith
  exact he.trans limitingVacancy_zero_iff_odd_carry

end RiemannResearch.RH.Pareto.IntegerDPP

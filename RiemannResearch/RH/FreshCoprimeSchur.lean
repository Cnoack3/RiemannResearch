import RiemannResearch.RH.FreshCoprimeDecomposition
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur

/-!
# The actual signed Schur contribution of the fresh coprime-to-six block

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 6, for the exact arithmetic Schur decomposition.
Independence and inverse-Gram existence are proved for the concrete columns.
No lower bound on their actual correlations is assumed or asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket
open RiemannResearch.Analysis.FiniteHilbertGram

def transportError (M : ℕ) : ThresholdHilbert :=
  hilbertOne - (transportedSpace M).starProjection hilbertOne

def freshScreenLinear (M : ℕ) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert :=
  (ContinuousLinearMap.id ℝ ThresholdHilbert - (transportedSpace M).starProjection).toLinearMap

def screenedFresh (M : ℕ) (i : freshIndices M) : ThresholdHilbert :=
  freshScreenLinear M (freshFamily M i)

theorem screenedFresh_eq (M : ℕ) (i : freshIndices M) :
    screenedFresh M i = freshFamily M i -
      (transportedSpace M).starProjection (freshFamily M i) := rfl

theorem freshFamily_mem (M : ℕ) (i : freshIndices M) :
    freshFamily M i ∈ freshSpace M := by
  rw [← freshFamily_span]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem transportedSpace_le_budget (M : ℕ) :
    transportedSpace M ≤ budgetHilbert (2*M) := by
  rw [← transportedSpace_sup_freshSpace]
  exact le_sup_left

theorem freshSpace_le_budget (M : ℕ) : freshSpace M ≤ budgetHilbert (2*M) := by
  rw [← transportedSpace_sup_freshSpace]
  exact le_sup_right

theorem screenedFresh_mem_budget (M : ℕ) (i : freshIndices M) :
    screenedFresh M i ∈ budgetHilbert (2*M) :=
  (budgetHilbert (2*M)).sub_mem
    (freshSpace_le_budget M (freshFamily_mem M i))
    (transportedSpace_le_budget M ((transportedSpace M).starProjection_apply_mem _))

theorem screenedFresh_mem_orthogonal (M : ℕ) (i : freshIndices M) :
    screenedFresh M i ∈ (transportedSpace M)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- Algebraic directness proves invertibility after the actual old-space screening. -/
theorem screenedFresh_linearIndependent (M : ℕ) :
    LinearIndependent ℝ (screenedFresh M) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hz i hi
  let v : ThresholdHilbert := ∑ j ∈ s, c j • freshFamily M j
  have hv : v ∈ freshSpace M := by
    exact (freshSpace M).sum_mem (fun j hj =>
      (freshSpace M).smul_mem (c j) (freshFamily_mem M j))
  have hscreen : freshScreenLinear M v = 0 := by
    simpa only [v, map_sum, map_smul, screenedFresh] using hz
  have hsame : v = (transportedSpace M).starProjection v :=
    sub_eq_zero.mp hscreen
  have hvU : v ∈ transportedSpace M := by
    rw [hsame]
    exact (transportedSpace M).starProjection_apply_mem v
  have hvzero : v = 0 :=
    (transportedSpace_disjoint_freshSpace M).le_bot ⟨hvU, hv⟩
  exact (linearIndependent_iff'.mp (freshFamily_linearIndependent M)) s c hvzero i hi

/-- Coefficients of the actual inverse signed Gram matrix. -/
def freshCoefficients (M : ℕ) : freshIndices M → ℝ :=
  inverseCoeff (screenedFresh_linearIndependent M) (transportError M)

def freshFit (M : ℕ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ (screenedFresh M) (freshCoefficients M)

def freshRemainder (M : ℕ) : ℝ :=
  ∑ i, freshCoefficients M i * cross (screenedFresh M) (transportError M) i

theorem freshFit_normal (M : ℕ) (i : freshIndices M) :
    inner ℝ (screenedFresh M i) (freshFit M) =
      inner ℝ (screenedFresh M i) (transportError M) :=
  inverseCoeff_normal (screenedFresh_linearIndependent M) (transportError M) i

theorem freshFit_mem_budget (M : ℕ) : freshFit M ∈ budgetHilbert (2*M) := by
  unfold freshFit
  rw [Fintype.linearCombination_apply]
  exact (budgetHilbert (2*M)).sum_mem (fun i hi =>
    (budgetHilbert (2*M)).smul_mem _ (screenedFresh_mem_budget M i))

theorem freshFit_mem_orthogonal (M : ℕ) : freshFit M ∈ (transportedSpace M)ᗮ := by
  unfold freshFit
  rw [Fintype.linearCombination_apply]
  exact ((transportedSpace M)ᗮ).sum_mem (fun i hi =>
    ((transportedSpace M)ᗮ).smul_mem _ (screenedFresh_mem_orthogonal M i))

theorem freshFit_norm_sq (M : ℕ) : ‖freshFit M‖^2 = freshRemainder M := by
  unfold freshFit
  rw [gram_quadratic]
  apply Finset.sum_congr rfl
  intro i hi
  change freshCoefficients M i * inner ℝ (screenedFresh M i) (freshFit M) = _
  rw [freshFit_normal]
  rfl

theorem freshRemainder_nonneg (M : ℕ) : 0 ≤ freshRemainder M := by
  rw [← freshFit_norm_sq]
  positivity

theorem freshFit_correlation_error (M : ℕ) :
    inner ℝ (error M) (freshFit M) = freshRemainder M := by
  have hu : inner ℝ ((transportedSpace M).starProjection hilbertOne) (freshFit M) = 0 :=
    ((transportedSpace M).mem_orthogonal _).mp (freshFit_mem_orthogonal M) _
      ((transportedSpace M).starProjection_apply_mem _)
  have ho : inner ℝ (fit M) (freshFit M) = 0 :=
    ((transportedSpace M).mem_orthogonal _).mp (freshFit_mem_orthogonal M) _
      (budget_le_transportedSpace M ((budgetHilbert M).starProjection_apply_mem _))
  have hc : inner ℝ (transportError M) (freshFit M) = freshRemainder M := by
    rw [real_inner_comm]
    exact inner_synthesis_left (screenedFresh M) (freshCoefficients M) (transportError M)
  unfold transportError at hc
  rw [inner_sub_left, hu, sub_zero] at hc
  unfold error
  rw [inner_sub_left, ho, sub_zero]
  exact hc

/-- An exact normalized witness supplied by the fresh block whenever its actual source is nonzero. -/
theorem fresh_normalized_correction (M : ℕ) (hR : 0 < freshRemainder M) :
    let w := (distance M / freshRemainder M) • freshFit M
    w ∈ budgetHilbert (2*M) ∧
      w ∈ (budgetHilbert M)ᗮ ∧
      inner ℝ (error M) w = distance M ∧
      ‖w‖^2 = (distance M)^2 / freshRemainder M := by
  dsimp only
  refine ⟨(budgetHilbert (2*M)).smul_mem _ (freshFit_mem_budget M), ?_, ?_, ?_⟩
  · apply ((budgetHilbert M)ᗮ).smul_mem
    apply ((budgetHilbert M).mem_orthogonal _).mpr
    intro x hx
    exact ((transportedSpace M).mem_orthogonal _).mp (freshFit_mem_orthogonal M) x
      (budget_le_transportedSpace M hx)
  · rw [real_inner_smul_right, freshFit_correlation_error]
    field_simp [ne_of_gt hR]
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, freshFit_norm_sq]
    field_simp [ne_of_gt hR]

private theorem fresh_residual_inner_old (M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ transportedSpace M) :
    inner ℝ (transportError M - freshFit M) x = 0 := by
  have h1 : inner ℝ (transportError M) x = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne x hx
  have h2 : inner ℝ (freshFit M) x = 0 := by
    rw [real_inner_comm]
    exact ((transportedSpace M).mem_orthogonal _).mp (freshFit_mem_orthogonal M) x hx
  rw [inner_sub_left, h1, h2, sub_self]

private theorem fresh_residual_inner_raw (M : ℕ) (i : freshIndices M) :
    inner ℝ (transportError M - freshFit M) (freshFamily M i) = 0 := by
  have hscreen : inner ℝ (transportError M - freshFit M) (screenedFresh M i) = 0 := by
    rw [real_inner_comm, inner_sub_right, freshFit_normal, sub_self]
  have hold := fresh_residual_inner_old M
    ((transportedSpace M).starProjection (freshFamily M i))
    ((transportedSpace M).starProjection_apply_mem _)
  rw [screenedFresh_eq, inner_sub_right, hold, sub_zero] at hscreen
  exact hscreen

private theorem fresh_residual_inner_budget (M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ budgetHilbert (2*M)) :
    inner ℝ (transportError M - freshFit M) x = 0 := by
  rw [← transportedSpace_sup_freshSpace] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [inner_add_right, fresh_residual_inner_old M u hu, zero_add]
  rw [← freshFamily_span] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact fresh_residual_inner_raw M i
  | zero => exact inner_zero_right _
  | add x y hx hy ihx ihy => rw [inner_add_right, ihx, ihy, add_zero]
  | smul c x hx ih => rw [real_inner_smul_right, ih, mul_zero]

/-- The full enlarged projection is the transported fit plus the fresh Schur fit. -/
theorem doubled_fit_eq_transport_add_fresh (M : ℕ) :
    fit (2*M) = (transportedSpace M).starProjection hilbertOne + freshFit M := by
  let d := (transportedSpace M).starProjection hilbertOne + freshFit M - fit (2*M)
  have hd : d ∈ budgetHilbert (2*M) :=
    (budgetHilbert (2*M)).sub_mem
      ((budgetHilbert (2*M)).add_mem
        (transportedSpace_le_budget M ((transportedSpace M).starProjection_apply_mem _))
        (freshFit_mem_budget M))
      ((budgetHilbert (2*M)).starProjection_apply_mem _)
  have hnew := fresh_residual_inner_budget M d hd
  have hold : inner ℝ (error (2*M)) d = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne d hd
  have heq : transportError M - freshFit M = error (2*M) - d := by
    unfold d transportError error fit
    abel
  rw [heq, inner_sub_left, hold, real_inner_self_eq_norm_sq] at hnew
  have hn : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  have hd0 : d = 0 := norm_eq_zero.mp hn
  exact (sub_eq_zero.mp hd0).symm

/-- This is the actual `zᵀ K⁻¹ z`, added to the actual transported improvement. -/
theorem full_gain_eq_transport_add_fresh (M : ℕ) :
    gain M = (distance M - ‖transportError M‖^2) + freshRemainder M := by
  have he := residual_schur_value (screenedFresh_linearIndependent M) (transportError M)
  change ‖transportError M - freshFit M‖^2 =
    ‖transportError M‖^2 - freshRemainder M at he
  have herr : error (2*M) = transportError M - freshFit M := by
    unfold error
    rw [doubled_fit_eq_transport_add_fresh]
    unfold transportError
    abel
  unfold gain distance
  rw [herr, he]
  ring

/-- Full signed Schur entries, with old projection covariance retained exactly. -/
theorem screenedFresh_inner (M : ℕ) (i j : freshIndices M) :
    inner ℝ (screenedFresh M i) (screenedFresh M j) =
      inner ℝ (freshFamily M i) (freshFamily M j) -
        inner ℝ ((transportedSpace M).starProjection (freshFamily M i))
          ((transportedSpace M).starProjection (freshFamily M j)) :=
  RiemannResearch.LinearAlgebra.inner_residualized_eq_schur
    (transportedSpace M) (freshFamily M i) (freshFamily M j)

/-- Actual residual source after refitting every transported old coefficient. -/
theorem screenedFresh_source (M : ℕ) (i : freshIndices M) :
    inner ℝ (transportError M) (screenedFresh M i) =
      inner ℝ hilbertOne (freshFamily M i) -
        inner ℝ ((transportedSpace M).starProjection hilbertOne)
          ((transportedSpace M).starProjection (freshFamily M i)) :=
  RiemannResearch.LinearAlgebra.inner_residualized_eq_schur
    (transportedSpace M) hilbertOne (freshFamily M i)

end RiemannResearch.RH.Pareto.CoupledResidual

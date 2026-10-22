import RiemannResearch.RH.NoorShiftedResidueDensity
import RiemannResearch.Analysis.ShiftedLiftApproximation

/-!
# Unscaled regularized approximation by finite arithmetic lifts

Source: the user-requested continuation of commit 8a7abbde and Route 3 of
RH/ActualResidualRegularityRoutes20260924.md. The arithmetic input is the
repository's kernel-verified Noor.shiftedResidue_density, whose source is
S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte criterion for the
RH", Theorem 9, https://arxiv.org/abs/1809.09577. That citation supports the
shifted-density input, not a quantitative regularization rate.

This module instantiates the finite minimization and approximation lemmas
with the actual residue atoms and actual finite projection residuals.
No RH, residual regularity, unshifted density, or rate assumption enters
finiteMinimum_tendsto_zero or exists_finite_minimizing_lifts.

The separate RH reduction explicitly requires divided-energy convergence.
Neither unscaled convergence nor finite attainment proves that hypothesis.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.ShiftedLift
open RiemannResearch.Analysis.ExhaustiveWalk
open CoefficientStabilization

/-- Hardy coordinates of the span of g_2 through g_(N+1). -/
def finiteLiftSpace (N : ℕ) : Submodule ℝ Space :=
  walkSpan (fun i => hardyCoordinates (residueAtom i)) id N

instance finiteLiftSpace_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (finiteLiftSpace N) := by
  unfold finiteLiftSpace
  infer_instance

/-- The actual finite projection residual, expressed in Hardy coordinates. -/
def finiteTarget (N : ℕ) : Space :=
  hardyCoordinates (hilbertOne - projection N)

/-- The full regularized energy infimum; it is attained for t > 0. -/
def finiteMinimum (N : ℕ) (t : ℝ) : ℝ :=
  regularizedInf rightShiftLinear (finiteTarget N) t (finiteLiftSpace N)

theorem finiteTarget_tendsto :
    Tendsto finiteTarget atTop (𝓝 (hardyCoordinates limitResidual)) := by
  exact hardyCoordinates.continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.sub projection_tendsto)

/-- Noor's already proved arithmetic density supplies every finite lift here. -/
theorem finiteLiftSpace_approximation (a : Space) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∃ v ∈ finiteLiftSpace N, ‖difference rightShiftLinear v - a‖ < ε := by
  exact finite_lift_approximation_of_dense rightShiftLinear
    (fun i => hardyCoordinates (residueAtom i)) shiftedResidue_density a ε hε

/-- Unconditional arithmetic bridge: along every vanishing parameter schedule,
the full unscaled finite minima tend to zero along all cutoffs. -/
theorem finiteMinimum_tendsto_zero (t : ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun N => finiteMinimum N (t N)) atTop (𝓝 0) := by
  exact regularizedInf_tendsto_zero rightShiftLinear finiteLiftSpace
    (walkSpan_mono (fun i => hardyCoordinates (residueAtom i)) id) (hardyCoordinates limitResidual)
    (finiteLiftSpace_approximation _) finiteTarget finiteTarget_tendsto t ht

/-- Finite arithmetic minimizing lifts at every cutoff form the requested
cofinal approximation family. There is no quantitative lift-norm bound. -/
theorem exists_finite_minimizing_lifts (t : ℕ → ℝ)
    (hpos : ∀ N, 0 < t N) (ht : Tendsto t atTop (𝓝 0)) :
    ∃ v : ℕ → Space, (∀ N, v N ∈ finiteLiftSpace N) ∧
      (∀ N, regularizedEnergy rightShiftLinear (finiteTarget N) (t N) (v N) =
        finiteMinimum N (t N)) ∧
      Tendsto (fun N => regularizedEnergy rightShiftLinear (finiteTarget N)
        (t N) (v N)) atTop (𝓝 0) := by
  classical
  choose v hv hE using fun N => exists_regularizedEnergy_minimizer
    rightShiftLinear (finiteTarget N) (t N) (hpos N) (finiteLiftSpace N)
  exact ⟨v, hv, hE, by simpa only [hE, finiteMinimum] using finiteMinimum_tendsto_zero t ht⟩

theorem finiteTarget_orthogonal (N : ℕ) (v : Space) (hv : v ∈ finiteLiftSpace N) :
    inner ℝ (finiteTarget N) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    change inner ℝ (hardyCoordinates (hilbertOne - projection N))
      (hardyCoordinates (residueAtom i.val)) = 0
    rw [hardyCoordinates.inner_map_map]
    rw [real_inner_comm]
    exact (Submodule.sub_starProjection_mem_orthogonal (K := finiteSpace N) hilbertOne)
      _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_right, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [inner_smul_right, ih, mul_zero]

theorem energy_le_scaled_finiteMinimum (N : ℕ) (t : ℝ) (ht : 0 < t) :
    energy N ≤ ((1+t)/t) * finiteMinimum N t := by
  obtain ⟨v, hv, hE⟩ := exists_regularizedEnergy_minimizer
    rightShiftLinear (finiteTarget N) t ht (finiteLiftSpace N)
  have hb := residual_sq_le_regularized_scaled rightShiftLinear rightShift_norm
    (finiteTarget N) v (finiteTarget_orthogonal N v hv) t ht
  rw [hE] at hb
  simpa only [finiteTarget, hardyCoordinates.norm_map, finiteMinimum,
    energy, walkError, projection, finiteSpace] using hb


/-- Exact finite-stage rate obstruction. Unscaled convergence cannot remove
the positive limiting residual energy from this divided-energy lower bound. -/
theorem energy_div_le_finiteMinimum_div (N : ℕ) (t : ℝ) (ht : 0 < t) :
    energy N / (1+t) ≤ finiteMinimum N t / t := by
  apply (div_le_iff₀ (show 0 < 1+t by linarith)).mpr
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    energy_le_scaled_finiteMinimum N t ht

/-- Conditional research reduction: the divided-energy convergence in hrate
is the open arithmetic provider. Cofinality and a positive vanishing parameter
schedule alone do not establish it. -/
theorem residual_zero_of_finiteMinimum_div_parameter_tendsto_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (t : ℕ → ℝ) (hpos : ∀ j, 0 < t j) (ht : Tendsto t atTop (𝓝 0))
    (hrate : Tendsto (fun j => finiteMinimum (N j) (t j) / t j)
      atTop (𝓝 0)) : limitResidual = 0 := by
  have hscaled : Tendsto (fun j => ((1+t j)/t j) * finiteMinimum (N j) (t j))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero, zero_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add ht).mul hrate
  have he : limitEnergy ≤ 0 := le_of_tendsto_of_tendsto
    (energy_tendsto.comp hN) hscaled
    (Filter.Eventually.of_forall (fun j =>
      energy_le_scaled_finiteMinimum (N j) (t j) (hpos j)))
  apply limitResidual_zero_iff_energy_zero.mpr
  exact le_antisymm he (sq_nonneg _)

/-- Conditional RH implication. The only unresolved arithmetic hypothesis
is hrate; this theorem does not supply it. -/
theorem riemannHypothesis_of_finiteMinimum_div_parameter_tendsto_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (t : ℕ → ℝ) (hpos : ∀ j, 0 < t j) (ht : Tendsto t atTop (𝓝 0))
    (hrate : Tendsto (fun j => finiteMinimum (N j) (t j) / t j)
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (residual_zero_of_finiteMinimum_div_parameter_tendsto_zero N hN t hpos ht hrate))

end RiemannResearch.RH.Pareto.Noor

import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# Nonconvergence of the limiting Möbius-defect reconstruction under failure of RH

Source: user-provided coefficient-stabilization handoff and independent
continuation, 2026-09-19. The proof uses joint separation by the continuous
Möbius coordinates, not density of the residue atoms. No novelty is claimed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Ordinary ordered partial reconstruction, with moduli 2 through N+1. -/
def coordinatePartialSum (f : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  ∑ i : Fin N, coefficientCLM (i.val + 2) f • residueAtom i.val

/-- Even ordinary ordered norm convergence identifies the original vector;
unconditional summability of the series is not needed. -/
theorem eq_of_coordinatePartialSum_tendsto (f g : ThresholdHilbert)
    (ht : Tendsto (coordinatePartialSum f) atTop (𝓝 g)) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
  have he : ∀ᶠ N : ℕ in atTop,
      coefficientCLM (j + 2) (coordinatePartialSum f N) = coefficientCLM (j + 2) f := by
    filter_upwards [eventually_ge_atTop (j + 1)] with N hN
    exact coefficient_finite_sum N (fun i : Fin N => coefficientCLM (i.val + 2) f)
      ⟨j, by omega⟩
  have hc := (coefficientCLM (j + 2)).continuous.tendsto g |>.comp ht
  have ht' : Tendsto (fun N => coefficientCLM (j + 2) (coordinatePartialSum f N))
      atTop (𝓝 (coefficientCLM (j + 2) f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with N hN
    exact hN.symm
  have heq := tendsto_nhds_unique hc ht'
  have hz : coefficientCLM (j + 2) (f - g) = 0 := by
    rw [map_sub, heq, sub_self]
  change -(mobiusDifferenceCLM (j + 2) (f - g)) = 0 at hz
  exact neg_eq_zero.mp hz

theorem coordinatePartialSum_mem (f : ThresholdHilbert) (N : ℕ) :
    coordinatePartialSum f N ∈ closedSpace := by
  apply Submodule.sum_mem
  intro i _
  exact closedSpace.smul_mem _ ((Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (Submodule.subset_span ⟨i.val, rfl⟩))

/-- No ordered norm-convergent reconstruction of the actual non-RH residual
exists. This is stronger than merely excluding unconditional summability. -/
theorem not_RH_defect_partialSums_no_limit (hRH : ¬ RiemannHypothesis) :
    ¬ ∃ g : ThresholdHilbert,
      Tendsto (coordinatePartialSum limitResidual) atTop (𝓝 g) := by
  rintro ⟨g, hg⟩
  have hfg := eq_of_coordinatePartialSum_tendsto limitResidual g hg
  have hm : limitResidual ∈ closedSpace := by
    rw [hfg]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hg
      (Filter.Eventually.of_forall (coordinatePartialSum_mem limitResidual))
  have ho := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hm
  have hr : limitResidual = 0 := by
    rw [real_inner_self_eq_norm_sq] at ho
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ho)
  exact hRH (riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr hr))

/-- Whenever its biorthogonal reconstruction series converges, it reconstructs
the original vector. This does not assert convergence for arbitrary vectors. -/
theorem eq_tsum_of_summable_coordinate_series (f : ThresholdHilbert)
    (hs : Summable (fun i : ℕ => coefficientCLM (i + 2) f • residueAtom i)) :
    f = ∑' i : ℕ, coefficientCLM (i + 2) f • residueAtom i := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have hc : coefficientCLM m (∑' i : ℕ, coefficientCLM (i + 2) f • residueAtom i) =
      coefficientCLM m f := by
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
    rw [(coefficientCLM (j + 2)).map_tsum hs]
    simp [map_smul, coefficientCLM_biorthogonal]
  have hz : coefficientCLM m
      (f - ∑' i : ℕ, coefficientCLM (i + 2) f • residueAtom i) = 0 := by
    rw [map_sub, hc, sub_self]
  change -(mobiusDifferenceCLM m
      (f - ∑' i : ℕ, coefficientCLM (i + 2) f • residueAtom i)) = 0 at hz
  exact neg_eq_zero.mp hz

theorem mem_closedSpace_of_summable_coordinate_series (f : ThresholdHilbert)
    (hs : Summable (fun i : ℕ => coefficientCLM (i + 2) f • residueAtom i)) :
    f ∈ closedSpace := by
  rw [eq_tsum_of_summable_coordinate_series f hs]
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  exact closedSpace.smul_mem _ ((Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (Submodule.subset_span ⟨i, rfl⟩))

/-- Even Hilbert convergence of the full stabilized defect series would force
RH. All signs are retained in the vector series. -/
theorem not_RH_defect_series_not_summable (hRH : ¬ RiemannHypothesis) :
    ¬ Summable (fun i : ℕ => coefficientCLM (i + 2) limitResidual • residueAtom i) := by
  intro hs
  have hm := mem_closedSpace_of_summable_coordinate_series limitResidual hs
  have ho := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hm
  have hr : limitResidual = 0 := by
    rw [real_inner_self_eq_norm_sq] at ho
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ho)
  exact hRH (riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr hr))

/-- The exact norm-weighted absolute defect sum must diverge. -/
theorem not_RH_defect_norms_not_summable (hRH : ¬ RiemannHypothesis) :
    ¬ Summable (fun i : ℕ =>
      ‖coefficientCLM (i + 2) limitResidual • residueAtom i‖) := by
  intro hs
  exact not_RH_defect_series_not_summable hRH hs.of_norm

/-- There are arbitrarily high indices with wrong stabilized coefficients;
finitely many exceptional coefficients could always be reconstructed. -/
theorem not_RH_cofinally_wrong_coefficients (hRH : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ 1 < m ∧
      limitCoefficient m ≠ -(ArithmeticFunction.moebius m : ℝ) := by
  by_contra! hn
  apply not_RH_defect_series_not_summable hRH
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro i hi
  have hNi : N < i + 2 := by
    simp only [Finset.mem_range] at hi
    omega
  have hc := hn (i + 2) hNi (by omega)
  rw [limitCoefficient_eq_residual (i + 2) (by omega)] at hc
  have hz : mobiusDifferenceCLM (i + 2) limitResidual = 0 := by linarith
  simp [coefficientCLM, hz]

end RiemannResearch.RH.Pareto.CoefficientStabilization

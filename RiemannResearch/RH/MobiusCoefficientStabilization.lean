import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Stabilization and exact characterization of residue coefficients

Source: the coefficient-stabilization argument developed with the user,
RH_Coefficient_Stabilization_Theorem_2026-09-18.md, for the statements and
proof strategy. This module concerns full Hilbert-norm orthogonal projections,
not a truncated or numerically rounded Gram problem.

Stage n uses g_2,...,g_(n+1), so it corresponds to N=n+1 in the written note.
The coefficients always stabilize. Their simultaneous equality to -mu(m)
is equivalent to a zero residual, and implies Mathlib's RiemannHypothesis
through the already proved Mellin bridge. That equality remains an explicit
open hypothesis in the conditional RH theorems.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

/-- The original legal atom g_(i+2); indexing starts at zero. -/
def residueAtom (i : ℕ) : ThresholdHilbert :=
  normalizedResidueHilbert (i + 2) (by omega)

/-- The continuous coefficient functional, with the sign required by g_d. -/
def coefficientCLM (m : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  -mobiusDifferenceCLM m

theorem coefficientCLM_biorthogonal (i j : ℕ) :
    coefficientCLM (i + 2) (residueAtom j) = if i = j then 1 else 0 := by
  unfold coefficientCLM residueAtom
  rw [neg_apply, mobius_normalizedResidue _ _ (by omega)]
  by_cases h : i = j <;> simp [h]

theorem residueAtom_linearIndependent : LinearIndependent ℝ residueAtom :=
  RiemannResearch.Analysis.continuous_biorthogonal_linearIndependent
    residueAtom (fun i => coefficientCLM (i + 2)) coefficientCLM_biorthogonal

theorem coefficient_finite_sum (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    coefficientCLM (i.val + 2) (∑ j : Fin n, a j • residueAtom j.val) = a i := by
  have hpair (j : Fin n) : coefficientCLM (i.val + 2) (residueAtom j.val) =
      if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using coefficientCLM_biorthogonal i.val j.val
  simp [map_sum, map_smul, hpair]

/-- At stage n the span contains g_2 through g_(n+1). -/
abbrev finiteSpace (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  walkSpan residueAtom id n

abbrev closedSpace : Submodule ℝ ThresholdHilbert := dictionaryClosure residueAtom

def projection (n : ℕ) : ThresholdHilbert :=
  (finiteSpace n).starProjection hilbertOne

def limitProjection : ThresholdHilbert := closedSpace.starProjection hilbertOne
def limitResidual : ThresholdHilbert := hilbertOne - limitProjection
def coefficient (n m : ℕ) : ℝ := coefficientCLM m (projection n)
def limitCoefficient (m : ℕ) : ℝ := coefficientCLM m limitProjection
def energy (n : ℕ) : ℝ := walkError residueAtom id hilbertOne n
def limitEnergy : ℝ := limitingError residueAtom hilbertOne

theorem finiteSpace_expansion (n : ℕ) (x : ThresholdHilbert) (hx : x ∈ finiteSpace n) :
    ∃ a : Fin n → ℝ, x = ∑ j : Fin n, a j • residueAtom j.val := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    simp
  | zero => exact ⟨fun _ => 0, by simp⟩
  | add x y hx hy hix hiy =>
    obtain ⟨a, rfl⟩ := hix
    obtain ⟨b, rfl⟩ := hiy
    exact ⟨fun j => a j + b j, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul c x hx hi =>
    obtain ⟨a, rfl⟩ := hi
    exact ⟨fun j => c * a j, by simp [mul_smul, Finset.smul_sum]⟩

/-- These are the actual coefficients of the full-norm orthogonal projection. -/
theorem projection_expansion (n : ℕ) :
    projection n = ∑ j : Fin n, coefficient n (j.val + 2) • residueAtom j.val := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n (projection n)
    ((finiteSpace n).starProjection_apply_mem hilbertOne)
  have hc (i : Fin n) : coefficient n (i.val + 2) = a i := by
    unfold coefficient
    rw [ha]
    exact coefficient_finite_sum n a i
  simpa only [hc] using ha

theorem projection_coefficients_unique (n : ℕ) (a : Fin n → ℝ)
    (ha : projection n = ∑ j : Fin n, a j • residueAtom j.val) (i : Fin n) :
    coefficient n (i.val + 2) = a i := by
  unfold coefficient
  rw [ha]
  exact coefficient_finite_sum n a i

theorem projection_tendsto : Tendsto projection atTop (𝓝 limitProjection) :=
  walkProjection_tendsto residueAtom id Function.surjective_id hilbertOne

theorem coefficient_tendsto (m : ℕ) :
    Tendsto (fun n => coefficient n m) atTop (𝓝 (limitCoefficient m)) :=
  walkProjection_map_tendsto residueAtom id Function.surjective_id
    hilbertOne (coefficientCLM m)

theorem energy_tendsto : Tendsto energy atTop (𝓝 limitEnergy) :=
  walkError_tendsto residueAtom id Function.surjective_id hilbertOne

theorem energy_antitone : Antitone energy :=
  walkError_antitone residueAtom id hilbertOne

/-- Exact energy identity; it does not assume that limitEnergy vanishes. -/
theorem energy_eq_limit_add (n : ℕ) :
    energy n = limitEnergy + ‖limitProjection - projection n‖ ^ 2 :=
  walkError_eq_limitingError_add residueAtom id hilbertOne n

theorem limitResidual_mem_orthogonal : limitResidual ∈ closedSpaceᗮ :=
  Submodule.sub_starProjection_mem_orthogonal hilbertOne

theorem limitCoefficient_eq_residual (m : ℕ) (hm : 0 < m) :
    limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) +
      mobiusDifferenceCLM m limitResidual := by
  simp only [limitCoefficient, coefficientCLM, neg_apply,
    limitResidual, map_sub, mobius_coordinate_one m hm]
  ring

/-- The correction is a finite divisor sum, with no infinite expansion used. -/
theorem limitCoefficient_eq_divisor_sum (m : ℕ) (hm : 0 < m) :
    limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) +
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) *
        (hilbertSequence limitResidual d - hilbertSequence limitResidual (d - 1)) := by
  simpa only [mobiusDifferenceCLM_apply, mobiusDifference] using
    limitCoefficient_eq_residual m hm

theorem coefficient_error_bound (n m : ℕ) :
    ‖limitCoefficient m - coefficient n m‖ ^ 2 ≤
      ‖mobiusDifferenceCLM m‖ ^ 2 * (energy n - limitEnergy) := by
  simpa only [limitCoefficient, coefficient, projection, limitProjection,
    finiteSpace, closedSpace, energy, limitEnergy, coefficientCLM, norm_neg] using
    walkProjection_map_error_bound residueAtom id hilbertOne n (coefficientCLM m)

theorem limitCoefficient_defect_bound (m : ℕ) (hm : 0 < m) :
    ‖limitCoefficient m + (ArithmeticFunction.moebius m : ℝ)‖ ^ 2 ≤
      ‖mobiusDifferenceCLM m‖ ^ 2 * limitEnergy := by
  have hb := limitingProjection_map_target_bound residueAtom hilbertOne
    (mobiusDifferenceCLM m)
  rw [mobius_coordinate_one m hm] at hb
  simpa only [limitCoefficient, coefficientCLM, neg_apply,
    limitProjection, sub_eq_add_neg, add_comm, limitEnergy] using hb

theorem coefficient_error_bound_explicit (n m : ℕ) (hm : 0 < m) :
    ‖limitCoefficient m - coefficient n m‖ ^ 2 ≤
      (∑ j ∈ Finset.Icc 1 m,
        (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff m j : ℝ) ^ 2) *
        (energy n - limitEnergy) := by
  simpa only [mobiusDifferenceCLM_norm_sq m hm] using coefficient_error_bound n m

theorem limitCoefficient_defect_bound_explicit (m : ℕ) (hm : 0 < m) :
    ‖limitCoefficient m + (ArithmeticFunction.moebius m : ℝ)‖ ^ 2 ≤
      (∑ j ∈ Finset.Icc 1 m,
        (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff m j : ℝ) ^ 2) * limitEnergy := by
  simpa only [mobiusDifferenceCLM_norm_sq m hm] using limitCoefficient_defect_bound m hm

theorem limitCoefficients_eq_mobius_iff_residual_zero :
    (∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ)) ↔
      limitResidual = 0 := by
  constructor
  · intro h
    apply eq_zero_of_mobius_coordinates_zero
    intro m hm
    have hc := h m hm
    rw [limitCoefficient_eq_residual m (by omega)] at hc
    linarith
  · intro hr m hm
    rw [limitCoefficient_eq_residual m (by omega), hr, map_zero, add_zero]

theorem limitResidual_zero_iff_energy_zero : limitResidual = 0 ↔ limitEnergy = 0 := by
  change limitResidual = 0 ↔ ‖limitResidual‖ ^ 2 = 0
  rw [sq_eq_zero_iff, norm_eq_zero]

theorem limitEnergy_zero_iff_mem : limitEnergy = 0 ↔ hilbertOne ∈ closedSpace :=
  limitingError_eq_zero_iff residueAtom hilbertOne

theorem limitCoefficients_eq_mobius_iff_mem :
    (∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ)) ↔
      hilbertOne ∈ closedSpace :=
  limitCoefficients_eq_mobius_iff_residual_zero.trans
    (limitResidual_zero_iff_energy_zero.trans limitEnergy_zero_iff_mem)

theorem limitCoefficients_eq_mobius_iff_energy_tendsto_zero :
    (∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ)) ↔
      Tendsto energy atTop (𝓝 0) := by
  rw [limitCoefficients_eq_mobius_iff_mem]
  exact (walkError_tendsto_zero_iff residueAtom id Function.surjective_id hilbertOne).symm

theorem coefficients_tendsto_mobius_iff :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => coefficient n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      ∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) := by
  constructor
  · intro h m hm
    exact tendsto_nhds_unique (coefficient_tendsto m) (h m hm)
  · intro h m hm
    simpa only [h m hm] using coefficient_tendsto m

theorem residueAtom_mem_legal (i : ℕ) :
    residueAtom i ∈ hilbertLegalSubspace {n : ℕ | 0 < n} := by
  change hilbertSequence (residueAtom i) ∈ legalSeedSpan {n : ℕ | 0 < n}
  rw [residueAtom, normalizedResidueHilbert_sequence]
  have he : residueFraction (i + 2) = (1 / ((i + 2 : ℕ) : ℝ)) • residue (i + 2) := by
    funext n
    simp [residueFraction, residue, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (legalSeedSpan {n : ℕ | 0 < n}).smul_mem _
    (residue_mem_legalSeedSpan _ (by change 0 < i + 2; omega))

theorem closedSpace_le_legalClosure : closedSpace ≤ hilbertLegalClosure {n : ℕ | 0 < n} := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact residueAtom_mem_legal i

/-- Conditional RH implication. The simultaneous Möbius limits remain an open hypothesis. -/
theorem riemannHypothesis_of_limitCoefficients
    (h : ∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure (limitCoefficients_eq_mobius_iff_mem.mp h)

theorem riemannHypothesis_of_coefficients_tendsto_mobius
    (h : ∀ m : ℕ, 1 < m → Tendsto (fun n => coefficient n m) atTop
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients (coefficients_tendsto_mobius_iff.mp h)

/-- A second conditional route: approximate the actual finite-support Riesz vectors.
Their membership is an open hypothesis; continuity alone does not supply it. -/
theorem residual_zero_of_mobiusRiesz_mem
    (h : ∀ m : ℕ, 1 < m → mobiusRieszHilbert m ∈ closedSpace) :
    limitResidual = 0 := by
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  rw [← mobiusRieszHilbert_inner]
  exact (closedSpace.mem_orthogonal limitResidual).mp limitResidual_mem_orthogonal
    (mobiusRieszHilbert m) (h m hm)

theorem riemannHypothesis_of_mobiusRiesz_mem
    (h : ∀ m : ℕ, 1 < m → mobiusRieszHilbert m ∈ closedSpace) :
    RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (residual_zero_of_mobiusRiesz_mem h))

/-- Failure of RH forces at least one stabilized coefficient to miss its Möbius target. -/
theorem exists_coefficient_defect_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ m : ℕ, 1 < m ∧ limitCoefficient m ≠ -(ArithmeticFunction.moebius m : ℝ) := by
  by_contra hn
  push Not at hn
  exact h (riemannHypothesis_of_limitCoefficients hn)

end RiemannResearch.RH.Pareto.CoefficientStabilization

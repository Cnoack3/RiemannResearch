import RiemannResearch.RH.ProjectedDualStretchedTail
import RiemannResearch.Analysis.FiniteCoefficientConcentration

/-!
# Projected inverse-column concentration and stretched residual criteria

Source: user-requested continuation of commit 396b7c015e48d46aca4648d4587799ebffe4ec63,
28 September 2026. These finite Cauchy--Schwarz estimates and filter arguments
assemble existing repository identities. No external analytic theorem is imported.

Established: signed inverse-column identification, l2/trace bounds, exact-support
and approximate-support estimates, and a necessary mass-growth obstruction.
CONDITIONAL RESEARCH REDUCTIONS: the cofinal concentration budgets below force
zero limiting residual. Their arithmetic providers remain Open. Neither an
unconditional sub-stretched coefficient-mass bound nor RH is proved here.
Stage n contains conductors 2,...,n+1.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis GramMobiusCorrection

/-- The signed coefficient column of the projected Riesz vector; this definition also covers stages before d is included. -/
def projectedDualColumn (n d : ℕ) (i : Fin n) : ℝ :=
  coefficientCLM (i.val + 2) ((finiteSpace n).starProjection (coefficientRiesz d))
/-- The squared Euclidean norm of the actual coefficient column, not its Pareto Hilbert energy. -/
def projectedDualColumnEnergy (n d : ℕ) : ℝ := ∑ i : Fin n, projectedDualColumn n d i ^ 2
/-- Two complete squared-coefficient energies, each multiplied by its own support size. -/
def projectedDualSplitEnergy (n d : ℕ) (s : Finset (Fin n)) : ℝ :=
  (s.card : ℝ) * (∑ i ∈ s, projectedDualColumn n d i ^ 2) +
    (sᶜ.card : ℝ) * (∑ i ∈ sᶜ, projectedDualColumn n d i ^ 2)

/-- Ordinary Cauchy--Schwarz retains the full dimension factor n. -/
theorem projectedDualCoefficientMass_sq_le_card_energy (n d : ℕ) :
    projectedDualCoefficientMass n d ^ 2 ≤ (n : ℝ) * projectedDualColumnEnergy n d := by
  simpa [projectedDualCoefficientMass, projectedDualColumnEnergy, projectedDualColumn]
    using finite_sum_abs_sq_le_card_energy Finset.univ (projectedDualColumn n d)

/-- Approximate sparsity bound. The entire complement is retained. -/
theorem projectedDualCoefficientMass_sq_le_split_energy (n d : ℕ) (s : Finset (Fin n)) :
    projectedDualCoefficientMass n d ^ 2 ≤ 2 * projectedDualSplitEnergy n d s := by
  exact finite_sum_abs_sq_le_split_energy s (projectedDualColumn n d)

/-- Hilbert Cauchy--Schwarz controls one coefficient by the corresponding inverse diagonal. -/
theorem projectedDualColumn_sq_le_diagonal (n d : ℕ) (i : Fin n) :
    projectedDualColumn n d i ^ 2 ≤
      ‖(finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 *
        residueInverseEntry n i i := by
  let p := (finiteSpace n).starProjection (coefficientRiesz d)
  have he : projectedDualColumn n d i =
      inner ℝ p ((finiteSpace n).starProjection (coefficientDual i.val)) := by
    calc
      _ = inner ℝ p (coefficientDual i.val) := (coefficientDual_inner p i.val).symm
      _ = _ := by
        symm
        rw [← (finiteSpace n).inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr ((finiteSpace n).starProjection_apply_mem _)]
  rw [he, residueInverseEntry_projection, real_inner_self_eq_norm_sq]
  simpa only [pow_two, real_inner_self_eq_norm_sq] using
    real_inner_mul_inner_self_le p ((finiteSpace n).starProjection (coefficientDual i.val))

/-- The available full-energy control pays the complete growing inverse trace. -/
theorem projectedDualColumnEnergy_le_diagonal_trace (n d : ℕ) :
    projectedDualColumnEnergy n d ≤
      ‖(finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 *
        ∑ i : Fin n, residueInverseEntry n i i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => projectedDualColumn_sq_le_diagonal n d i)

/-- An unconditional finite bound in terms of the explicitly known finite-support dual norms. -/
theorem projectedDualColumnEnergy_le_dual_trace (n d : ℕ) :
    projectedDualColumnEnergy n d ≤
      ‖coefficientRiesz d‖ ^ 2 * ∑ i : Fin n, ‖coefficientDual i.val‖ ^ 2 := by
  apply (projectedDualColumnEnergy_le_diagonal_trace n d).trans
  apply mul_le_mul
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((finiteSpace n).norm_starProjection_apply_le _)
  · exact Finset.sum_le_sum (fun i _ => residueInverseEntry_diagonal_le_dual n i)
  · apply Finset.sum_nonneg
    intro i hi
    rw [residueInverseEntry_projection, real_inner_self_eq_norm_sq]
    positivity
  · positivity



/-- For a present conductor, each signed coefficient is exactly its inverse-Gram entry. -/
theorem projectedDualColumn_eq_inverse_entry (n : ℕ) (i k : Fin n) :
    projectedDualColumn n (i.val + 2) k = residueInverseEntry n k i := by
  rw [residueInverseEntry_projection]
  rw [(finiteSpace n).inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr ((finiteSpace n).starProjection_apply_mem _)]
  rw [real_inner_comm, coefficientDual_inner]
  rfl

/-- The column energy is the complete squared l2 norm of the inverse-Gram column. -/
theorem projectedDualColumnEnergy_eq_inverse_column_sq (n : ℕ) (i : Fin n) :
    projectedDualColumnEnergy n (i.val + 2) =
      ∑ k : Fin n, residueInverseEntry n k i ^ 2 := by
  simp only [projectedDualColumnEnergy, projectedDualColumn_eq_inverse_entry]

/-- A flexible weighted l2 estimate; positivity of every chosen weight is explicit. -/
theorem projectedDualCoefficientMass_sq_le_weighted_energy (n d : ℕ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    projectedDualCoefficientMass n d ^ 2 ≤
      (∑ i, w i) * ∑ i, projectedDualColumn n d i ^ 2 / w i :=
  finite_sum_abs_sq_le_weighted_energy Finset.univ _ w (fun i _ => hw i)

/-- Exact sparsity removes the complement and the factor two. Sparsity is a hypothesis. -/
theorem projectedDualCoefficientMass_sq_le_support_energy (n d : ℕ)
    (s : Finset (Fin n)) (hzero : ∀ i, i ∉ s → projectedDualColumn n d i = 0) :
    projectedDualCoefficientMass n d ^ 2 ≤
      (s.card : ℝ) * projectedDualColumnEnergy n d := by
  have hsum : (∑ i : Fin n, |projectedDualColumn n d i|) =
      ∑ i ∈ s, |projectedDualColumn n d i| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i hi hnot
    simp [hzero i hnot]
  change (∑ i : Fin n, |projectedDualColumn n d i|) ^ 2 ≤ _
  rw [hsum]
  apply (finite_sum_abs_sq_le_card_energy s _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => sq_nonneg _)

/-- A relative l2 leakage bound produces the effective-support cost card(s)+card(s-complement)*rho. -/
theorem projectedDualSplitEnergy_le_effective_support (n d : ℕ)
    (s : Finset (Fin n)) (ρ : ℝ)
    (hleak : (∑ i ∈ sᶜ, projectedDualColumn n d i ^ 2) ≤
      ρ * projectedDualColumnEnergy n d) :
    projectedDualSplitEnergy n d s ≤
      ((s.card : ℝ) + (sᶜ.card : ℝ) * ρ) * projectedDualColumnEnergy n d := by
  have hhead : (∑ i ∈ s, projectedDualColumn n d i ^ 2) ≤
      projectedDualColumnEnergy n d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hhead (Nat.cast_nonneg s.card : (0:ℝ) ≤ _)
  have h2 := mul_le_mul_of_nonneg_left hleak (Nat.cast_nonneg sᶜ.card : (0:ℝ) ≤ _)
  unfold projectedDualSplitEnergy
  nlinarith [h1, h2]

/-- The split coefficient energy controls the complete moving physical tail. -/
theorem projectedDualTailEnergy_le_split_energy (n d : ℕ) (s : Finset (Fin n)) :
    projectedDualTailEnergy n d ≤
      2 * projectedDualSplitEnergy n d s / ((n : ℝ) + 1) :=
  (projectedDualTailEnergy_le_coefficient_mass n d).trans
    (div_le_div_of_nonneg_right (projectedDualCoefficientMass_sq_le_split_energy n d s)
      (by positivity))

/-- A nonzero limiting correction forces divergence of the weighted squared coefficient mass. This is a conditional lower obstruction. -/
theorem coefficient_mass_stretched_barrier_of_nonzero_correction
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a) (d : ℕ) (hd : 1 < d)
    (hne : mobiusDifferenceCLM d limitResidual ≠ 0) :
    Tendsto (fun n : ℕ => Real.exp (-b * logProductPower (1 / 11)
      (6 + Real.log (n : ℝ))) * projectedDualCoefficientMass n d ^ 2) atTop atTop :=
  tendsto_atTop_mono (stretched_projectedDualTailEnergy_le_coefficient_mass b · d)
    (projectedDualTail_stretched_barrier_of_nonzero_correction hC henergy b hba d hd hne)

/-- CONDITIONAL RESEARCH REDUCTION: cofinal smallness at the arithmetic exponent itself suffices. The mass provider is Open. -/
theorem limitResidual_eq_zero_of_cofinally_small_coefficient_mass
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (hmass : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
        projectedDualCoefficientMass n d ^ 2 < ε) :
    limitResidual = 0 := by
  have hz (d : ℕ) (hd : 1 < d) : mobiusDifferenceCLM d limitResidual = 0 := by
    apply correction_limit_eq_zero_of_cofinally_small_stretched_dual_tail hC henergy d hd
    intro ε hε
    exact (hmass d hd ε hε).mono (fun n hn =>
      (stretched_projectedDualTailEnergy_le_coefficient_mass a n d).trans_lt hn)
  apply limitResidual_zero_iff_energy_zero.mpr
  apply limitEnergy_zero_iff_mem.mpr
  apply projection_norm_tendsto_zero_iff_mem.mp
  apply correction_limits_iff_norm.mp
  intro d hd
  simpa only [hz d hd] using correction_tendsto_residual d (by omega)

/-- CONDITIONAL RESEARCH REDUCTION: a cofinal split-energy budget implies the existing coefficient-mass criterion. The budget provider is Open. -/
theorem limitResidual_eq_zero_of_cofinal_stretched_split_energy
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a)
    (hbound : ∀ d : ℕ, 1 < d → ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∃ s : Finset (Fin n), Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualSplitEnergy n d s ≤ K) :
    limitResidual = 0 := by
  apply limitResidual_eq_zero_of_cofinal_stretched_coefficient_mass hC henergy b hba
  intro d hd
  obtain ⟨K, hK⟩ := hbound d hd
  refine ⟨2 * K, hK.mono ?_⟩
  rintro n ⟨s, hs⟩
  have he := mul_le_mul_of_nonneg_left
    (projectedDualCoefficientMass_sq_le_split_energy n d s)
    (Real.exp_pos (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))).le
  nlinarith

/-- CONDITIONAL RESEARCH REDUCTION: l2 column energy times effective support must meet one joint cofinal budget. Both bounds are required at the same indices; the provider is Open. -/
theorem limitResidual_eq_zero_of_cofinal_stretched_l2_concentration
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (b : ℝ) (hba : b < a)
    (hbound : ∀ d : ℕ, 1 < d → ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
      ∃ (s : Finset (Fin n)) (ρ : ℝ), 0 ≤ ρ ∧
        (∑ i ∈ sᶜ, projectedDualColumn n d i ^ 2) ≤
          ρ * projectedDualColumnEnergy n d ∧
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
          (((s.card : ℝ) + (sᶜ.card : ℝ) * ρ) * projectedDualColumnEnergy n d) ≤ K) :
    limitResidual = 0 := by
  apply limitResidual_eq_zero_of_cofinal_stretched_split_energy hC henergy b hba
  intro d hd
  obtain ⟨K, hK⟩ := hbound d hd
  refine ⟨K, hK.mono ?_⟩
  rintro n ⟨s, ρ, hρ, hleak, hbudget⟩
  exact ⟨s, (mul_le_mul_of_nonneg_left
    (projectedDualSplitEnergy_le_effective_support n d s ρ hleak)
    (Real.exp_pos _).le).trans hbudget⟩


/-- CONDITIONAL RESEARCH REDUCTION: endpoint liminf-zero split energy suffices, without a strict exponent margin. The provider is Open. -/
theorem limitResidual_eq_zero_of_cofinally_small_split_energy
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ n : ℕ in atTop, ‖tailError n‖ ^ 2 ≤ 8 + C * (n : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
    (hbound : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      ∃ s : Finset (Fin n), Real.exp (-a * logProductPower (1 / 11)
        (6 + Real.log (n : ℝ))) * projectedDualSplitEnergy n d s < ε) :
    limitResidual = 0 := by
  apply limitResidual_eq_zero_of_cofinally_small_coefficient_mass hC henergy
  intro d hd ε hε
  apply (hbound d hd (ε / 2) (by positivity)).mono
  rintro n ⟨s, hs⟩
  have he := mul_le_mul_of_nonneg_left
    (projectedDualCoefficientMass_sq_le_split_energy n d s)
    (Real.exp_pos (-a * logProductPower (1 / 11) (6 + Real.log (n : ℝ)))).le
  nlinarith

/-- The checked arithmetic energy supplies a>0 unconditionally. The l2 concentration provider remains Open and explicitly implies zero residual and RH. -/
theorem exists_stretched_l2_concentration_rh_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, b < a →
      (∀ d : ℕ, 1 < d → ∃ K : ℝ, ∃ᶠ n : ℕ in atTop,
        ∃ (s : Finset (Fin n)) (ρ : ℝ), 0 ≤ ρ ∧
          (∑ i ∈ sᶜ, projectedDualColumn n d i ^ 2) ≤
            ρ * projectedDualColumnEnergy n d ∧
          Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (n : ℝ))) *
            (((s.card : ℝ) + (sᶜ.card : ℝ) * ρ) *
              projectedDualColumnEnergy n d) ≤ K) →
      limitResidual = 0 ∧ RiemannHypothesis := by
  obtain ⟨a, ha, C, hC, he⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, ?_⟩
  intro b hb hbound
  have hz := limitResidual_eq_zero_of_cofinal_stretched_l2_concentration hC he b hb hbound
  refine ⟨hz, ?_⟩
  apply riemannHypothesis_of_residual_mem_modeClosure
  rw [hz]
  exact Submodule.zero_mem _

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

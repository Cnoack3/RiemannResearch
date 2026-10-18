import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# A first-coordinate test for the actual limiting residue residual

Source: continuation developed with Christian Noack from the coefficient-
stabilization and multi-range handoffs, 2026-09-19. The proof uses exact integer
dilation, closed-span invariance, and Cauchy--Schwarz. This is an independently
derived argument, with no claim of mathematical novelty. The assertion that the
first residual coordinate vanishes remains an explicit open RH hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

theorem normalizedResidue_mem_atomSpan (d : ℕ) (hd : 0 < d) :
    normalizedResidueHilbert d hd ∈ Submodule.span ℝ (Set.range residueAtom) := by
  by_cases hd1 : d = 1
  · subst d
    have hz : normalizedResidueHilbert 1 hd = 0 := by
      apply hilbertSequence_injective
      rw [normalizedResidueHilbert_sequence]
      funext k
      cases k <;> simp [residueFraction, hilbertSequence, Nat.mod_one]
    rw [hz]
    exact Submodule.zero_mem _
  · have he : d - 2 + 2 = d := by omega
    apply Submodule.subset_span
    exact ⟨d - 2, by simp only [residueAtom, he]⟩

theorem hilbertDilation_residueAtom (m : ℕ) (hm : 0 < m) (i : ℕ) :
    hilbertDilation m hm (residueAtom i) =
      (m : ℝ) • normalizedResidueHilbert (m * (i + 2)) (by positivity) -
        ((m : ℝ) / (i + 2 : ℕ)) • normalizedResidueHilbert m hm := by
  apply hilbertSequence_injective
  change hilbertSequence (hilbertDilation m hm (residueAtom i)) =
    hilbertSequenceLinear (_ - _)
  rw [map_sub, map_smul, map_smul, hilbertDilation_sequence]
  change dilation m (hilbertSequence (residueAtom i)) =
    (m : ℝ) • hilbertSequence (normalizedResidueHilbert (m * (i + 2)) _) -
      ((m : ℝ) / (i + 2 : ℕ)) • hilbertSequence (normalizedResidueHilbert m hm)
  rw [residueAtom, normalizedResidueHilbert_sequence,
    normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]
  funext k
  simp only [dilation, residueFraction, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Nat.mod_mul, Nat.cast_add, Nat.cast_mul]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hi0 : ((i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hi0 ⊢
  field_simp
  ring

theorem closedSpace_dilation {f : ThresholdHilbert} (hf : f ∈ closedSpace)
    (m : ℕ) (hm : 0 < m) : hilbertDilation m hm f ∈ closedSpace := by
  let S := Submodule.span ℝ (Set.range residueAtom)
  have hmap : Set.MapsTo (hilbertDilationContinuous m hm)
      (S : Set ThresholdHilbert) (S : Set ThresholdHilbert) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      change hilbertDilation m hm (residueAtom i) ∈ S
      rw [hilbertDilation_residueAtom]
      exact S.sub_mem
        (S.smul_mem _ (normalizedResidue_mem_atomSpan _ (by positivity)))
        (S.smul_mem _ (normalizedResidue_mem_atomSpan _ hm))
    | zero =>
      change (hilbertDilationContinuous m hm) 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    | add x y hx hy ihx ihy =>
      change (hilbertDilationContinuous m hm) (x + y) ∈ S
      rw [map_add]
      exact S.add_mem ihx ihy
    | smul c x hx ih =>
      change (hilbertDilationContinuous m hm) (c • x) ∈ S
      rw [map_smul]
      exact S.smul_mem c ih
  exact hmap.closure (hilbertDilationContinuous m hm).continuous hf

theorem firstPoint_eq_dilation_difference :
    paretoPointHilbert 0 = hilbertOne - (1 / 2 : ℝ) • hilbertDilation 2 (by omega) hilbertOne := by
  apply hilbertSequence_injective
  change hilbertSequence (paretoPointHilbert 0) = hilbertSequenceLinear (_ - _)
  rw [map_sub, map_smul]
  change hilbertSequence (paretoPointHilbert 0) = hilbertSequence hilbertOne -
    (1 / 2 : ℝ) • hilbertSequence (hilbertDilation 2 _ hilbertOne)
  rw [hilbertSequence_paretoPoint, hilbertDilation_sequence, hilbertOne_sequence]
  funext k
  by_cases hk0 : k = 0
  · subst k; norm_num [paretoPointSequence, dilation, zeroAnchor]
  by_cases hk1 : k = 1
  · subst k; norm_num [paretoPointSequence, dilation, zeroAnchor]
  have hkdiv : k / 2 ≠ 0 := by omega
  simp [paretoPointSequence, dilation, zeroAnchor, hk0, hk1, hkdiv]

theorem limitResidual_inner_one : inner ℝ limitResidual hilbertOne = limitEnergy := by
  have ho : inner ℝ limitResidual limitProjection = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (closedSpace.starProjection_apply_mem hilbertOne)
  have he : hilbertOne = limitResidual + limitProjection := by
    unfold limitResidual
    abel
  rw [he, inner_add_right, ho, add_zero, real_inner_self_eq_norm_sq]
  rfl

theorem limitResidual_inner_dilation_one (m : ℕ) (hm : 0 < m) :
    inner ℝ limitResidual (hilbertDilation m hm hilbertOne) =
      inner ℝ limitResidual (hilbertDilation m hm limitResidual) := by
  have ho : inner ℝ limitResidual (hilbertDilation m hm limitProjection) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (closedSpace_dilation (closedSpace.starProjection_apply_mem hilbertOne) m hm)
  have he : hilbertOne = limitResidual + limitProjection := by
    unfold limitResidual
    abel
  rw [he]
  change inner ℝ limitResidual ((hilbertDilationContinuous m hm) (_ + _)) = _
  rw [map_add, inner_add_right]
  change inner ℝ limitResidual (hilbertDilation m hm limitResidual) +
    inner ℝ limitResidual (hilbertDilation m hm limitProjection) = _
  rw [ho, add_zero]

theorem firstCoordinate_energy_identity :
    hilbertSequence limitResidual 1 / 2 = limitEnergy -
      inner ℝ limitResidual (hilbertDilation 2 (by omega) limitResidual) / 2 := by
  have h := congrArg (fun f => inner ℝ limitResidual f) firstPoint_eq_dilation_difference
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq, inner_sub_right, inner_smul_right,
    limitResidual_inner_one, limitResidual_inner_dilation_one] at h
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at h
  change (1 / 2 : ℝ) * hilbertSequence limitResidual 1 =
    limitEnergy - (1 / 2 : ℝ) * inner ℝ limitResidual (hilbertDilation 2 _ limitResidual) at h
  linarith

theorem firstCoordinate_energy_bounds :
    (1 - Real.sqrt 2 / 2) * limitEnergy ≤ hilbertSequence limitResidual 1 / 2 ∧
    hilbertSequence limitResidual 1 / 2 ≤ (1 + Real.sqrt 2 / 2) * limitEnergy := by
  have h := norm_inner_le_norm (𝕜 := ℝ) limitResidual
    (hilbertDilation 2 (by omega) limitResidual)
  rw [hilbertDilation_norm] at h
  have he : ‖limitResidual‖ ^ 2 = limitEnergy := rfl
  have hb : |inner ℝ limitResidual (hilbertDilation 2 (by omega) limitResidual)| ≤
      Real.sqrt 2 * limitEnergy := by
    rw [Real.norm_eq_abs] at h
    calc
      _ ≤ ‖limitResidual‖ * (Real.sqrt 2 * ‖limitResidual‖) := h
      _ = Real.sqrt 2 * ‖limitResidual‖ ^ 2 := by ring
      _ = _ := by rw [he]
  have hp := firstCoordinate_energy_identity
  constructor <;> nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

theorem firstCoordinate_zero_iff_residual_zero :
    hilbertSequence limitResidual 1 = 0 ↔ limitResidual = 0 := by
  constructor
  · intro hz
    have h := firstCoordinate_energy_bounds.1
    rw [hz] at h
    have hs : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have he : 0 ≤ limitEnergy := sq_nonneg _
    have hzero : limitEnergy = 0 := by nlinarith
    exact limitResidual_zero_iff_energy_zero.mpr hzero
  · intro hz
    rw [hz]
    simp [hilbertSequence]

theorem firstCoordinate_nonneg : 0 ≤ hilbertSequence limitResidual 1 := by
  have h := firstCoordinate_energy_bounds.1
  have hs : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have he : 0 ≤ limitEnergy := sq_nonneg _
  nlinarith

theorem firstPoint_mem_iff_one_mem :
    paretoPointHilbert 0 ∈ closedSpace ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro hmem
    have ho := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hmem
    rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq] at ho
    rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at ho
    change (1 / 2 : ℝ) * hilbertSequence limitResidual 1 = 0 at ho
    have hz : hilbertSequence limitResidual 1 = 0 := by linarith
    exact limitEnergy_zero_iff_mem.mp
      (limitResidual_zero_iff_energy_zero.mp (firstCoordinate_zero_iff_residual_zero.mp hz))
  · intro hmem
    rw [firstPoint_eq_dilation_difference]
    exact closedSpace.sub_mem hmem
      (closedSpace.smul_mem _ (closedSpace_dilation hmem 2 (by omega)))

/-- Conditional reduction: the displayed scalar equality is not proved here. -/
theorem riemannHypothesis_of_firstCoordinate_zero
    (h : hilbertSequence limitResidual 1 = 0) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (firstCoordinate_zero_iff_residual_zero.mp h))

theorem firstCoordinate_zero_iff_limitCoefficients :
    hilbertSequence limitResidual 1 = 0 ↔
      ∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) :=
  firstCoordinate_zero_iff_residual_zero.trans
    limitCoefficients_eq_mobius_iff_residual_zero.symm

theorem firstPoint_error_tendsto_zero_iff :
    Tendsto (walkError residueAtom id (paretoPointHilbert 0)) atTop (𝓝 0) ↔
      ∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) := by
  rw [walkError_tendsto_zero_iff residueAtom id Function.surjective_id,
    firstPoint_mem_iff_one_mem, ← limitCoefficients_eq_mobius_iff_mem]

theorem projection_firstCoordinate_tendsto :
    Tendsto (fun n => hilbertSequence (projection n) 1) atTop
      (𝓝 (hilbertSequence limitProjection 1)) := by
  simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
    (anchoredEvaluationCLM 1).continuous.tendsto limitProjection |>.comp projection_tendsto

theorem projection_firstCoordinate_tendsto_one_iff :
    Tendsto (fun n => hilbertSequence (projection n) 1) atTop (𝓝 1) ↔
      limitResidual = 0 := by
  have he : hilbertSequence limitResidual 1 = 1 - hilbertSequence limitProjection 1 := by
    change hilbertSequenceLinear (hilbertOne - limitProjection) 1 = _
    rw [map_sub]
    change hilbertSequence hilbertOne 1 - hilbertSequence limitProjection 1 = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  constructor
  · intro h
    have hv := tendsto_nhds_unique projection_firstCoordinate_tendsto h
    apply firstCoordinate_zero_iff_residual_zero.mp
    rw [he, hv, sub_self]
  · intro h
    have hz := firstCoordinate_zero_iff_residual_zero.mpr h
    have hv : hilbertSequence limitProjection 1 = 1 := by linarith
    simpa only [hv] using projection_firstCoordinate_tendsto

/-- The full Pareto error of the single point target is an open sufficient input. -/
theorem riemannHypothesis_of_firstPoint_error_tendsto_zero
    (h : Tendsto (walkError residueAtom id (paretoPointHilbert 0)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients (firstPoint_error_tendsto_zero_iff.mp h)

theorem firstCoordinate_exact_positive_identity :
    hilbertSequence limitResidual 1 =
      limitEnergy / 2 +
        ‖limitResidual - (1 / 2 : ℝ) •
          hilbertDilation 2 (by omega) limitResidual‖ ^ 2 := by
  have h := firstCoordinate_energy_identity
  rw [norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, hilbertDilation_norm_sq]
  change hilbertSequence limitResidual 1 =
    limitEnergy / 2 + (limitEnergy -
      2 * ((1 / 2 : ℝ) * inner ℝ limitResidual
        (hilbertDilation 2 (by omega) limitResidual)) +
      |(1 / 2 : ℝ)| ^ 2 * (2 * limitEnergy))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem firstCoordinate_energy_half_le :
    limitEnergy / 2 ≤ hilbertSequence limitResidual 1 := by
  rw [firstCoordinate_exact_positive_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.Pareto.CoefficientStabilization

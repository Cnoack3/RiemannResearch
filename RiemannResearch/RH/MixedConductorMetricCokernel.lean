import RiemannResearch.RH.MixedConductorSquareZero
import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.MixedConductorContractiveSection
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The metric cokernel of the Pareto mixed inclusion

For the original mean `C` with screened section `s`, every bounded real
linear map `f` that kills the mixed closure descends to `f.comp s`.
Its norm is exactly the norm of `f` times the norm of the screened unit.
Taking the screened projection as the test map gives the optimal bound in
the cokernel universal property. The bound is one precisely when the
scalar map of the square-zero algebra is isometric in the original Hilbert norm.

The approximation criterion is Bagchi, *On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis*, Theorem 1,
https://arxiv.org/abs/math/0607733. The factorization and norm identities
below follow directly from the Pareto splitting and the fiber norm estimate.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The physical norm of a scalar under the screened section. -/
theorem norm_screenedMeanSection_apply (a : ℝ) :
    ‖screenedMeanSection a‖ = ‖a‖ * ‖normalizedScreenedTwo‖ := by
  change ‖a • normalizedScreenedTwo‖ = _
  rw [norm_smul]

/-- The canonical section preserves the original distances exactly when the constant is legal. -/
theorem screenedMeanSection_isometry_iff_one_mem :
    Isometry (screenedMeanSection : ℝ → closedSpace) ↔ hilbertOne ∈ closedSpace := by
  rw [← limitEnergy_zero_iff_mem, ← normalizedScreenedTwo_norm_eq_one_iff]
  constructor
  · intro h
    have he := h.dist_eq (1 : ℝ) 0
    simpa only [map_zero, dist_zero_right, norm_screenedMeanSection_apply,
      norm_one, one_mul] using he
  · intro hu
    apply isometry_iff_dist_eq.mpr
    intro a b
    simp only [dist_eq_norm, ← map_sub, norm_screenedMeanSection_apply, hu, mul_one]

/-- The Gram operator of the screened section in the original Hilbert metrics. -/
theorem screenedMeanSection_adjoint_comp_self :
    screenedMeanSection.adjoint.comp screenedMeanSection =
      ‖normalizedScreenedTwo‖ ^ 2 • ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro a
  change screenedMeanSection.adjoint (screenedMeanSection a) = ‖normalizedScreenedTwo‖ ^ 2 * a
  calc
    _ = inner ℝ (screenedMeanSection.adjoint (screenedMeanSection a)) (1 : ℝ) := by
      simp [Real.inner_apply]
    _ = inner ℝ (screenedMeanSection a) (screenedMeanSection 1) :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ‖normalizedScreenedTwo‖ ^ 2 * a := by
      change inner ℝ (a • normalizedScreenedTwo) ((1 : ℝ) • normalizedScreenedTwo) = _
      rw [one_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, mul_comm]

/-- In the real Hilbert category the section is the adjoint of the mean exactly in the
isometric case. -/
theorem screenedMeanSection_isometry_iff_adjoint :
    Isometry (screenedMeanSection : ℝ → closedSpace) ↔
      legalPacketMean.adjoint = screenedMeanSection := by
  rw [screenedMeanSection_isometry_iff_one_mem, ← limitEnergy_zero_iff_mem]
  constructor
  · intro hE
    rw [legalPacketMean_adjoint_eq_scaled_section, hE, sub_zero, one_smul]
  · intro h
    apply screenedPrimeClosure_eq_constantLine_iff_limitEnergy_zero.mp
    apply screenedPrimeClosure_eq_constantLine_iff_coisometry.mpr
    rw [h, legalPacketMean_comp_screenedMeanSection]

/-- The original mean is a morphism in the category of real normed spaces and contractions. -/
theorem norm_legalPacketMean_le_one : ‖legalPacketMean‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, Real.norm_eq_abs]
  calc
    |legalPacketMean v| = |legalPacketMean v| * 1 := (mul_one _).symm
    _ ≤ |legalPacketMean v| * ‖normalizedScreenedTwo‖ :=
      mul_le_mul_of_nonneg_left one_le_norm_normalizedScreenedTwo (abs_nonneg _)
    _ ≤ ‖v‖ := legalPacketMean_fiber_bound v

/-- The screened component of a legal vector is a contraction for every value of the energy. -/
theorem norm_screenedMeanSection_comp_mean_le_one :
    ‖screenedMeanSection.comp legalPacketMean‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.comp_apply, norm_screenedMeanSection_apply,
    Real.norm_eq_abs, one_mul] using legalPacketMean_fiber_bound v

/-- Precomposition with the legal mean has the same exact norm scale for maps from the
scalar line to any real normed target. -/
theorem norm_comp_legalPacketMean_mul {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : ℝ →L[ℝ] Y) :
    ‖g.comp legalPacketMean‖ * ‖normalizedScreenedTwo‖ = ‖g‖ := by
  have hu : 0 < ‖normalizedScreenedTwo‖ :=
    zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  apply le_antisymm
  · apply (le_div_iff₀ hu).mp
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hu.le)
    intro v
    calc
      ‖(g.comp legalPacketMean) v‖ ≤ ‖g‖ * |legalPacketMean v| := by
        simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs] using
          g.le_opNorm (legalPacketMean v)
      _ ≤ (‖g‖ / ‖normalizedScreenedTwo‖) * ‖v‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hu, mul_assoc]
        exact mul_le_mul_of_nonneg_left (legalPacketMean_fiber_bound v) (norm_nonneg _)
  · have h : (g.comp legalPacketMean).comp screenedMeanSection = g := by
      apply ContinuousLinearMap.ext
      intro a
      change g (legalPacketMean (screenedMeanSection a)) = g a
      rw [legalPacketMean_screenedMeanSection]
    calc
      ‖g‖ = ‖(g.comp legalPacketMean).comp screenedMeanSection‖ := congrArg norm h.symm
      _ ≤ ‖g.comp legalPacketMean‖ * ‖screenedMeanSection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = _ := by rw [norm_screenedMeanSection]

/-- Factorization of a contraction annihilating the mixed inclusion, with a prescribed
operator-norm bound on the unique scalar factor. At one this is the cokernel
universal property for real normed spaces and contractions. -/
def LegalMeanFactorizationBound (K : ℝ) : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : closedSpace →L[ℝ] Y),
    f.comp legalMixedInclusion = 0 → ‖f‖ ≤ 1 →
      ∃! g : ℝ →L[ℝ] Y, g.comp legalPacketMean = f ∧ ‖g‖ ≤ K

private theorem mixed_factorization {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : closedSpace →L[ℝ] Y} (hf : f.comp legalMixedInclusion = 0) :
    (f.comp screenedMeanSection).comp legalPacketMean = f := by
  apply ContinuousLinearMap.ext
  intro v
  have hz : f (legalMixedInclusion (legalMixedRetraction v)) = 0 :=
    DFunLike.congr_fun hf (legalMixedRetraction v)
  rw [legalMixedInclusion_legalMixedRetraction, map_sub, sub_eq_zero] at hz
  exact hz.symm

private theorem unique_scalar_factor {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : closedSpace →L[ℝ] Y} {g : ℝ →L[ℝ] Y} (hg : g.comp legalPacketMean = f) :
    g = f.comp screenedMeanSection := by
  apply ContinuousLinearMap.ext
  intro a
  have h := DFunLike.congr_fun hg (screenedMeanSection a)
  change g (legalPacketMean (screenedMeanSection a)) = f (screenedMeanSection a) at h
  change g a = f (screenedMeanSection a)
  simpa only [legalPacketMean_screenedMeanSection] using h

/-- Descending a map that kills the mixed inclusion multiplies its operator norm
by the norm of the screened unit. -/
theorem norm_descend_legalPacketMean {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : closedSpace →L[ℝ] Y} (hf : f.comp legalMixedInclusion = 0) :
    ‖f.comp screenedMeanSection‖ = ‖f‖ * ‖normalizedScreenedTwo‖ := by
  have h := norm_comp_legalPacketMean_mul (f.comp screenedMeanSection)
  rw [mixed_factorization hf] at h
  exact h.symm

/-- The sharp universal factorization bound in the physical normalization.
The screened projection itself realizes the sharpness test. -/
theorem legalMeanFactorizationBound_iff (K : ℝ) :
    LegalMeanFactorizationBound K ↔ ‖normalizedScreenedTwo‖ ≤ K := by
  constructor
  · intro hK
    let p := screenedMeanSection.comp legalPacketMean
    have hp : p.comp legalMixedInclusion = 0 := by
      apply ContinuousLinearMap.ext
      intro m
      change screenedMeanSection (legalPacketMean (legalMixedInclusion m)) = 0
      rw [legalPacketMean_legalMixedInclusion, map_zero]
    obtain ⟨g, ⟨hg, hgK⟩, _⟩ := hK closedSpace p hp norm_screenedMeanSection_comp_mean_le_one
    have hgs : g = screenedMeanSection := by
      apply ContinuousLinearMap.ext
      intro a
      have h := DFunLike.congr_fun hg (screenedMeanSection a)
      change g (legalPacketMean (screenedMeanSection a)) =
        screenedMeanSection (legalPacketMean (screenedMeanSection a)) at h
      simpa only [legalPacketMean_screenedMeanSection] using h
    simpa only [hgs, norm_screenedMeanSection] using hgK
  · intro hK Y _ _ f hf0 hf
    refine ⟨f.comp screenedMeanSection, ⟨mixed_factorization hf0, ?_⟩, ?_⟩
    · calc
        ‖f.comp screenedMeanSection‖ = ‖f‖ * ‖normalizedScreenedTwo‖ :=
          norm_descend_legalPacketMean hf0
        _ ≤ 1 * ‖normalizedScreenedTwo‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
        _ ≤ K := by simpa only [one_mul] using hK
    · intro g hg
      exact unique_scalar_factor hg.1

/-- The actual topological cokernel retains its universal property with contractive
arrows exactly when the screened section is an isometry for the physical norm. -/
theorem legalMean_contractive_cokernel_iff_isometry :
    LegalMeanFactorizationBound 1 ↔ Isometry (screenedMeanSection : ℝ → closedSpace) := by
  rw [legalMeanFactorizationBound_iff, screenedMeanSection_isometry_iff_one_mem,
    ← limitEnergy_zero_iff_mem, ← normalizedScreenedTwo_norm_eq_one_iff]
  exact ⟨fun h => le_antisymm h one_le_norm_normalizedScreenedTwo, fun h => h.le⟩

open scoped LegalMeanAlgebra in
/-- The unital scalar map of the square-zero algebra is isometric precisely when the
unscaled mean has the contractive cokernel property. -/
theorem algebraMap_isometry_iff_contractive_cokernel :
    Isometry (algebraMap ℝ closedSpace) ↔ LegalMeanFactorizationBound 1 := by
  have h : (⇑(algebraMap ℝ closedSpace) : ℝ → closedSpace) = screenedMeanSection :=
    funext LegalMeanAlgebra.algebraMap_apply
  rw [h, legalMean_contractive_cokernel_iff_isometry]

/-- Membership as a contractive cokernel is exactly the discrete Nyman–Beurling
approximation condition. -/
theorem legalMean_contractive_cokernel_iff_naturalApproximation :
    LegalMeanFactorizationBound 1 ↔ BaezDuarte.NaturalApproximation :=
  legalMean_contractive_cokernel_iff_isometry.trans
    (screenedMeanSection_isometry_iff_one_mem.trans
      BaezDuarte.naturalApproximation_iff_one_mem.symm)

/-- The contractive universal property of the physical mean suffices for RH. -/
theorem riemannHypothesis_of_legalMean_contractive_cokernel (h : LegalMeanFactorizationBound 1) :
    RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo (one_mem_closedSpace_iff_normalizedScreenedTwo.mp
    (screenedMeanSection_isometry_iff_one_mem.mp
      (legalMean_contractive_cokernel_iff_isometry.mp h)))

end RiemannResearch.RH.Pareto.PrimePowerSchur

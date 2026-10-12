import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoGibbsEnergy
import RiemannResearch.RH.ParetoGibbsHankel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual bounded Gibbs operator on the complete weighted Hilbert space

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md.
The operator below acts on the existing genuine `ThresholdHilbert` carrier.
Its infinite coordinate series and norm bound are proved, not postulated.
The pi/4 bound is recorded as a reusable proposition. The later module
`ParetoGibbsSpectralGap` proves it using the Gamma-weighted Schur estimate;
that bound is not needed to construct the operator below.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The genuine full-H operator, built from the actual infinite Gibbs action. -/
def hilbertGibbs (f : ThresholdHilbert) : ThresholdHilbert :=
  ⟨fun n => Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical f) n, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (paretoWeight_pos _).le] using
      gibbsAction_square_summable (hilbertGibbsPhysical_square_summable f)⟩

@[simp] theorem hilbertGibbs_apply (f : ThresholdHilbert) (n : ℕ) :
    hilbertGibbs f n =
      Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical f) n := rfl

/-- The bundled operator has exactly the intended physical sequence. -/
@[simp] theorem hilbertGibbs_physical (f : ThresholdHilbert) :
    hilbertGibbsPhysical (hilbertGibbs f) = gibbsAction (hilbertGibbsPhysical f) := by
  funext n
  change Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical f) n /
    Real.sqrt (paretoWeight n) = _
  field_simp [ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos n))]

def hilbertGibbsLinear : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertGibbs
  map_add' f g := by
    apply Subtype.ext
    funext n
    simp only [hilbertGibbs_apply, hilbertGibbsPhysical_add,
      gibbsAction_add (hilbertGibbsPhysical_abs_summable f)
        (hilbertGibbsPhysical_abs_summable g)]
    change Real.sqrt (paretoWeight n) *
      (gibbsAction (hilbertGibbsPhysical f) n + gibbsAction (hilbertGibbsPhysical g) n) =
      Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical f) n +
      Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical g) n
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext n
    simp only [hilbertGibbs_apply, hilbertGibbsPhysical_smul, gibbsAction_smul]
    change Real.sqrt (paretoWeight n) * (c * gibbsAction (hilbertGibbsPhysical f) n) =
      c * (Real.sqrt (paretoWeight n) * gibbsAction (hilbertGibbsPhysical f) n)
    ring

/-- Full infinite-dimensional contraction, without a spectral hypothesis. -/
theorem hilbertGibbs_norm_le (f : ThresholdHilbert) : ‖hilbertGibbs f‖ ≤ ‖f‖ := by
  have hs := gibbsAction_square_contraction (hilbertGibbsPhysical_square_summable f)
  have hout : ‖hilbertGibbs f‖ ^ 2 =
      ∑' n, paretoWeight n * gibbsAction (hilbertGibbsPhysical f) n ^ 2 := by
    rw [hilbert_norm_sq]
    apply tsum_congr
    intro n
    simp only [hilbertGibbs_apply, mul_pow, Real.sq_sqrt (paretoWeight_pos n).le]
  have hin : (∑' n, paretoWeight n * hilbertGibbsPhysical f n ^ 2) = ‖f‖ ^ 2 := by
    simp only [hilbertGibbsPhysical_square, hilbert_norm_sq]
  rw [hin, ← hout] at hs
  nlinarith [norm_nonneg f, norm_nonneg (hilbertGibbs f)]

/-- A bounded linear operator on the complete Hilbert space, with bound one. -/
def hilbertGibbsContinuous : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertGibbsLinear.mkContinuous 1 (fun f => by
    change ‖hilbertGibbs f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using hilbertGibbs_norm_le f)

@[simp] theorem hilbertGibbsContinuous_apply (f : ThresholdHilbert) :
    hilbertGibbsContinuous f = hilbertGibbs f := rfl

theorem hilbertGibbs_mean (f : ThresholdHilbert) :
    (∑' n, paretoWeight n * hilbertGibbsPhysical (hilbertGibbs f) n) =
      ∑' n, paretoWeight n * hilbertGibbsPhysical f n := by
  rw [hilbertGibbs_physical]
  exact gibbsAction_mean (hilbertGibbsPhysical_abs_summable f)

/-- The existing constant target is fixed by the full actual Gibbs operator. -/
theorem hilbertGibbs_one : hilbertGibbs hilbertOne = hilbertOne := by
  apply hilbertSequence_injective
  funext k
  cases k with
  | zero => simp
  | succ n =>
      change hilbertGibbsPhysical (hilbertGibbs hilbertOne) n =
        hilbertGibbsPhysical hilbertOne n
      rw [hilbertGibbs_physical, hilbertGibbs_one_physical, gibbsAction_const]

/-- Mean preservation in the existing Hilbert-space normalization. -/
theorem hilbertGibbs_mean_inner (f : ThresholdHilbert) :
    inner ℝ (hilbertGibbs f) hilbertOne = inner ℝ f hilbertOne := by
  rw [hilbertGibbs_inner_one, hilbertGibbs_inner_one]
  exact hilbertGibbs_mean f

/-- Self-adjointness is proved from the actual infinite symmetric kernel. -/
theorem hilbertGibbs_pairing_symm (f g : ThresholdHilbert) :
    inner ℝ (hilbertGibbs f) g = inner ℝ f (hilbertGibbs g) := by
  rw [← real_inner_comm (hilbertGibbs f) g, hilbertGibbs_inner_physical,
    hilbertGibbs_inner_physical, hilbertGibbs_physical, hilbertGibbs_physical]
  exact gibbsAction_pairing_symm (hilbertGibbsPhysical_square_summable g)
    (hilbertGibbsPhysical_square_summable f)

theorem hilbertGibbsContinuous_isSelfAdjoint : IsSelfAdjoint hilbertGibbsContinuous := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  exact hilbertGibbs_pairing_symm f g

/-- Fixed vectors of the actual bounded operator are precisely the constant line. -/
theorem hilbertGibbs_fixed_iff (f : ThresholdHilbert) :
    hilbertGibbs f = f ↔ ∃ c : ℝ, f = c • hilbertOne := by
  constructor
  · intro hfix
    have hp : gibbsAction (hilbertGibbsPhysical f) = hilbertGibbsPhysical f := by
      rw [← hilbertGibbs_physical, hfix]
    obtain ⟨c, hc⟩ := (gibbsAction_fixed_iff_constant
      (hilbertGibbsPhysical_square_summable f)).mp hp
    refine ⟨c, ?_⟩
    apply hilbertSequence_injective
    funext k
    cases k with
    | zero => simp
    | succ n =>
        change hilbertGibbsPhysical f n = hilbertGibbsPhysical (c • hilbertOne) n
        simp only [hilbertGibbsPhysical_smul, hilbertGibbs_one_physical, hc, mul_one]
  · rintro ⟨c, rfl⟩
    change hilbertGibbsLinear (c • hilbertOne) = c • hilbertOne
    rw [map_smul]
    change c • hilbertGibbs hilbertOne = c • hilbertOne
    rw [hilbertGibbs_one]

/-- The mean-zero pi/4 bound, proved for this actual infinite operator by
`paretoGibbsSharpGap` in `RH/ParetoGibbsSpectralGap`. The proof uses exact
Gamma-weighted infinite Schur rows and the complete tail basis; no external
spectral theorem is imported as an axiom. -/
def ParetoGibbsSharpGap : Prop :=
  ∀ f : ThresholdHilbert,
    (∑' n, paretoWeight n * hilbertGibbsPhysical f n) = 0 →
      ‖hilbertGibbs f‖ ≤ (Real.pi / 4) * ‖f‖

end
end RiemannResearch.RH.Pareto

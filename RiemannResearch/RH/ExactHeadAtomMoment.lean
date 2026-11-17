import RiemannResearch.RH.ExactHeadAtomStability
import RiemannResearch.Analysis.FiniteAffineMomentFunctional
import Mathlib.Tactic

/-!
# Direct signed-moment certification for the actual affine Green fit
The fitted moment is one explicit observation of the actual residual.
Removing upper-span directions gives a centered-probe route to a deficit.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.MobiusAffineProfile

def fittedMomentProbe (x r : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 x,
    affineMomentDual (Finset.Icc 1 x) weight (fun e => (e : ℝ) / x)
      (fun e => (ArithmeticFunction.moebius e : ℝ) / e) d *
        ((d : ℝ) * grid d r)

def atomFittedMoment (P x : ℕ) : ℝ :=
  pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
    (atomResidual P x) (fittedMomentProbe x)

def trialFittedMoment (P x : ℕ) (u : ℕ → ℝ) : ℝ :=
  pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
    (trialResidual P x u) (fittedMomentProbe x)

theorem atomProfile_eq_pairing (P x d : ℕ) :
    atomProfile P x d = pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (atomResidual P x) (fun r => (d : ℝ) * grid d r) := by
  unfold atomProfile score pairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem fitted_moment_eq_probe (P x : ℕ) (hx : 2 ≤ x) (c0 c1 : ℝ)
    (h0 : mass (Finset.Icc 1 x) weight * c0 +
      (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x)) * c1 =
        ∑ d ∈ Finset.Icc 1 x, weight d * atomProfile P x d)
    (h1 : (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x)) * c0 +
      energy (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x) * c1 =
        ∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x) * atomProfile P x d) :
    signedSum x (fun d => c0 + c1 * ((d : ℝ) / x)) = atomFittedMoment P x := by
  have hd := MobiusAffineProfile.affine_determinant_pos x hx
  have hm := affine_signed_moment_eq_dual (Finset.Icc 1 x) weight
    (fun d => (d : ℝ) / x) (fun d => (ArithmeticFunction.moebius d : ℝ) / d)
    (atomProfile P x) c0 c1 hd.ne' h0 h1
  unfold atomFittedMoment fittedMomentProbe
  rw [pairing_finite_combination]
  simp_rw [← atomProfile_eq_pairing P x]
  exact hm

theorem trial_fitted_moment_error_sq_le (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    (trialFittedMoment P x u - atomFittedMoment P x) ^ 2 ≤
      defectBudget P x u *
        energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (fittedMomentProbe x) :=
  trial_observation_error_sq_le P x hP u (fittedMomentProbe x)

theorem target_pairing_eq_energy (P x : ℕ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (atomResidual P x) (target P) = atomEnergy P x := by
  have hn := atomResidual_normal P x (atomResidual P x - target P)
    (atomResidual_sub_target_mem P x)
  have he :
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (atomResidual P x) (atomResidual P x - target P) =
      atomEnergy P x - pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (atomResidual P x) (target P) := by
    unfold atomEnergy energy pairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [Pi.sub_apply]
    ring
  rw [he] at hn
  linarith

theorem fitted_moment_gap_eq_pairing (P x : ℕ) (alpha : ℝ)
    (v : ℕ → ℝ) (hv : v ∈ upperSpan P x (atom P)) :
    atomFittedMoment P x - alpha * atomEnergy P x =
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) := by
  have hn := atomResidual_normal P x v hv
  have he :
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) =
      atomFittedMoment P x - alpha *
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) (target P) -
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) v := by
    unfold atomFittedMoment pairing
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only
    ring
  rw [target_pairing_eq_energy, hn, sub_zero] at he
  exact he.symm

theorem fitted_moment_gap_sq_le (P x : ℕ) (alpha : ℝ)
    (v : ℕ → ℝ) (hv : v ∈ upperSpan P x (atom P)) :
    (atomFittedMoment P x - alpha * atomEnergy P x) ^ 2 ≤ atomEnergy P x *
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) := by
  rw [fitted_moment_gap_eq_pairing P x alpha v hv]
  exact pairing_sq_le _ _ _ _ (fun r _ => progressionWeight_nonneg P r)

/-- A bounded centered probe supplies the signed-moment budget without bounding q. -/
theorem fitted_moment_deficit_of_probe_bound (P x : ℕ) (alpha M eps : ℝ)
    (hM : 0 ≤ M) (heps : 0 < eps) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan P x (atom P))
    (hb : energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fun r => fittedMomentProbe x r - alpha * target P r - v r) ≤ M) :
    atomFittedMoment P x ≤
      (alpha + eps) * atomEnergy P x + M / (4 * eps) := by
  have hq : 0 ≤ atomEnergy P x :=
    energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)
  have hs := (fitted_moment_gap_sq_le P x alpha v hv).trans
    (mul_le_mul_of_nonneg_left hb hq)
  have h := one_sided_of_square_budget (atomFittedMoment P x - alpha * atomEnergy P x)
    (atomEnergy P x) M eps hq hM heps hs
  nlinarith only [h]

private theorem upper_span_eval_zero (P x r : ℕ) (hr : r ≤ x) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan P x (atom P)) : v r = 0 := by
  let eval : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan : upperSpan P x (atom P) ≤ LinearMap.ker eval := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    exact LinearMap.mem_ker.mpr (atom_zero_of_lt P d r (hr.trans_lt (Finset.mem_filter.mp hd).2))
  exact LinearMap.mem_ker.mp (hspan hv)

private theorem primorial_residual_zero_on_head (x r : ℕ) (hr : r ∈ Finset.Icc 1 x) :
    atomResidual (MobiusHeadGreen.greenPeriod x) x r = 0 := by
  have hxP := MobiusHeadGreen.greenPeriod_gt x
  obtain ⟨hr1, hrx⟩ := Finset.mem_Icc.mp hr
  have hrP : r ∈ Finset.Icc 1 (MobiusHeadGreen.greenPeriod x - 1) :=
    Finset.mem_Icc.mpr ⟨hr1, by omega⟩
  rw [← primorial_residual_eq_atomResidual x r hrP]
  exact MobiusHeadGreen.residual_head _ x hxP.le _
    (MobiusHeadGreen.primorialNormalCoefficients_spec x).1 r hr1 hrx

/-- Centering and every upper-span correction vanish on the positive exact head. -/
theorem centered_probe_eq_on_primorial_head (x r : ℕ) (hr : r ∈ Finset.Icc 1 x)
    (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (MobiusHeadGreen.greenPeriod x) x (atom (MobiusHeadGreen.greenPeriod x))) :
    fittedMomentProbe x r - alpha * target (MobiusHeadGreen.greenPeriod x) r - v r =
      fittedMomentProbe x r := by
  have hrx := (Finset.mem_Icc.mp hr).2
  have hzero := primorial_residual_zero_on_head x r hr
  have hs := upper_span_eval_zero _ _ r hrx _ (atomResidual_sub_target_mem
    (MobiusHeadGreen.greenPeriod x) x)
  change atomResidual (MobiusHeadGreen.greenPeriod x) x r -
    target (MobiusHeadGreen.greenPeriod x) r = 0 at hs
  have ht : target (MobiusHeadGreen.greenPeriod x) r = 0 := by linarith only [hzero, hs]
  rw [ht, upper_span_eval_zero _ _ r hrx _ hv, mul_zero, sub_zero, sub_zero]

/-- A correction can only change the part of the energy outside the exact head. -/
theorem complete_centered_probe_energy_split (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (MobiusHeadGreen.greenPeriod x) x (atom (MobiusHeadGreen.greenPeriod x))) :
    let P := MobiusHeadGreen.greenPeriod x
    let f := fun r => fittedMomentProbe x r - alpha * target P r - v r
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f =
      energy (Finset.Icc 1 x) (progressionWeight P) (fittedMomentProbe x) +
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 x) (progressionWeight P) f := by
  dsimp only
  have hxP := MobiusHeadGreen.greenPeriod_gt x
  have hsub : Finset.Icc 1 x ⊆ Finset.Icc 1 (MobiusHeadGreen.greenPeriod x - 1) :=
    Finset.Icc_subset_Icc_right (by omega)
  let f := fun r => fittedMomentProbe x r - alpha * target (MobiusHeadGreen.greenPeriod x) r - v r
  have he : energy (Finset.Icc 1 x) (progressionWeight (MobiusHeadGreen.greenPeriod x)) f =
      energy (Finset.Icc 1 x) (progressionWeight (MobiusHeadGreen.greenPeriod x)) (fittedMomentProbe x) := by
    unfold energy
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [f]
    rw [centered_probe_eq_on_primorial_head x r hr alpha v hv]
  change _ = _ + energy _ _ f
  rw [← he, add_comm]
  exact (Finset.sum_sdiff hsub).symm

theorem primorial_head_probe_energy_le (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (MobiusHeadGreen.greenPeriod x) x (atom (MobiusHeadGreen.greenPeriod x))) :
    let P := MobiusHeadGreen.greenPeriod x
    energy (Finset.Icc 1 x) (progressionWeight P) (fittedMomentProbe x) ≤
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) := by
  dsimp only
  rw [complete_centered_probe_energy_split x alpha v hv]
  exact le_add_of_nonneg_right (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg _ r))

/-- The moment sees only the residues outside the exact head. -/
theorem fitted_moment_gap_sq_le_tail (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (MobiusHeadGreen.greenPeriod x) x
      (atom (MobiusHeadGreen.greenPeriod x))) :
    let P := MobiusHeadGreen.greenPeriod x
    (atomFittedMoment P x - alpha * atomEnergy P x) ^ 2 ≤ atomEnergy P x *
      energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 x) (progressionWeight P)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) := by
  let P := MobiusHeadGreen.greenPeriod x
  let s := Finset.Icc 1 (P - 1)
  let t := s \ Finset.Icc 1 x
  let f := fun r => fittedMomentProbe x r - alpha * target P r - v r
  change (atomFittedMoment P x - alpha * atomEnergy P x) ^ 2 ≤
    atomEnergy P x * energy t (progressionWeight P) f
  have hs : t ⊆ s := Finset.sdiff_subset
  have hz (r : ℕ) (hrs : r ∈ s) (hrt : r ∉ t) : atomResidual P x r = 0 := by
    apply primorial_residual_zero_on_head x r
    by_contra h
    exact hrt (Finset.mem_sdiff.mpr ⟨hrs, h⟩)
  rw [fitted_moment_gap_eq_pairing P x alpha v hv]
  change (pairing s (progressionWeight P) (atomResidual P x) f) ^ 2 ≤ _
  rw [← pairing_support s t (progressionWeight P) (atomResidual P x) f hs hz]
  have he : energy t (progressionWeight P) (atomResidual P x) = atomEnergy P x :=
    energy_support s t (progressionWeight P) (atomResidual P x) hs hz
  rw [← he]
  exact pairing_sq_le t (progressionWeight P) (atomResidual P x) f
    (fun r _ => progressionWeight_nonneg P r)

/-- A uniform bound for the complementary energy suffices for the R5 moment budget. -/
theorem fitted_moment_deficit_of_tail_probe_bound (x : ℕ) (alpha M eps : ℝ)
    (hM : 0 ≤ M) (heps : 0 < eps) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (MobiusHeadGreen.greenPeriod x) x
      (atom (MobiusHeadGreen.greenPeriod x)))
    (hb : let P := MobiusHeadGreen.greenPeriod x
      energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 x) (progressionWeight P)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) ≤ M) :
    let P := MobiusHeadGreen.greenPeriod x
    atomFittedMoment P x ≤ (alpha + eps) * atomEnergy P x + M / (4 * eps) := by
  dsimp only at hb ⊢
  let P := MobiusHeadGreen.greenPeriod x
  have hq : 0 ≤ atomEnergy P x :=
    energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)
  have hs := (fitted_moment_gap_sq_le_tail x alpha v hv).trans
    (mul_le_mul_of_nonneg_left hb hq)
  have h := one_sided_of_square_budget (atomFittedMoment P x - alpha * atomEnergy P x)
    (atomEnergy P x) M eps hq hM heps hs
  change atomFittedMoment P x ≤ _
  nlinarith only [h]

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer

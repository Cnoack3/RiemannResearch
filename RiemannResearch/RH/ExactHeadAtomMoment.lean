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

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer

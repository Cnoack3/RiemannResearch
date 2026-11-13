import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Invertible P/Q density and distinct reciprocal operators

Source: user-provided change-of-measure identities, 12 November 2026.
B denotes QDensityMetric.B = dQ/dP throughout this module.
The local notation R resolves the historical QShiftedReciprocal.B name;
it always means physical multiplication by 1/(n+1).
Physical n >= 1 corresponds to normalized coordinate n-1.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityMetricInverse
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QDensityMetric QReciprocalMetric
local notation "R" => QShiftedReciprocal.B

/-- The bounded inverse density dP/dQ on the Q realization. -/
def inverse : QHilbert →L[ℝ] QHilbert :=
  zetaTwo • (ContinuousLinearMap.id ℝ QHilbert - R)

@[simp] theorem inverse_apply (f : QHilbert) (n : ℕ) :
    inverse f n = zetaTwo * (f n - f n / ((n : ℝ) + 2)) := rfl

@[simp] theorem inverse_B (f : QHilbert) : inverse (B f) = f := by
  apply Subtype.ext
  funext n
  change zetaTwo * ((1 / zetaTwo) * (f n + f n / ((n : ℝ) + 1)) -
    ((1 / zetaTwo) * (f n + f n / ((n : ℝ) + 1))) / ((n : ℝ) + 2)) = f n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2, ne_of_gt zetaTwo_pos]
  ring

@[simp] theorem B_inverse (f : QHilbert) : B (inverse f) = f := by
  apply Subtype.ext
  funext n
  change (1 / zetaTwo) * (zetaTwo * (f n - f n / ((n : ℝ) + 2)) +
    (zetaTwo * (f n - f n / ((n : ℝ) + 2))) / ((n : ℝ) + 1)) = f n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2, ne_of_gt zetaTwo_pos]
  ring

/-- The density is a continuous linear equivalence, not the physical identity. -/
def densityEquiv : QHilbert ≃L[ℝ] QHilbert where
  toLinearEquiv :=
    { B.toLinearMap with
      invFun := inverse
      left_inv := inverse_B
      right_inv := B_inverse }
  continuous_toFun := B.continuous
  continuous_invFun := inverse.continuous

@[simp] theorem densityEquiv_apply (f : QHilbert) : densityEquiv f = B f := rfl

theorem qSequence_inverse (f : QHilbert) (k : ℕ) :
    qSequence (inverse f) k =
      (zetaTwo * (k : ℝ) / ((k : ℝ) + 1)) * qSequence f k := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [qSequence_succ, inverse_apply, Nat.cast_add, Nat.cast_one]
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h2]
    ring

theorem D_eq_density (f : QHilbert) : D f = zetaTwo • B f - f := by
  change D f = zetaTwo • ((1 / zetaTwo) • (f + D f)) - f
  rw [smul_smul, mul_one_div_cancel (ne_of_gt zetaTwo_pos), one_smul]
  abel

theorem inverse_D (f : QHilbert) : inverse (D f) = zetaTwo • R f := by
  change zetaTwo • (D f - R (D f)) = _
  rw [D_sub_B_D]

theorem R_eq_inverse_D (f : QHilbert) :
    R f = (1 / zetaTwo) • inverse (D f) := by
  rw [inverse_D, smul_smul, one_div_mul_cancel (ne_of_gt zetaTwo_pos), one_smul]

theorem R_eq_inverse (f : QHilbert) :
    R f = f - (1 / zetaTwo) • inverse f := by
  change R f = f - (1 / zetaTwo) • (zetaTwo • (f - R f))
  rw [smul_smul, one_div_mul_cancel (ne_of_gt zetaTwo_pos), one_smul]
  abel

/-- Exact inner-product transport for the same physical sequences. -/
theorem pareto_inner_inverse (f g : QHilbert) :
    inner ℝ (toPareto f) (toPareto g) = inner ℝ f (inverse g) := by
  rw [QShiftedReciprocal.pareto_inner_identity]
  change _ = inner ℝ f (zetaTwo • (g - R g))
  rw [inner_smul_right, inner_sub_right]

theorem q_inner_density (f g : QHilbert) :
    inner ℝ f g = inner ℝ (toPareto f) (toPareto (B g)) := by
  rw [pareto_inner_inverse, inverse_B]

/-- The Q pairing as a sum of two P pairings of the same physical sequences. -/
theorem q_inner_pareto_add_D (f g : QHilbert) :
    inner ℝ f g = (1 / zetaTwo) *
      (inner ℝ (toPareto f) (toPareto g) +
        inner ℝ (toPareto f) (toPareto (D g))) := by
  rw [q_inner_density]
  change inner ℝ (toPareto f) (toParetoCLM ((1 / zetaTwo) • (g + D g))) = _
  rw [map_smul, map_add, inner_smul_right, inner_add_right]
  rfl

/-- On a closed P subspace, the second argument may be compressed back into it. -/
theorem q_inner_pareto_compressed (S : Submodule ℝ Pareto.ThresholdHilbert)
    [S.HasOrthogonalProjection] (f g : QHilbert) (hf : toPareto f ∈ S) :
    inner ℝ f g = (1 / zetaTwo) *
      (inner ℝ (toPareto f) (toPareto g) +
        inner ℝ (toPareto f) (S.starProjection (toPareto (D g)))) := by
  rw [q_inner_pareto_add_D, ← S.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hf]

theorem norm_comparison (f : QHilbert) :
    (zetaTwo / 2) * ‖f‖ ^ 2 ≤ ‖toPareto f‖ ^ 2 ∧
      ‖toPareto f‖ ^ 2 ≤ zetaTwo * ‖f‖ ^ 2 := by
  constructor
  · have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq f
    linarith
  · exact toPareto_norm_sq_le f

/-- D in the P realization, obtained by preserving physical sequences. -/
def DP : Pareto.ThresholdHilbert →L[ℝ] Pareto.ThresholdHilbert :=
  toParetoCLM.comp (D.comp toQCLM)

theorem DP_toPareto (f : QHilbert) : DP (toPareto f) = toPareto (D f) := by
  change toPareto (D (toQ (toPareto f))) = _
  rw [toQ_toPareto]

theorem DP_physical (f : Pareto.ThresholdHilbert) (k : ℕ) :
    Pareto.hilbertSequence (DP f) k = Pareto.hilbertSequence f k / (k : ℝ) := by
  change Pareto.hilbertSequence (toPareto (D (toQ f))) k = _
  rw [toPareto_sequence, qSequence_D, toQ_sequence]

/-- Invertible density maps commute with taking the closure of a subspace. -/
theorem map_closure (S : Submodule ℝ QHilbert) :
    S.topologicalClosure.map B.toLinearMap =
      (S.map B.toLinearMap).topologicalClosure := by
  apply SetLike.coe_injective
  exact densityEquiv.toHomeomorph.image_closure (S : Set QHilbert)

theorem mem_density_closure_iff (S : Submodule ℝ QHilbert) (f : QHilbert) :
    B f ∈ (S.map B.toLinearMap).topologicalClosure ↔ f ∈ S.topologicalClosure := by
  rw [← map_closure]
  constructor
  · rintro ⟨x, hx, he⟩
    have hxf : x = f := densityEquiv.injective he
    exact hxf ▸ hx
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem density_closure_eq_top_iff (S : Submodule ℝ QHilbert) :
    (S.map B.toLinearMap).topologicalClosure = ⊤ ↔ S.topologicalClosure = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro f _
    apply (mem_density_closure_iff S f).mp
    rw [h]
    trivial
  · intro h
    rw [← map_closure, h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr densityEquiv.surjective

end RiemannResearch.RH.QDensityMetricInverse

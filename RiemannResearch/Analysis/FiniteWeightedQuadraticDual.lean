import RiemannResearch.Analysis.CumulativeEnergySummability
import RiemannResearch.Analysis.WeightedScalarEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact finite weighted quadratic duality

Source: user-provided `V_vector_space_RH.pdf`, Sections 7--8 (16 September 2026),
for the prescribed arithmetic-energy problem and its finite square completion.
The exact primal--dual identities below are elementary consequences. The RH
consumer is `RH.ChebyshevEnergyDual`; no arithmetic bound is asserted here.

All signed terms are retained. Nonnegative weights suffice for strong duality;
strictly positive weights are needed only for uniqueness on the tested set.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedQuadraticDual

open WeightedScalarEnergy

def dualValue {ι : Type*} (S : Finset ι) (w e y : ι → ℝ) : ℝ :=
  ∑ i ∈ S, w i * (2 * e i * y i - y i ^ 2)

theorem gap {ι : Type*} (S : Finset ι) (w e y : ι → ℝ) :
    square S w e - dualValue S w e y =
      square S w (fun i => e i - y i) := by
  unfold square dualValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weak_duality {ι : Type*} (S : Finset ι) (w e y : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    dualValue S w e y ≤ square S w e := by
  have hg := gap S w e y
  have hn := square_nonneg S w (fun i => e i - y i) hw
  linarith

theorem attained {ι : Type*} (S : Finset ι) (w e : ι → ℝ) :
    dualValue S w e e = square S w e := by
  unfold square dualValue
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem isGreatest {ι : Type*} (S : Finset ι) (w e : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    IsGreatest (Set.range (dualValue S w e)) (square S w e) := by
  refine ⟨⟨e, attained S w e⟩, ?_⟩
  rintro z ⟨y, rfl⟩
  exact weak_duality S w e y hw

theorem square_le_iff_dual_le {ι : Type*} (S : Finset ι) (w e : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (C : ℝ) :
    square S w e ≤ C ↔ ∀ y : ι → ℝ, dualValue S w e y ≤ C := by
  constructor
  · intro h y
    exact (weak_duality S w e y hw).trans h
  · intro h
    simpa only [attained] using h e

theorem equality_iff {ι : Type*} (S : Finset ι) (w e y : ι → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) :
    dualValue S w e y = square S w e ↔ ∀ i ∈ S, y i = e i := by
  constructor
  · intro he
    have hz : square S w (fun i => e i - y i) = 0 := by
      rw [← gap, he, sub_self]
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => mul_nonneg (hw i hi).le (sq_nonneg (e i - y i)))).mp hz
    intro i hi
    have hsq : (e i - y i) ^ 2 = 0 :=
      (mul_eq_zero.mp (hz' i hi)).resolve_left (ne_of_gt (hw i hi))
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)).symm
  · intro he
    rw [← attained S w e]
    unfold dualValue
    exact Finset.sum_congr rfl (fun i hi => by rw [he i hi])

theorem summable_iff_uniform_dual_bound (w e : ℕ → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Summable (fun i => w i * e i ^ 2) ↔
      ∃ C : ℝ, ∀ N (y : ℕ → ℝ), dualValue (Finset.range N) w e y ≤ C := by
  rw [NonnegativeEnergy.summable_iff_nonnegative_prefix_bound _
    (fun i => mul_nonneg (hw i) (sq_nonneg _))]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun N => (square_le_iff_dual_le _ w e (fun i _ => hw i) C).mp (hC N)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun N => (square_le_iff_dual_le _ w e (fun i _ => hw i) C).mpr (hC N)⟩

end RiemannResearch.Analysis.FiniteWeightedQuadraticDual

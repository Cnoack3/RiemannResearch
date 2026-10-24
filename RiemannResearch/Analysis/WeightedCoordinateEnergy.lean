import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# An explicit summably weighted coordinate energy

Source: fifth Ramanujan transfer program, 24 October 2026.
Every coordinate gets strictly positive weight. Normalization by its full
operator norm proves a geometric majorant, including a uniform tail bound.
Convergence therefore follows from boundedness and pointwise coordinate
convergence; summability and domination are conclusions, not assumptions.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.WeightedCoordinateEnergy
variable {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def weight (ℓ : ℕ → H →L[ℝ] ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖ℓ n‖ ^ 2)

def energy (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) : ℝ :=
  ∑' n, weight ℓ n * (ℓ n x) ^ 2

theorem weight_pos (ℓ : ℕ → H →L[ℝ] ℝ) (n : ℕ) : 0 < weight ℓ n := by
  unfold weight
  positivity

theorem weight_le_geometric (ℓ : ℕ → H →L[ℝ] ℝ) (n : ℕ) :
    weight ℓ n ≤ (1 / 2 : ℝ) ^ n := by
  unfold weight
  apply (div_le_iff₀ (show 0 < 1 + ‖ℓ n‖ ^ 2 by positivity)).mpr
  nlinarith [pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) n,
    mul_nonneg (pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) n) (sq_nonneg ‖ℓ n‖)]

theorem weight_summable (ℓ : ℕ → H →L[ℝ] ℝ) : Summable (weight ℓ) :=
  Summable.of_nonneg_of_le (fun n => (weight_pos ℓ n).le)
    (weight_le_geometric ℓ) summable_geometric_two

theorem summand_bound (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) (n : ℕ) :
    weight ℓ n * (ℓ n x) ^ 2 ≤ (1 / 2 : ℝ) ^ n * ‖x‖ ^ 2 := by
  have hop := mul_self_le_mul_self (norm_nonneg (ℓ n x)) ((ℓ n).le_opNorm x)
  have hs : (ℓ n x) ^ 2 ≤ (1 + ‖ℓ n‖ ^ 2) * ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (show ‖ℓ n x‖ ^ 2 ≤ (1 + ‖ℓ n‖ ^ 2) * ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖])
  have hn := mul_le_mul_of_nonneg_left hs (weight_pos ℓ n).le
  have he : weight ℓ n * ((1 + ‖ℓ n‖ ^ 2) * ‖x‖ ^ 2) =
      (1 / 2 : ℝ) ^ n * ‖x‖ ^ 2 := by
    rw [← mul_assoc, weight, div_mul_cancel₀ _ (by positivity : 1 + ‖ℓ n‖ ^ 2 ≠ 0)]
  exact hn.trans_eq he

theorem summand_summable (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) :
    Summable (fun n => weight ℓ n * (ℓ n x) ^ 2) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_pos ℓ n).le (sq_nonneg _))
    (summand_bound ℓ x) (summable_geometric_two.mul_right (‖x‖ ^ 2))

theorem energy_nonneg (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) : 0 ≤ energy ℓ x :=
  tsum_nonneg (fun n => mul_nonneg (weight_pos ℓ n).le (sq_nonneg _))

theorem energy_le (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) : energy ℓ x ≤ 2 * ‖x‖ ^ 2 := by
  have h := (summand_summable ℓ x).tsum_le_tsum (summand_bound ℓ x)
    (summable_geometric_two.mul_right (‖x‖ ^ 2))
  simpa only [energy, tsum_mul_right, tsum_geometric_two] using h

theorem summand_le_energy (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) (n : ℕ) :
    weight ℓ n * (ℓ n x) ^ 2 ≤ energy ℓ x := by
  simpa only [Finset.sum_singleton, energy] using
    (summand_summable ℓ x).sum_le_tsum {n}
      (fun i hi => mul_nonneg (weight_pos ℓ i).le (sq_nonneg _))

theorem energy_eq_zero_iff (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) :
    energy ℓ x = 0 ↔ ∀ n, ℓ n x = 0 := by
  constructor
  · intro he n
    have hb := summand_le_energy ℓ x n
    rw [he] at hb
    have hs : (ℓ n x) ^ 2 = 0 := by
      have hp := weight_pos ℓ n
      nlinarith [sq_nonneg (ℓ n x)]
    exact sq_eq_zero_iff.mp hs
  · intro hz
    simp only [energy, hz, sq, mul_zero, tsum_zero]

/-- The omitted infinite tail is explicitly bounded, uniformly on norm-bounded sets. -/
theorem tail_le (ℓ : ℕ → H →L[ℝ] ℝ) (x : H) (N : ℕ) :
    (∑' j, weight ℓ (j + N) * (ℓ (j + N) x) ^ 2) ≤
      2 * (1 / 2 : ℝ) ^ N * ‖x‖ ^ 2 := by
  have hs := (summand_summable ℓ x).comp_injective
    (i := fun j : ℕ => j + N) (fun i j h => Nat.add_right_cancel h)
  have hg : Summable (fun j => (1 / 2 : ℝ) ^ (j + N) * ‖x‖ ^ 2) := by
    simpa only [pow_add, mul_assoc] using
      summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ N * ‖x‖ ^ 2)
  have h := hs.tsum_le_tsum (fun j => summand_bound ℓ x (j + N)) hg
  simpa only [pow_add, mul_assoc, tsum_mul_right, tsum_geometric_two] using h

/-- A single eventually uniform norm bound proves all domination needed by Tannery. -/
theorem energy_tendsto_of_coordinates {l : Filter α}
    (ℓ : ℕ → H →L[ℝ] ℝ) (F : α → H) (x : H)
    (hcoord : ∀ n, Tendsto (fun i => ℓ n (F i)) l (𝓝 (ℓ n x)))
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ B) :
    Tendsto (fun i => energy ℓ (F i)) l (𝓝 (energy ℓ x)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_geometric_two.mul_right B)
  · intro n
    exact ((hcoord n).pow 2).const_mul (weight ℓ n)
  · filter_upwards [hbound] with i hi n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_pos ℓ n).le (sq_nonneg _))]
    exact (summand_bound ℓ (F i) n).trans
      (mul_le_mul_of_nonneg_left hi (by positivity))

end RiemannResearch.Analysis.WeightedCoordinateEnergy

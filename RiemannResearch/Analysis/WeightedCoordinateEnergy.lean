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

namespace RiemannResearch.Analysis.WeightedCoordinateEnergy
variable {H α ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A complete observation energy with arbitrary nonnegative weights. The
natural summability hypothesis concerns weighted squared operator norms;
no summability of the weights themselves is required. -/
def observationEnergy (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (x : H) : ℝ :=
  ∑' j, w j * (ℓ j x) ^ 2

def observationMass (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) : ℝ :=
  ∑' j, w j * ‖ℓ j‖ ^ 2

theorem observation_summand_bound (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (x : H) (j : ι) :
    w j * (ℓ j x) ^ 2 ≤ (w j * ‖ℓ j‖ ^ 2) * ‖x‖ ^ 2 := by
  have hop := mul_self_le_mul_self (norm_nonneg (ℓ j x)) ((ℓ j).le_opNorm x)
  have hs : (ℓ j x) ^ 2 ≤ ‖ℓ j‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, ← pow_two, sq_abs, mul_pow] using hop
  calc
    _ ≤ w j * (‖ℓ j‖ ^ 2 * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hs (hw j)
    _ = _ := by ring

theorem observation_summable (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    Summable (fun j => w j * (ℓ j x) ^ 2) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (sq_nonneg _))
    (observation_summand_bound w ℓ hw x) (hs.mul_right (‖x‖ ^ 2))

theorem observationEnergy_nonneg (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (x : H) : 0 ≤ observationEnergy w ℓ x :=
  tsum_nonneg (fun j => mul_nonneg (hw j) (sq_nonneg _))

theorem observationEnergy_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    observationEnergy w ℓ x ≤ observationMass w ℓ * ‖x‖ ^ 2 := by
  have h := (observation_summable w ℓ hw hs x).tsum_le_tsum
    (observation_summand_bound w ℓ hw x) (hs.mul_right (‖x‖ ^ 2))
  simpa only [observationEnergy, observationMass, tsum_mul_right] using h

theorem observation_summand_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) (j : ι) :
    w j * (ℓ j x) ^ 2 ≤ observationEnergy w ℓ x := by
  classical
  simpa only [Finset.sum_singleton, observationEnergy] using
    (observation_summable w ℓ hw hs x).sum_le_tsum {j}
      (fun i hi => mul_nonneg (hw i) (sq_nonneg _))

/-- Zero energy sees exactly the coordinates on the support of the weights. -/
theorem observationEnergy_eq_zero_iff_supported (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    observationEnergy w ℓ x = 0 ↔ ∀ j, w j = 0 ∨ ℓ j x = 0 := by
  constructor
  · intro h j
    have hle := observation_summand_le w ℓ hw hs x j
    rw [h] at hle
    have hz : w j * (ℓ j x) ^ 2 = 0 :=
      le_antisymm hle (mul_nonneg (hw j) (sq_nonneg _))
    rcases mul_eq_zero.mp hz with hw | hx
    · exact Or.inl hw
    · exact Or.inr (sq_eq_zero_iff.mp hx)
  · intro h
    have hz (j : ι) : w j * (ℓ j x) ^ 2 = 0 := by
      rcases h j with hj | hj <;>
        simp only [hj, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
    simp only [observationEnergy, hz, tsum_zero]

theorem observationEnergy_eq_zero_iff (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 < w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    observationEnergy w ℓ x = 0 ↔ ∀ j, ℓ j x = 0 := by
  rw [observationEnergy_eq_zero_iff_supported w ℓ (fun j => (hw j).le) hs x]
  constructor
  · intro h j
    exact (h j).resolve_left (hw j).ne'
  · intro h j
    exact Or.inr (h j)

/-- Bounded coordinate convergence controls the complete energy under the
weighted operator-norm moment hypothesis, for arbitrary parameter filters. -/
theorem observationEnergy_tendsto {l : Filter α}
    (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (F : α → H) (x : H)
    (hcoord : ∀ j, Tendsto (fun i => ℓ j (F i)) l (𝓝 (ℓ j x)))
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w ℓ (F i)) l (𝓝 (observationEnergy w ℓ x)) := by
  apply tendsto_tsum_of_dominated_convergence (hs.mul_right B)
  · intro j
    exact ((hcoord j).pow 2).const_mul (w j)
  · filter_upwards [hbound] with i hi j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw j) (sq_nonneg _))]
    exact (observation_summand_bound w ℓ hw (F i) j).trans
      (mul_le_mul_of_nonneg_left hi (mul_nonneg (hw j) (sq_nonneg _)))

/-- Any summable nonnegative envelope generates an admissible weighting. -/
theorem normalized_envelope_moment_summable
    (u : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hu : ∀ j, 0 ≤ u j) (hs : Summable u) :
    Summable (fun j => (u j / (1 + ‖ℓ j‖ ^ 2)) * ‖ℓ j‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (div_nonneg (hu j) (by positivity)) (sq_nonneg _)) _ hs
  intro j
  have hd : 0 < 1 + ‖ℓ j‖ ^ 2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith [hu j]

/-- In particular the earlier geometric weights satisfy the stronger
weighted operator-norm summability condition. -/
theorem geometric_weight_moment_summable (ℓ : ℕ → H →L[ℝ] ℝ) :
    Summable (fun j => weight ℓ j * ‖ℓ j‖ ^ 2) :=
  normalized_envelope_moment_summable (fun j => (1 / 2 : ℝ) ^ j) ℓ
    (fun j => by positivity) summable_geometric_two

end RiemannResearch.Analysis.WeightedCoordinateEnergy

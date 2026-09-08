import RiemannResearch.RH.CombinedAudited.WeightedPythagoras
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite weighted fibers and exact partial repair

Source: user-provided `RH_Two_Seed_Threshold.tex`, revised September 7, 2026,
Section 10, Proposition `prop:crt-defect`, equations `eq:crt-fiber-variance`,
`eq:crt-repair-pythagoras`, and Corollary `cor:crt-partial`.

These are unconditional finite real identities for actual weighted sums.
They prove the weighted conditional mean and its complete error decomposition,
not merely a Pythagorean consequence with orthogonality assumed. The final
results optimize addition of one actual correction vector, retaining the
mixed term. Specialization to the infinite quotient weights of the paper,
legal-generator completeness, and a vanishing two-seed error remain separate.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedFiniteProjection

variable {ι κ : Type*}

noncomputable def mass (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, w i

noncomputable def mean (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * x i) / mass s w

noncomputable def energy (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * x i ^ 2

noncomputable def pairing (s : Finset ι) (w x y : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * x i * y i

theorem mean_mass (s : Finset ι) (w x : ι → ℝ) (hW : mass s w ≠ 0) :
    mass s w * mean s w x = ∑ i ∈ s, w i * x i := by
  unfold mean
  field_simp [hW]

theorem centered_sum (s : Finset ι) (w x : ι → ℝ) (hW : mass s w ≠ 0) :
    (∑ i ∈ s, w i * (x i - mean s w x)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ i ∈ s, w i * x i) - mass s w * mean s w x = 0
  rw [mean_mass s w x hW, sub_self]

theorem centered_cross (s : Finset ι) (w x : ι → ℝ)
    (hW : mass s w ≠ 0) (c : ℝ) :
    pairing s w (fun i => x i - mean s w x) (fun _ => c) = 0 := by
  unfold pairing
  rw [← Finset.sum_mul, centered_sum s w x hW, zero_mul]

theorem mean_constant (s : Finset ι) (w : ι → ℝ) (hW : mass s w ≠ 0) (c : ℝ) :
    mean s w (fun _ => c) = c := by
  unfold mean mass at *
  rw [← Finset.sum_mul]
  field_simp [hW]

theorem energy_nonneg (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ energy s w x := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg (x i))

/-- Exact conditional error: target may be any coarse value, not just one. -/
theorem fiber_error_decomposition (s : Finset ι) (w x : ι → ℝ)
    (hW : mass s w ≠ 0) (target : ℝ) :
    energy s w (fun i => x i - target) =
      energy s w (fun i => x i - mean s w x) +
      mass s w * (mean s w x - target) ^ 2 := by
  have h := RiemannResearch.RH.CombinedAudited.weighted_pythagorean s w
    (fun i => x i - mean s w x) (fun _ => mean s w x - target)
    (centered_cross s w x hW (mean s w x - target))
  simpa only [sub_add_sub_cancel, ← Finset.sum_mul, energy, mass] using h

/-- Summing the true fiber identity keeps all within-fiber and coarse errors. -/
theorem total_error_decomposition (t : Finset κ) (s : κ → Finset ι)
    (w x : ι → ℝ) (target : κ → ℝ)
    (hW : ∀ r ∈ t, mass (s r) w ≠ 0) :
    (∑ r ∈ t, energy (s r) w (fun i => x i - target r)) =
      (∑ r ∈ t, energy (s r) w (fun i => x i - mean (s r) w x)) +
      ∑ r ∈ t, mass (s r) w * (mean (s r) w x - target r) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact fiber_error_decomposition (s r) w x (hW r hr) (target r)

theorem mean_minimizes (s : Finset ι) (w x : ι → ℝ)
    (hW : 0 < mass s w) (target : ℝ) :
    energy s w (fun i => x i - mean s w x) ≤
      energy s w (fun i => x i - target) := by
  rw [fiber_error_decomposition s w x (ne_of_gt hW) target]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hW) (sq_nonneg _))

theorem mean_unique_minimizer (s : Finset ι) (w x : ι → ℝ)
    (hW : 0 < mass s w) (target : ℝ) :
    energy s w (fun i => x i - target) =
      energy s w (fun i => x i - mean s w x) ↔ target = mean s w x := by
  rw [fiber_error_decomposition s w x (ne_of_gt hW) target]
  constructor
  · intro h
    have hz : mass s w * (mean s w x - target) ^ 2 = 0 := by linarith
    have hs : (mean s w x - target) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt hW)
    nlinarith [sq_nonneg (mean s w x - target)]
  · intro h
    simp [h]

/-- The complete signed mixed term for a correction along an actual vector. -/
theorem correction_expansion (s : Finset ι) (w e g : ι → ℝ) (α : ℝ) :
    energy s w (fun i => e i - α * g i) =
      energy s w e - 2 * α * pairing s w e g + α ^ 2 * energy s w g := by
  unfold energy pairing
  calc
    (∑ i ∈ s, w i * (e i - α * g i) ^ 2) =
        ∑ i ∈ s, (w i * e i ^ 2 - 2 * α * (w i * e i * g i) +
          α ^ 2 * (w i * g i ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]

/-- Exact optimal partial correction, including its nonnegative excess. -/
theorem partial_correction_square (s : Finset ι) (w e g : ι → ℝ)
    (hg : energy s w g ≠ 0) (α : ℝ) :
    energy s w (fun i => e i - α * g i) =
      energy s w e - pairing s w e g ^ 2 / energy s w g +
      energy s w g * (α - pairing s w e g / energy s w g) ^ 2 := by
  rw [correction_expansion]
  field_simp [hg]
  <;> ring

/-- Exact rank-one gain for unrestricted full-error optimization. -/
theorem optimal_partial_correction (s : Finset ι) (w e g : ι → ℝ)
    (hg : energy s w g ≠ 0) :
    energy s w (fun i => e i - (pairing s w e g / energy s w g) * g i) =
      energy s w e - pairing s w e g ^ 2 / energy s w g := by
  rw [partial_correction_square s w e g hg]
  simp

theorem partial_correction_minimizes (s : Finset ι) (w e g : ι → ℝ)
    (hg : 0 < energy s w g) (α : ℝ) :
    energy s w (fun i => e i - (pairing s w e g / energy s w g) * g i) ≤
      energy s w (fun i => e i - α * g i) := by
  rw [optimal_partial_correction s w e g (ne_of_gt hg),
    partial_correction_square s w e g (ne_of_gt hg)]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hg) (sq_nonneg _))

/-- Orthogonal new directions give exactly zero gain, not a free improvement. -/
theorem zero_pairing_no_gain (s : Finset ι) (w e g : ι → ℝ)
    (he : pairing s w e g = 0) (α : ℝ) :
    energy s w (fun i => e i - α * g i) = energy s w e + α ^ 2 * energy s w g := by
  rw [correction_expansion, he]
  ring

end RiemannResearch.LinearAlgebra.WeightedFiniteProjection


/-!
# Pairwise formula for the exact weighted projection defect

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 7, 2026,
Section 10, equation `eq:crt-fiber-variance`. This proves the complete
double-sum expression for each finite weighted fiber. It does not assert
that the infinite arithmetic quotient weights have been constructed.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedFiniteProjection

variable {ι : Type*}

theorem pairwise_moment_identity (s : Finset ι) (w x : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
      2 * mass s w * energy s w x - 2 * (∑ i ∈ s, w i * x i) ^ 2 := by
  have inner (i : ι) :
      (∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
        (w i * x i ^ 2) * mass s w - (2 * w i * x i) * (∑ j ∈ s, w j * x j) +
          w i * energy s w x := by
    calc
      (∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
          ∑ j ∈ s, ((w i * x i ^ 2) * w j - (2 * w i * x i) * (w j * x j) +
            w i * (w j * x j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, mass, energy]
  calc
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
        ∑ i ∈ s, (mass s w * (w i * x i ^ 2) -
          (2 * (∑ j ∈ s, w j * x j)) * (w i * x i) + energy s w x * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change mass s w * energy s w x -
        (2 * (∑ j ∈ s, w j * x j)) * (∑ i ∈ s, w i * x i) +
        energy s w x * mass s w = _
      ring

/-- Conditional variance is exactly the weighted sum of every pairwise square. -/
theorem fiber_pairwise_variance (s : Finset ι) (w x : ι → ℝ)
    (hW : mass s w ≠ 0) :
    energy s w (fun i => x i - mean s w x) =
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) / (2 * mass s w) := by
  rw [pairwise_moment_identity]
  have he := fiber_error_decomposition s w x hW 0
  simp only [sub_zero] at he
  have hm := mean_mass s w x hW
  have hsq := congrArg (fun z : ℝ => z ^ 2) hm
  have he' := congrArg (fun z : ℝ => mass s w * z) he
  apply (eq_div_iff (mul_ne_zero (by norm_num) hW)).mpr
  nlinarith [hsq, he']

/-- Nonnegative arithmetic weights make the actual projection defect nonnegative. -/
theorem fiber_defect_nonneg (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : mass s w ≠ 0) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) / (2 * mass s w) := by
  rw [← fiber_pairwise_variance s w x hW]
  exact energy_nonneg s w _ hw

/-- Strictly positive weights identify the nullspace of the actual energy. -/
theorem energy_eq_zero_iff (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    energy s w x = 0 ↔ ∀ i ∈ s, x i = 0 := by
  constructor
  · intro h i hi
    have hle : w i * x i ^ 2 ≤ energy s w x :=
      Finset.single_le_sum (fun j hj => mul_nonneg (le_of_lt (hw j hj)) (sq_nonneg _)) hi
    have hz : w i * x i ^ 2 = 0 := by
      have hn := mul_nonneg (le_of_lt (hw i hi)) (sq_nonneg (x i))
      rw [h] at hle
      exact le_antisymm hle hn
    have hs : x i ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i hi))
    nlinarith [sq_nonneg (x i)]
  · intro h
    unfold energy
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i hi]
    ring

/-- The defect vanishes exactly on vectors constant on the weighted fiber. -/
theorem fiber_defect_eq_zero_iff (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hW : mass s w ≠ 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) / (2 * mass s w) = 0 ↔
      ∀ i ∈ s, x i = mean s w x := by
  rw [← fiber_pairwise_variance s w x hW, energy_eq_zero_iff s w _ hw]
  simp only [sub_eq_zero]

end RiemannResearch.LinearAlgebra.WeightedFiniteProjection

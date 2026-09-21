import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Infinite orthogonal affine minimum

Source: continuation of the user-provided Pareto capacity argument
(2026-09-21). This module supplies its general real-Hilbert-space geometry.
The series converges in the Hilbert norm; absolute summability of vector
norms is not assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrthogonalAffineSeries

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Orthogonal vectors are summable exactly when their squared norms are. -/
theorem summable_iff_sq_norm_summable (v : ι → H)
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0)) :
    Summable v ↔ Summable (fun i => ‖v i‖ ^ 2) := by
  let V (i : ι) : Submodule ℝ H := Submodule.span ℝ {v i}
  have hV : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    change inner ℝ (x : H) (y : H) = 0
    rw [← ha, ← hb, real_inner_smul_left, inner_smul_right, ho hij]
    simp
  let f (i : ι) : V i := ⟨v i, Submodule.subset_span (Set.mem_singleton _)⟩
  exact hV.summable_iff_norm_sq_summable f

def reciprocalEnergyMass (v : ι → H) : ℝ := ∑' i, (‖v i‖ ^ 2)⁻¹

def reciprocalEnergyVector (v : ι → H) : H :=
  ∑' i, (‖v i‖ ^ 2)⁻¹ • v i

def affineMinimum (v : ι → H) : H :=
  (reciprocalEnergyMass v)⁻¹ • reciprocalEnergyVector v

variable {v : ι → H}

/-- Square summability constructs the actual infinite Hilbert vector. -/
theorem reciprocalEnergy_summable
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) :
    Summable (fun i => (‖v i‖ ^ 2)⁻¹ • v i) := by
  apply (summable_iff_sq_norm_summable _ ?_).2
  · convert hs using 1
    ext i
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hi : ‖v i‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv i))
    field_simp
  · intro i j hij
    simp [real_inner_smul_left, inner_smul_right, ho hij]

/-- Every original vector has unit pairing with the unnormalized series. -/
theorem reciprocalEnergyVector_inner
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) (i : ι) :
    inner ℝ (reciprocalEnergyVector v) (v i) = 1 := by
  classical
  rw [real_inner_comm]
  change (innerSL ℝ (v i)) (∑' j, (‖v j‖ ^ 2)⁻¹ • v j) = 1
  rw [ContinuousLinearMap.map_tsum _ (reciprocalEnergy_summable ho hv hs)]
  change (∑' j, inner ℝ (v i) ((‖v j‖ ^ 2)⁻¹ • v j)) = 1
  rw [tsum_eq_single i]
  · rw [inner_smul_right, real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv i)))
  · intro j hji
    simp [inner_smul_right, ho (Ne.symm hji)]

/-- The squared norm equals the complete reciprocal-energy mass. -/
theorem reciprocalEnergyVector_norm_sq
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) :
    ‖reciprocalEnergyVector v‖ ^ 2 = reciprocalEnergyMass v := by
  rw [← real_inner_self_eq_norm_sq]
  change (innerSL ℝ (reciprocalEnergyVector v))
    (∑' i, (‖v i‖ ^ 2)⁻¹ • v i) = _
  rw [ContinuousLinearMap.map_tsum _ (reciprocalEnergy_summable ho hv hs)]
  change (∑' i, inner ℝ (reciprocalEnergyVector v)
    ((‖v i‖ ^ 2)⁻¹ • v i)) = _
  simp only [inner_smul_right, reciprocalEnergyVector_inner ho hv hs,
    mul_one, reciprocalEnergyMass]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem reciprocalEnergyMass_pos [Nonempty ι]
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) :
    0 < reciprocalEnergyMass v := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact lt_of_lt_of_le (inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr (hv i))))
    (hs.le_tsum i (fun j _ => inv_nonneg.mpr (sq_nonneg _)))

theorem affineMinimum_norm_sq
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹))
    (hM : reciprocalEnergyMass v ≠ 0) :
    ‖affineMinimum v‖ ^ 2 = (reciprocalEnergyMass v)⁻¹ := by
  rw [affineMinimum, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    reciprocalEnergyVector_norm_sq ho hv hs]
  field_simp

theorem affineMinimum_inner
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) (i : ι) :
    inner ℝ (affineMinimum v) (v i) = (reciprocalEnergyMass v)⁻¹ := by
  rw [affineMinimum, real_inner_smul_left,
    reciprocalEnergyVector_inner ho hv hs, mul_one]

/-- A convergent signed vector series automatically has summable scalar
coefficients; the scalar total is its pairing with the reciprocal vector. -/
theorem coefficient_hasSum
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹))
    {a : ι → ℝ} {z : H} (hz : HasSum (fun i => a i • v i) z) :
    HasSum a (inner ℝ (reciprocalEnergyVector v) z) := by
  have h := (innerSL ℝ (reciprocalEnergyVector v)).hasSum hz
  change HasSum (fun i => inner ℝ (reciprocalEnergyVector v) (a i • v i))
    (inner ℝ (reciprocalEnergyVector v) z) at h
  simpa only [inner_smul_right, reciprocalEnergyVector_inner ho hv hs, mul_one] using h

/-- Exact infinite-family energy completion, retaining arbitrary signed weights. -/
theorem affine_energy_completion
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹))
    (hM : reciprocalEnergyMass v ≠ 0)
    {a : ι → ℝ} {z : H} (hz : HasSum (fun i => a i • v i) z)
    (ha : ∑' i, a i = 1) :
    ‖z‖ ^ 2 = (reciprocalEnergyMass v)⁻¹ + ‖z - affineMinimum v‖ ^ 2 := by
  have hpair : inner ℝ (reciprocalEnergyVector v) z = 1 := by
    rw [← (coefficient_hasSum ho hv hs hz).tsum_eq, ha]
  have hright : inner ℝ (affineMinimum v) z = (reciprocalEnergyMass v)⁻¹ := by
    rw [affineMinimum, real_inner_smul_left, hpair, mul_one]
  have hleft : inner ℝ z (affineMinimum v) = (reciprocalEnergyMass v)⁻¹ := by
    rw [real_inner_comm]; exact hright
  have hdiff : ‖z - affineMinimum v‖ ^ 2 =
      ‖z‖ ^ 2 - (reciprocalEnergyMass v)⁻¹ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hleft, hright, affineMinimum_norm_sq ho hv hs hM]
    ring
  rw [hdiff]
  ring

theorem affine_energy_eq_iff
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹))
    (hM : reciprocalEnergyMass v ≠ 0)
    {a : ι → ℝ} {z : H} (hz : HasSum (fun i => a i • v i) z)
    (ha : ∑' i, a i = 1) :
    ‖z‖ ^ 2 = (reciprocalEnergyMass v)⁻¹ ↔ z = affineMinimum v := by
  rw [affine_energy_completion ho hv hs hM hz ha]
  constructor
  · intro h
    have hn : ‖z - affineMinimum v‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro h
    rw [h, sub_self, norm_zero]
    ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The minimizing series has total coefficient exactly one. -/
theorem affineMinimum_coefficients_hasSum
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹))
    (hM : reciprocalEnergyMass v ≠ 0) :
    HasSum (fun i => (reciprocalEnergyMass v)⁻¹ * (‖v i‖ ^ 2)⁻¹) 1 := by
  have h := hs.hasSum.mul_left (reciprocalEnergyMass v)⁻¹
  change HasSum _ ((reciprocalEnergyMass v)⁻¹ * reciprocalEnergyMass v) at h
  simpa only [inv_mul_cancel₀ hM] using h

/-- The normalized inverse-energy coefficients attain the actual Hilbert vector. -/
theorem affineMinimum_hasSum
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0)
    (hs : Summable (fun i => (‖v i‖ ^ 2)⁻¹)) :
    HasSum (fun i => ((reciprocalEnergyMass v)⁻¹ * (‖v i‖ ^ 2)⁻¹) • v i)
      (affineMinimum v) := by
  have h := (reciprocalEnergy_summable ho hv hs).hasSum.const_smul
    (reciprocalEnergyMass v)⁻¹
  simpa only [smul_smul, affineMinimum, reciprocalEnergyVector] using h

end RiemannResearch.Analysis.OrthogonalAffineSeries

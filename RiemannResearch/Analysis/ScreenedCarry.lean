/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionSourceImprovement
import RiemannResearch.Analysis.ProjectionCompressionDefect
import RiemannResearch.LinearAlgebra.TwoChannelCancellation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Screened carry identities for the actual orthogonal projection

Source: Christian Noack's CRT-carry report, *CRT Carries and Squarefree
Residual Exhaustion*, 19 October 2026, Sections 2 and 5.  This module proves
the Hilbert-space algebra of its screened carries.  The arithmetic module
supplies the actual floor-defined carry decomposition; no asymptotic error
exhaustion claim is made here.

The screening operator below is literally `I - V.starProjection`, rather
than an unspecified linear map.  Both old prime directions belong to `V`.
Consequently arbitrary changes to their coefficients disappear after
screening, including CRT representative changes.
-/

noncomputable section

namespace RiemannResearch.Analysis.ScreenedCarry

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (V : Submodule ℝ H) [V.HasOrthogonalProjection]

/-- Actual orthogonal screening, `R_V = I - P_V`. -/
def screen : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - V.starProjection

@[simp] theorem screen_apply (x : H) : screen V x = x - V.starProjection x := rfl

theorem screen_of_mem {x : H} (hx : x ∈ V) : screen V x = 0 := by
  rw [screen_apply, Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

theorem screen_eq_zero_iff (x : H) : screen V x = 0 ↔ x ∈ V := by
  rw [screen_apply, sub_eq_zero]
  constructor
  · intro h
    exact Submodule.starProjection_eq_self_iff.mp h.symm
  · intro h
    exact (Submodule.starProjection_eq_self_iff.mpr h).symm

theorem screen_add_of_mem (x : H) {v : H} (hv : v ∈ V) :
    screen V (x + v) = screen V x := by
  rw [map_add, screen_of_mem V hv, add_zero]

theorem screen_sub_of_mem (x : H) {v : H} (hv : v ∈ V) :
    screen V (x - v) = screen V x := by
  rw [map_sub, screen_of_mem V hv, sub_zero]

/-- The real synthesis identity supplied by a CRT floor carry. -/
def carry (a b : ℝ) (x y z : H) : H := a • x + b • y - z

variable (a b a' b' : ℝ) (x y z : H)

/-- The old-space projection absorbs both prime terms exactly. -/
theorem project_carry (hx : x ∈ V) (hy : y ∈ V) :
    V.starProjection (carry a b x y z) = a • x + b • y - V.starProjection z := by
  rw [carry, map_sub, map_add, map_smul, map_smul,
    Submodule.starProjection_eq_self_iff.mpr hx,
    Submodule.starProjection_eq_self_iff.mpr hy]

theorem screen_carry (hx : x ∈ V) (hy : y ∈ V) :
    screen V (carry a b x y z) = -screen V z := by
  rw [carry, map_sub, map_add, map_smul, map_smul,
    screen_of_mem V hx, screen_of_mem V hy]
  simp

/-- A formulation accepting an already proved carry identity. -/
theorem screen_of_carry_eq (κ : H) (hκ : κ = a • x + b • y - z)
    (hx : x ∈ V) (hy : y ∈ V) : screen V κ = -screen V z := by
  rw [hκ]
  exact screen_carry V a b x y z hx hy

/-- Any two coefficient choices give the same screened carry. -/
theorem screen_carry_coefficients_eq (hx : x ∈ V) (hy : y ∈ V) :
    screen V (carry a b x y z) = screen V (carry a' b' x y z) := by
  rw [screen_carry V a b x y z hx hy,
    screen_carry V a' b' x y z hx hy]

/-- Every old-space gauge shift leaves the actual screened vector unchanged. -/
theorem screen_representative_shift (κ : H) (u v : ℝ)
    (hx : x ∈ V) (hy : y ∈ V) :
    screen V (κ + u • x + v • y) = screen V κ := by
  rw [map_add, map_add, map_smul, map_smul,
    screen_of_mem V hx, screen_of_mem V hy]
  simp

theorem norm_screen_carry_eq (hx : x ∈ V) (hy : y ∈ V) :
    ‖screen V (carry a b x y z)‖ = ‖screen V z‖ := by
  rw [screen_carry V a b x y z hx hy, norm_neg]

theorem norm_screen_carry_le (hx : x ∈ V) (hy : y ∈ V) :
    ‖screen V (carry a b x y z)‖ ≤ ‖z‖ := by
  rw [norm_screen_carry_eq V a b x y z hx hy, screen_apply]
  exact ProjectionCompression.defect_norm_le V z

theorem screen_carry_eq_zero_iff (hx : x ∈ V) (hy : y ∈ V) :
    screen V (carry a b x y z) = 0 ↔ z ∈ V := by
  rw [screen_carry V a b x y z hx hy, neg_eq_zero,
    screen_eq_zero_iff]

/-- A carry is old precisely when its composite column is old. -/
theorem carry_mem_iff (hx : x ∈ V) (hy : y ∈ V) :
    carry a b x y z ∈ V ↔ z ∈ V := by
  exact (screen_eq_zero_iff V (carry a b x y z)).symm.trans
    (screen_carry_eq_zero_iff V a b x y z hx hy)

/-- Pythagoras identifies exactly the energy removed by screening. -/
theorem carry_energy_pythagoras (hx : x ∈ V) (hy : y ∈ V) :
    ‖carry a b x y z‖ ^ 2 =
      ‖V.starProjection (carry a b x y z)‖ ^ 2 + ‖screen V z‖ ^ 2 := by
  have h := ProjectionCompression.projection_pythagoras V (carry a b x y z)
  change ‖carry a b x y z‖ ^ 2 =
    ‖V.starProjection (carry a b x y z)‖ ^ 2 +
      ‖screen V (carry a b x y z)‖ ^ 2 at h
  simpa only [norm_screen_carry_eq V a b x y z hx hy] using h

/-- Screened Gram entries depend only on the composite columns. -/
theorem screened_gram_eq (hx : x ∈ V) (hy : y ∈ V)
    (c d : ℝ) (x' y' z' : H) (hx' : x' ∈ V) (hy' : y' ∈ V) :
    inner ℝ (screen V (carry a b x y z))
      (screen V (carry c d x' y' z')) =
      inner ℝ (screen V z) (screen V z') := by
  rw [screen_carry V a b x y z hx hy,
    screen_carry V c d x' y' z' hx' hy']
  rw [inner_neg_left, inner_neg_right, neg_neg]

theorem screened_target_inner_eq (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    inner ℝ (screen V t) (screen V (carry a b x y z)) =
      -inner ℝ (screen V t) (screen V z) := by
  rw [screen_carry V a b x y z hx hy, inner_neg_right]

/-- Correlations of the actual target residual with the raw carry retain
the signed composite correlation exactly. -/
theorem residual_inner_carry (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    inner ℝ (screen V t) (carry a b x y z) =
      -inner ℝ (screen V t) z := by
  have hκ := ProjectionSourceImprovement.residual_inner V t (carry a b x y z)
  have hz := ProjectionSourceImprovement.residual_inner V t z
  change inner ℝ (screen V t) (screen V (carry a b x y z)) =
    inner ℝ (screen V t) (carry a b x y z) at hκ
  change inner ℝ (screen V t) (screen V z) =
    inner ℝ (screen V t) z at hz
  rw [← hκ, screened_target_inner_eq V a b x y z t hx hy, hz]

theorem residual_inner_coefficients_eq (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    inner ℝ (screen V t) (carry a b x y z) =
      inner ℝ (screen V t) (carry a' b' x y z) := by
  rw [residual_inner_carry V a b x y z t hx hy,
    residual_inner_carry V a' b' x y z t hx hy]

theorem carry_mem_sup (hx : x ∈ V) (hy : y ∈ V) :
    carry a b x y z ∈ V ⊔ Submodule.span ℝ {z} := by
  have hxy : a • x + b • y ∈ V :=
    V.add_mem (V.smul_mem a hx) (V.smul_mem b hy)
  have hV : V ≤ V ⊔ Submodule.span ℝ {z} := le_sup_left
  have hZ : Submodule.span ℝ {z} ≤ V ⊔ Submodule.span ℝ {z} := le_sup_right
  exact (V ⊔ Submodule.span ℝ {z}).sub_mem
    (hV hxy) (hZ (Submodule.subset_span (by simp)))

/-- Adjoining a carry is exactly the same real subspace enlargement as
adjoining its composite atom. -/
theorem sup_span_carry_eq (hx : x ∈ V) (hy : y ∈ V) :
    V ⊔ Submodule.span ℝ {carry a b x y z} =
      V ⊔ Submodule.span ℝ {z} := by
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro w hw
    have hw' : w = carry a b x y z := Set.mem_singleton_iff.mp hw
    subst w
    exact carry_mem_sup V a b x y z hx hy
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro w hw
    have hw' : w = z := Set.mem_singleton_iff.mp hw
    subst w
    let W := V ⊔ Submodule.span ℝ {carry a b x y z}
    have hV : V ≤ W := le_sup_left
    have hK : Submodule.span ℝ {carry a b x y z} ≤ W := le_sup_right
    have hxy : a • x + b • y ∈ W :=
      hV (V.add_mem (V.smul_mem a hx) (V.smul_mem b hy))
    have hκ : carry a b x y z ∈ W :=
      hK (Submodule.subset_span (by simp))
    have h := W.sub_mem hxy hκ
    have he : a • x + b • y - carry a b x y z = z := by
      unfold carry
      abel
    rw [he] at h
    exact h

theorem sup_span_carry_coefficients_eq (hx : x ∈ V) (hy : y ∈ V) :
    V ⊔ Submodule.span ℝ {carry a b x y z} =
      V ⊔ Submodule.span ℝ {carry a' b' x y z} := by
  rw [sup_span_carry_eq V a b x y z hx hy,
    sup_span_carry_eq V a' b' x y z hx hy]

/-- Complete signed raw Gram identity; no mixed term is discarded. -/
theorem carry_norm_sq :
    ‖carry a b x y z‖ ^ 2 =
      a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2 + ‖z‖ ^ 2 +
        2 * a * b * inner ℝ x y -
        2 * a * inner ℝ x z - 2 * b * inner ℝ y z := by
  rw [carry, sub_eq_add_neg,
    RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq,
    RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq]
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Optimal scalar refit after all old coefficients have been refitted. -/
def refit (t z : H) : H :=
  V.starProjection t +
    (inner ℝ (screen V t) z / ‖screen V z‖ ^ 2) • screen V z

/-- Replacing a composite column by its carry gives the identical optimal
refitted vector, including when the innovation vanishes. -/
theorem refit_carry_eq (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    refit V t (carry a b x y z) = refit V t z := by
  unfold refit
  rw [residual_inner_carry V a b x y z t hx hy,
    screen_carry V a b x y z hx hy, norm_neg]
  simp only [neg_div, neg_smul, smul_neg, neg_neg]

theorem refit_coefficients_eq (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    refit V t (carry a b x y z) = refit V t (carry a' b' x y z) := by
  rw [refit_carry_eq V a b x y z t hx hy,
    refit_carry_eq V a' b' x y z t hx hy]

/-- The exact innovation Rayleigh quotient is gauge invariant. -/
theorem gain_quotient_carry_eq (t : H) (hx : x ∈ V) (hy : y ∈ V) :
    (inner ℝ (screen V t) (carry a b x y z)) ^ 2 /
        ‖screen V (carry a b x y z)‖ ^ 2 =
      (inner ℝ (screen V t) z) ^ 2 / ‖screen V z‖ ^ 2 := by
  rw [residual_inner_carry V a b x y z t hx hy,
    screen_carry V a b x y z hx hy, norm_neg]
  simp

/-- Exact actual-Q refit gain, with the nonzero composite innovation
displayed as an explicit hypothesis. -/
theorem optimal_refit_gain_carry (t : H) (hx : x ∈ V) (hy : y ∈ V)
    (hz : screen V z ≠ 0) :
    ‖screen V t‖ ^ 2 - ‖t - refit V t (carry a b x y z)‖ ^ 2 =
      (inner ℝ (screen V t) z) ^ 2 / ‖screen V z‖ ^ 2 := by
  rw [refit_carry_eq V a b x y z t hx hy]
  simpa only [refit, screen_apply, ProjectionSourceImprovement.residual] using
    ProjectionSourceImprovement.optimal_refit_gain V t z hz

/- Append inside namespace RiemannResearch.Analysis.ScreenedCarry, before its
closing `end`.  Uses only the imports and declarations of ScreenedCarry.lean. -/

/-- The scalar refit is literally the enlarged-space orthogonal projection.
The formula remains valid when the innovation vanishes (Lean's `0 / 0 = 0`). -/
theorem refit_eq_projection (t z : H)
    [(V ⊔ Submodule.span ℝ {z}).HasOrthogonalProjection] :
    refit V t z = (V ⊔ Submodule.span ℝ {z}).starProjection t := by
  let W := V ⊔ Submodule.span ℝ {z}
  let c : ℝ := inner ℝ (screen V t) z / ‖screen V z‖ ^ 2
  have hVW : V ≤ W := le_sup_left
  have hZW : Submodule.span ℝ {z} ≤ W := le_sup_right
  have hzW : z ∈ W := hZW (Submodule.subset_span (by simp))
  have hmem : refit V t z ∈ W := by
    change V.starProjection t + c • (z - V.starProjection z) ∈ W
    exact W.add_mem (hVW (Submodule.starProjection_apply_mem V t))
      (W.smul_mem c (W.sub_mem hzW
        (hVW (Submodule.starProjection_apply_mem V z))))
  have he : t - refit V t z = screen V t - c • screen V z := by
    change t - (V.starProjection t + c • screen V z) =
      (t - V.starProjection t) - c • screen V z
    abel
  have hoV : ∀ v ∈ V, inner ℝ (t - refit V t z) v = 0 := by
    intro v hv
    have ht : inner ℝ (screen V t) v = 0 :=
      Submodule.starProjection_inner_eq_zero t v hv
    have hz : inner ℝ (screen V z) v = 0 :=
      Submodule.starProjection_inner_eq_zero z v hv
    rw [he, inner_sub_left, real_inner_smul_left, ht, hz, mul_zero, sub_self]
  have hoz : inner ℝ (t - refit V t z) z = 0 := by
    by_cases hz : screen V z = 0
    · exact hoV z ((screen_eq_zero_iff V z).mp hz)
    · have hden : ‖screen V z‖ ^ 2 ≠ 0 :=
        pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
      have hself : inner ℝ (screen V z) z = ‖screen V z‖ ^ 2 := by
        have h := ProjectionSourceImprovement.residual_inner V z z
        change inner ℝ (screen V z) (screen V z) = inner ℝ (screen V z) z at h
        rw [real_inner_self_eq_norm_sq] at h
        exact h.symm
      rw [he, inner_sub_left, real_inner_smul_left, hself]
      dsimp only [c]
      rw [div_mul_cancel₀ _ hden, sub_self]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  change w ∈ V ⊔ Submodule.span ℝ {z} at hw
  obtain ⟨v, hv, u, hu, hsum⟩ := Submodule.mem_sup.mp hw
  obtain ⟨r, hru⟩ := Submodule.mem_span_singleton.mp hu
  rw [← hsum, inner_add_right, hoV v hv, ← hru,
    inner_smul_right, hoz, mul_zero, add_zero]

/-- Exact distance improvement of the actual enlarged orthogonal projection. -/
theorem projection_gain (t z : H)
    [(V ⊔ Submodule.span ℝ {z}).HasOrthogonalProjection]
    (hz : screen V z ≠ 0) :
    ‖screen V t‖ ^ 2 -
        ‖t - (V ⊔ Submodule.span ℝ {z}).starProjection t‖ ^ 2 =
      (inner ℝ (screen V t) z) ^ 2 / ‖screen V z‖ ^ 2 := by
  rw [← refit_eq_projection V t z]
  simpa only [refit, screen_apply, ProjectionSourceImprovement.residual] using
    ProjectionSourceImprovement.optimal_refit_gain V t z hz

/-- The actual projection obtained by adjoining the carry is identical to
the actual projection obtained by adjoining its composite atom. -/
theorem carry_projection_eq_composite (a b : ℝ) (x y z t : H)
    (hx : x ∈ V) (hy : y ∈ V)
    [(V ⊔ Submodule.span ℝ {carry a b x y z}).HasOrthogonalProjection]
    [(V ⊔ Submodule.span ℝ {z}).HasOrthogonalProjection] :
    (V ⊔ Submodule.span ℝ {carry a b x y z}).starProjection t =
      (V ⊔ Submodule.span ℝ {z}).starProjection t := by
  rw [← refit_eq_projection V t (carry a b x y z),
    refit_carry_eq V a b x y z t hx hy, refit_eq_projection V t z]

/-- Every coefficient choice gives the identical enlarged-space projection. -/
theorem carry_projection_coefficients_eq (a b a' b' : ℝ) (x y z t : H)
    (hx : x ∈ V) (hy : y ∈ V)
    [(V ⊔ Submodule.span ℝ {carry a b x y z}).HasOrthogonalProjection]
    [(V ⊔ Submodule.span ℝ {carry a' b' x y z}).HasOrthogonalProjection] :
    (V ⊔ Submodule.span ℝ {carry a b x y z}).starProjection t =
      (V ⊔ Submodule.span ℝ {carry a' b' x y z}).starProjection t := by
  rw [← refit_eq_projection V t (carry a b x y z),
    ← refit_eq_projection V t (carry a' b' x y z),
    refit_coefficients_eq V a b a' b' x y z t hx hy]

/-- The report's one-direction gain formula, now for the actual projection
onto the space enlarged by the carry, rather than only a trial vector. -/
theorem carry_projection_gain (a b : ℝ) (x y z t : H)
    (hx : x ∈ V) (hy : y ∈ V)
    [(V ⊔ Submodule.span ℝ {carry a b x y z}).HasOrthogonalProjection]
    (hz : screen V z ≠ 0) :
    ‖screen V t‖ ^ 2 -
        ‖t - (V ⊔ Submodule.span ℝ {carry a b x y z}).starProjection t‖ ^ 2 =
      (inner ℝ (screen V t) (carry a b x y z)) ^ 2 /
        ‖screen V (carry a b x y z)‖ ^ 2 := by
  apply projection_gain V t (carry a b x y z)
  rw [screen_carry V a b x y z hx hy]
  exact neg_ne_zero.mpr hz

/-- The same actual enlarged-space gain expressed using the composite column. -/
theorem carry_projection_gain_composite (a b : ℝ) (x y z t : H)
    (hx : x ∈ V) (hy : y ∈ V)
    [(V ⊔ Submodule.span ℝ {carry a b x y z}).HasOrthogonalProjection]
    (hz : screen V z ≠ 0) :
    ‖screen V t‖ ^ 2 -
        ‖t - (V ⊔ Submodule.span ℝ {carry a b x y z}).starProjection t‖ ^ 2 =
      (inner ℝ (screen V t) z) ^ 2 / ‖screen V z‖ ^ 2 := by
  rw [carry_projection_gain V a b x y z t hx hy hz,
    gain_quotient_carry_eq V a b x y z t hx hy]


/-- Every finite signed block retains exactly the same screened synthesis,
up to the common minus sign on composite columns. -/
theorem screen_sum_carries {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (x y z : ι → H)
    (hx : ∀ i, x i ∈ V) (hy : ∀ i, y i ∈ V) :
    screen V (∑ i, c i • carry (a i) (b i) (x i) (y i) (z i)) =
      -screen V (∑ i, c i • z i) := by
  have hi : ∀ i, screen V (carry (a i) (b i) (x i) (y i) (z i)) =
      -screen V (z i) := fun i =>
    screen_carry V (a i) (b i) (x i) (y i) (z i) (hx i) (hy i)
  simp only [map_sum, map_smul, hi, smul_neg, Finset.sum_neg_distrib]

/-- The complete energy of a signed screened block is representative free. -/
theorem norm_screen_sum_carries {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (x y z : ι → H)
    (hx : ∀ i, x i ∈ V) (hy : ∀ i, y i ∈ V) :
    ‖screen V (∑ i, c i • carry (a i) (b i) (x i) (y i) (z i))‖ ^ 2 =
      ‖screen V (∑ i, c i • z i)‖ ^ 2 := by
  rw [screen_sum_carries V a b c x y z hx hy, norm_neg]

end RiemannResearch.Analysis.ScreenedCarry

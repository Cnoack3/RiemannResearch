import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact one-direction Schur repair in a real inner product space

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 6. These identities retain the full old/new and within-packet
mixed terms. No global boundedness assertion is included.
-/

namespace RiemannResearch.LinearAlgebra
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Remove the component along the free direction using the full pairing. -/
def schurRemove (d x : H) : H := x - (inner ℝ x d / ‖d‖ ^ 2) • d

/-- Correct one constraint and then minimize along a free direction. -/
def schurRepair (F u d : H) (δ : ℝ) : H := schurRemove d (F + δ • u)

theorem norm_add_smul_sq_exact (x y : H) (a : ℝ) :
    ‖x + a • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * a * inner ℝ x y + a ^ 2 * ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq, real_inner_comm y x]
  ring

theorem schurRemove_inner (x d : H) (hd : d ≠ 0) :
    inner ℝ (schurRemove d x) d = 0 := by
  have hn : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [schurRemove, inner_sub_left, inner_smul_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Exact complete-square identity, including every value of the free scalar. -/
theorem schur_line_complete_square (x d : H) (t : ℝ) (hd : d ≠ 0) :
    ‖x + t • d‖ ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ x d) ^ 2 / ‖d‖ ^ 2 +
        ‖d‖ ^ 2 * (t + inner ℝ x d / ‖d‖ ^ 2) ^ 2 := by
  rw [norm_add_smul_sq_exact]
  have hn : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  field_simp
  ring

theorem schurRemove_norm_sq (x d : H) (hd : d ≠ 0) :
    ‖schurRemove d x‖ ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ x d) ^ 2 / ‖d‖ ^ 2 := by
  change ‖x - (inner ℝ x d / ‖d‖ ^ 2) • d‖ ^ 2 = _
  rw [sub_eq_add_neg, ← neg_smul]
  rw [schur_line_complete_square x d _ hd]
  simp

theorem schurRemove_minimizes (x d : H) (hd : d ≠ 0) (t : ℝ) :
    ‖schurRemove d x‖ ^ 2 ≤ ‖x + t • d‖ ^ 2 := by
  rw [schurRemove_norm_sq x d hd, schur_line_complete_square x d t hd]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The exact energy update of the mean-preserving packet recursion. -/
theorem schurRepair_norm_sq (F u d : H) (δ : ℝ) (hd : d ≠ 0) :
    ‖schurRepair F u d δ‖ ^ 2 =
      ‖F‖ ^ 2 + 2 * δ * inner ℝ F u + δ ^ 2 * ‖u‖ ^ 2 -
        (inner ℝ F d + δ * inner ℝ u d) ^ 2 / ‖d‖ ^ 2 := by
  rw [schurRepair, schurRemove_norm_sq _ _ hd, norm_add_smul_sq_exact]
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]

/-- Every continuous or algebraic linear constraint killed by both directions
is exactly preserved. This includes the Pareto mean functional. -/
theorem schurRepair_preserves_linear (F u d : H) (δ : ℝ)
    (L : H →ₗ[ℝ] ℝ) (hu : L u = 0) (hd : L d = 0) :
    L (schurRepair F u d δ) = L F := by
  simp [schurRepair, schurRemove, map_sub, map_add, map_smul, hu, hd]

theorem schurRepair_preserves_inner (F u d z : H) (δ : ℝ)
    (hu : inner ℝ u z = 0) (hd : inner ℝ d z = 0) :
    inner ℝ (schurRepair F u d δ) z = inner ℝ F z := by
  simp [schurRepair, schurRemove, inner_sub_left, inner_add_left,
    inner_smul_left, hu, hd]

/-- Exact update for every coordinate or test vector, without independence. -/
theorem schurRepair_inner (F u d z : H) (δ : ℝ) :
    inner ℝ (schurRepair F u d δ) z =
      inner ℝ F z + δ * inner ℝ u z -
        ((inner ℝ F d + δ * inner ℝ u d) / ‖d‖ ^ 2) * inner ℝ d z := by
  simp [schurRepair, schurRemove, inner_sub_left, inner_add_left, inner_smul_left]

theorem schurRepair_mem (V : Submodule ℝ H) (F u d : H) (δ : ℝ)
    (hF : F ∈ V) (hu : u ∈ V) (hd : d ∈ V) :
    schurRepair F u d δ ∈ V := by
  exact V.sub_mem (V.add_mem hF (V.smul_mem δ hu)) (V.smul_mem _ hd)

/-- Exact relation between norm and error for a mean-one vector and unit target. -/
theorem norm_sq_eq_one_add_error (F e : H)
    (he : ‖e‖ ^ 2 = 1) (hmean : inner ℝ F e = 1) :
    ‖F‖ ^ 2 = 1 + ‖F - e‖ ^ 2 := by
  have h := norm_add_smul_sq_exact F e (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg, he, hmean] at h
  linarith

/-- The exact squared energy of the future-coordinate part of a normalized
repair. Its leading Haar coefficient is one. -/
theorem normalized_repair_tail_norm_sq (u h : H) (a : ℝ)
    (hh : ‖h‖ ^ 2 = 1) (huh : a * inner ℝ u h = 1) :
    ‖a • u - h‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 - 1 := by
  have he := norm_add_smul_sq_exact (a • u) h (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_smul_left, RCLike.conj_to_real, hh] at he
  rw [huh] at he
  linarith

/-- The second equality in the report's operator-norm formula, stated as an
exact identity of actual projected Hilbert vectors. The identification with
an operator norm requires the corresponding sharpness argument separately. -/
theorem normalized_repair_schur_tail_energy (u d h : H) (a : ℝ)
    (hd : d ≠ 0) (hh : ‖h‖ ^ 2 = 1)
    (huh : a * inner ℝ u h = 1) (hhd : inner ℝ h d = 0) :
    1 + ‖schurRemove d (a • u - h)‖ ^ 2 =
      a ^ 2 * (‖u‖ ^ 2 - (inner ℝ u d) ^ 2 / ‖d‖ ^ 2) := by
  rw [schurRemove_norm_sq _ _ hd, normalized_repair_tail_norm_sq u h a hh huh]
  simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real,
    hhd, sub_zero]
  ring

end
end RiemannResearch.LinearAlgebra

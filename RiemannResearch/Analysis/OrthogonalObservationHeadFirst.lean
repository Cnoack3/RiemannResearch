/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Head-first observation gain and exact source cancellation

Source: independently developed from the user-provided innovation-space
research agenda, 29 October 2026. The concrete consumer is QCRTHeadFirstSource.
Exact norm and pairing identities retain all signed terms and full norms.
-/

namespace RiemannResearch.Analysis.OrthogonalObservationHeadFirst
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def adjustedColumn (x k : H) (c K : ℝ) : H := x - (c / K) • k

def headFirstGain (D k ell : H) (a b K cap : ℝ) : H :=
  D - (b / cap) • ell + (a / K - b / cap) • k

theorem adjusted_inner (x y k : H) (c d K : ℝ)
    (hK : K ≠ 0) (hk : ‖k‖ ^ 2 = K)
    (hx : inner ℝ x k = 0) (hy : inner ℝ k y = 0) :
    inner ℝ (adjustedColumn x k c K) (adjustedColumn y k d K) =
      inner ℝ x y + c * d / K := by
  simp only [adjustedColumn, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    hx, hy, hk]
  field_simp
  <;> ring

theorem adjusted_norm (x k : H) (c K : ℝ)
    (hK : K ≠ 0) (hk : ‖k‖ ^ 2 = K) (hx : inner ℝ x k = 0) :
    ‖adjustedColumn x k c K‖ ^ 2 = ‖x‖ ^ 2 + c ^ 2 / K := by
  have hh := adjusted_inner x x k c c K hK hk hx
    (by simpa only [real_inner_comm] using hx)
  simpa only [real_inner_self_eq_norm_sq, pow_two] using hh

theorem gain_norm (D k ell : H) (a b K cap : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hell : ‖ell‖ ^ 2 = cap - K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hDell : inner ℝ D ell = b - a) :
    ‖headFirstGain D k ell a b K cap‖ ^ 2 =
      a ^ 2 / K - (b ^ 2 / cap - ‖D‖ ^ 2) := by
  simp only [headFirstGain, norm_add_sq_real, norm_sub_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_sub_left,
    real_inner_smul_left, inner_smul_right, hDk, hellk, hDell, hk, hell]
  field_simp
  <;> ring

theorem gain_pairing (D k ell x : H) (a b K cap c : ℝ)
    (hK : K ≠ 0) (hk : ‖k‖ ^ 2 = K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hxk : inner ℝ k x = 0) (hellx : inner ℝ ell x = c) :
    inner ℝ (headFirstGain D k ell a b K cap) (adjustedColumn x k c K) =
      inner ℝ D x - a * c / K := by
  simp only [headFirstGain, adjustedColumn, inner_add_left, inner_sub_left,
    inner_sub_right, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hDk, hellk, hxk, hellx, hk]
  field_simp
  <;> ring

/-- A complete-norm cancellation estimate for each actual joint source.
It remains valid when innovation capacity is zero; only old and total
capacity need be nonzero. -/
theorem joint_source_sq_le (D k ell x : H) (a b K cap c : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hell : ‖ell‖ ^ 2 = cap - K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hDell : inner ℝ D ell = b - a)
    (hxk : inner ℝ k x = 0) (hellx : inner ℝ ell x = c) :
    (inner ℝ D x - a * c / K) ^ 2 ≤
      (a ^ 2 / K - (b ^ 2 / cap - ‖D‖ ^ 2)) *
        (‖x‖ ^ 2 + c ^ 2 / K) := by
  have hc := real_inner_mul_inner_self_le
    (headFirstGain D k ell a b K cap) (adjustedColumn x k c K)
  rw [gain_pairing D k ell x a b K cap c hK hk hDk hellk hxk hellx,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    gain_norm D k ell a b K cap hK hcap hk hell hDk hellk hDell,
    adjusted_norm x k c K hK hk
      (by simpa only [real_inner_comm] using hxk)] at hc
  nlinarith

/-- A usable signed upper bound requiring an upper bound on one adjusted
column norm, rather than a lower eigenvalue bound for the full Gram matrix. -/
theorem signed_transition_le (D k ell x : H) (a b K cap c M : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hell : ‖ell‖ ^ 2 = cap - K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hDell : inner ℝ D ell = b - a)
    (hxk : inner ℝ k x = 0) (hellx : inner ℝ ell x = c)
    (hM : 0 < M) (hbound : ‖x‖ ^ 2 + c ^ 2 / K ≤ M) :
    b ^ 2 / cap - ‖D‖ ^ 2 ≤
      a ^ 2 / K - (inner ℝ D x - a * c / K) ^ 2 / M := by
  have hnonneg : 0 ≤ a ^ 2 / K - (b ^ 2 / cap - ‖D‖ ^ 2) := by
    rw [← gain_norm D k ell a b K cap hK hcap hk hell hDk hellk hDell]
    exact sq_nonneg _
  have hsource := joint_source_sq_le D k ell x a b K cap c
    hK hcap hk hell hDk hellk hDell hxk hellx
  have hm := mul_le_mul_of_nonneg_left hbound hnonneg
  have hquot : (inner ℝ D x - a * c / K) ^ 2 / M ≤
      a ^ 2 / K - (b ^ 2 / cap - ‖D‖ ^ 2) :=
    (div_le_iff₀ hM).mpr (hsource.trans hm)
  linarith


/-- Exact rank-one Gram update for imposing the observation first. -/
theorem adjusted_gram {ι : Type*} (v : ι → H) (k : H) (c : ι → ℝ) (K : ℝ)
    (hK : K ≠ 0) (hk : ‖k‖ ^ 2 = K)
    (hv : ∀ i, inner ℝ (v i) k = 0) :
    (fun i j => inner ℝ (adjustedColumn (v i) k (c i) K)
      (adjustedColumn (v j) k (c j) K)) =
    (fun i j => inner ℝ (v i) (v j) + c i * c j / K) := by
  funext i j
  exact adjusted_inner (v i) (v j) k (c i) (c j) K hK hk (hv i)
    (by simpa only [real_inner_comm] using hv j)

end
end RiemannResearch.Analysis.OrthogonalObservationHeadFirst

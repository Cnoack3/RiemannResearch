import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Module

/-!
# Exact Abel coboundary identities

Source: user-provided argument, the September 10, 2026 two-seed quotient-norm
handoff, equations (N17)--(N23). This module formalizes the summation identity
used there. It does not prove an arithmetic orbit estimate, or assert that an
Abel operator is bounded on the entire quotient space.

The summability assumptions are stated explicitly. The finite identity keeps
the terminal boundary term, and the infinite identity retains the exact sign.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.AbelCoboundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted series underlying an Abel average. -/
noncomputable def series (r : ℝ) (v : ℕ → E) : E :=
  ∑' n : ℕ, r ^ n • v n

/-- An Abel average, meaningful under the explicitly stated summability
premises in the theorems below. -/
noncomputable def average (r : ℝ) (v : ℕ → E) : E :=
  (1 - r) • series r v

/-- Exact finite discounted telescoping, including the boundary term. -/
theorem finite_discounted (r : ℝ) (v : ℕ → E) (N : ℕ) :
    (∑ n ∈ Finset.range N, r ^ n • (v n - r • v (n + 1))) =
      v 0 - r ^ N • v N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [smul_sub, smul_smul, pow_succ]
      module

/-- Exact finite Abel coboundary formula. It also holds at `r = 0`, since
it is written without division. -/
theorem finite_coboundary (r : ℝ) (v : ℕ → E) (N : ℕ) :
    r • (∑ n ∈ Finset.range N, r ^ n • (v n - v (n + 1))) =
      v 0 - (1 - r) • (∑ n ∈ Finset.range N, r ^ n • v n) -
        r ^ N • v N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ, smul_add]
      rw [ih]
      simp only [smul_sub, smul_smul, pow_succ]
      module

/-- Splitting off the head of a summable weighted series. -/
theorem series_eq_head_add (r : ℝ) (v : ℕ → E)
    (hv : Summable (fun n : ℕ => r ^ n • v n))
    (hshift : Summable (fun n : ℕ => r ^ n • v (n + 1))) :
    series r v = v 0 + r • series r (fun n => v (n + 1)) := by
  unfold series
  rw [hv.tsum_eq_zero_add]
  simp only [pow_zero, one_smul]
  congr 1
  simp only [pow_succ', mul_smul]
  have hmap := (r • ContinuousLinearMap.id ℝ E).map_tsum hshift
  simpa only [smul_apply, ContinuousLinearMap.id_apply] using hmap.symm

/-- Summability of a difference is established before splitting the series. -/
theorem series_sub (r : ℝ) (u v : ℕ → E)
    (hu : Summable (fun n : ℕ => r ^ n • u n))
    (hv : Summable (fun n : ℕ => r ^ n • v n)) :
    series r (fun n => u n - v n) = series r u - series r v := by
  unfold series
  simpa only [smul_sub] using hu.tsum_sub hv

/-- Division-free infinite Abel coboundary telescoping. No global boundedness
assumption on the averaging operator is used. -/
theorem average_coboundary_mul (r : ℝ) (v : ℕ → E)
    (hv : Summable (fun n : ℕ => r ^ n • v n))
    (hshift : Summable (fun n : ℕ => r ^ n • v (n + 1))) :
    r • average r (fun n => v n - v (n + 1)) =
      (1 - r) • (v 0 - average r v) := by
  rw [average, series_sub r v (fun n => v (n + 1)) hv hshift]
  rw [average, series_eq_head_add r v hv hshift]
  module

/-- Infinite Abel coboundary identity with its exact coefficient and sign. -/
theorem average_coboundary (r : ℝ) (hr : r ≠ 0) (v : ℕ → E)
    (hv : Summable (fun n : ℕ => r ^ n • v n))
    (hshift : Summable (fun n : ℕ => r ^ n • v (n + 1))) :
    average r (fun n => v n - v (n + 1)) =
      ((1 - r) / r) • (v 0 - average r v) := by
  calc
    average r (fun n => v n - v (n + 1)) =
        r⁻¹ • (r • average r (fun n => v n - v (n + 1))) := by
          simp [smul_smul, hr]
    _ = r⁻¹ • ((1 - r) • (v 0 - average r v)) := by
          rw [average_coboundary_mul r v hv hshift]
    _ = ((1 - r) / r) • (v 0 - average r v) := by
          simp [smul_smul, div_eq_mul_inv, mul_comm]

/-- The operator orbit, defined recursively to make its recurrence explicit. -/
def orbit (B : E →L[ℝ] E) (z : E) : ℕ → E
  | 0 => z
  | n + 1 => B (orbit B z n)

@[simp] theorem orbit_zero (B : E →L[ℝ] E) (z : E) : orbit B z 0 = z := rfl

@[simp] theorem orbit_succ (B : E →L[ℝ] E) (z : E) (n : ℕ) :
    orbit B z (n + 1) = B (orbit B z n) := rfl

theorem orbit_sub (B : E →L[ℝ] E) (z w : E) (n : ℕ) :
    orbit B (z - w) n = orbit B z n - orbit B w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih, map_sub]

theorem orbit_apply (B : E →L[ℝ] E) (z : E) (n : ℕ) :
    orbit B (B z) n = orbit B z (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih]

/-- The identity used for the explicit seed potential in (N23). The two
summability hypotheses are precisely those needed for these orbit series. -/
theorem orbit_average_coboundary (B : E →L[ℝ] E) (r : ℝ) (hr : r ≠ 0) (z : E)
    (hz : Summable (fun n : ℕ => r ^ n • orbit B z n))
    (hBz : Summable (fun n : ℕ => r ^ n • orbit B z (n + 1))) :
    average r (orbit B (z - B z)) =
      ((1 - r) / r) • (z - average r (orbit B z)) := by
  have hpoint : orbit B (z - B z) = fun n => orbit B z n - orbit B z (n + 1) := by
    funext n
    rw [orbit_sub, orbit_apply]
  rw [hpoint]
  simpa only [orbit_zero] using average_coboundary r hr (orbit B z) hz hBz

/-- Norm control of the exact coboundary identity; no orbit bound is hidden
in this theorem. -/
theorem norm_orbit_average_coboundary_le
    (B : E →L[ℝ] E) (r : ℝ) (hr : r ≠ 0) (z : E)
    (hz : Summable (fun n : ℕ => r ^ n • orbit B z n))
    (hBz : Summable (fun n : ℕ => r ^ n • orbit B z (n + 1))) :
    ‖average r (orbit B (z - B z))‖ ≤
      |(1 - r) / r| * (‖z‖ + ‖average r (orbit B z)‖) := by
  rw [orbit_average_coboundary B r hr z hz hBz, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_sub_le z (average r (orbit B z))) (abs_nonneg _)

end RiemannResearch.Analysis.AbelCoboundary


/-! Additional seed-decomposition lemmas intended for the AbelCoboundary module.
Source: user-provided two-seed handoff, equation (N23). -/

namespace RiemannResearch.Analysis.AbelCoboundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem average_add (r : ℝ) (u v : ℕ → E)
    (hu : Summable (fun n : ℕ => r ^ n • u n))
    (hv : Summable (fun n : ℕ => r ^ n • v n)) :
    average r (fun n => u n + v n) = average r u + average r v := by
  have hs : series r (fun n => u n + v n) = series r u + series r v := by
    unfold series
    simpa only [smul_add] using hu.tsum_add hv
  rw [average, hs, smul_add]
  rfl

theorem orbit_add (B : E →L[ℝ] E) (z w : E) (n : ℕ) :
    orbit B (z + w) n = orbit B z n + orbit B w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih, map_add]

theorem orbit_smul (B : E →L[ℝ] E) (a : ℝ) (z : E) (n : ℕ) :
    orbit B (a • z) n = a • orbit B z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih, map_smul]

theorem orbit_eq_of_fixed (B : E →L[ℝ] E) (w : E) (hw : B w = w) (n : ℕ) :
    orbit B w n = w := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih, hw]

theorem summable_constant (r : ℝ) (hr : ‖r‖ < 1) (z : E) :
    Summable (fun n : ℕ => r ^ n • z) := by
  exact ((hasSum_geometric_of_norm_lt_one hr).smul_const z).summable

theorem average_constant (r : ℝ) (hr : ‖r‖ < 1) (z : E) :
    average r (fun _ => z) = z := by
  have hr1 : r ≠ 1 := by
    intro h
    simp [h] at hr
  have hne : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.symm
  have hs : series r (fun _ : ℕ => z) = (1 - r)⁻¹ • z := by
    exact ((hasSum_geometric_of_norm_lt_one hr).smul_const z).tsum_eq
  rw [average, hs, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- A fixed vector plus an exact coboundary has this exact Abel average.
The particular arithmetic seed identity is a separate application. -/
theorem orbit_average_fixed_add_coboundary
    (B : E →L[ℝ] E) (r a : ℝ) (hr : r ≠ 0) (hrnorm : ‖r‖ < 1)
    (w z : E) (hw : B w = w)
    (hz : Summable (fun n : ℕ => r ^ n • orbit B z n))
    (hBz : Summable (fun n : ℕ => r ^ n • orbit B z (n + 1))) :
    average r (orbit B (a • w + (z - B z))) =
      a • w + ((1 - r) / r) • (z - average r (orbit B z)) := by
  have hpoint : orbit B (a • w + (z - B z)) =
      fun n => a • w + (orbit B z n - orbit B z (n + 1)) := by
    funext n
    rw [orbit_add, orbit_smul, orbit_eq_of_fixed B w hw, orbit_sub, orbit_apply]
  have hcb : Summable (fun n : ℕ => r ^ n • (orbit B z n - orbit B z (n + 1))) := by
    simpa only [smul_sub] using hz.sub hBz
  rw [hpoint, average_add r (fun _ => a • w)
    (fun n => orbit B z n - orbit B z (n + 1)) (summable_constant r hrnorm _) hcb]
  rw [average_constant r hrnorm, average_coboundary r hr (orbit B z) hz hBz]
  rfl

end RiemannResearch.Analysis.AbelCoboundary

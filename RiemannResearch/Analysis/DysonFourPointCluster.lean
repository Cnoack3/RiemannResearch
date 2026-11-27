import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The fourth Dyson density with two points escaping

This pointwise limit concerns the sine determinant itself. The two-label
comparison for zeta ordinates uses integrated, fixed-window fourth tests.
-/
noncomputable section
open Filter Matrix
open scoped Topology
namespace RiemannResearch.Analysis.DysonFourPoint

def S (u : ℝ) : ℝ := Real.sinc (Real.pi*u)

private theorem S_tendsto : Tendsto S atTop (𝓝 0) := by
  have hlarge : Tendsto (fun t : ℝ => Real.pi*t) atTop atTop :=
    tendsto_id.const_mul_atTop Real.pi_pos
  have hi : Tendsto (fun t : ℝ => (Real.pi*t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlarge
  apply squeeze_zero_norm' _ hi
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have hp : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  rw [S,Real.sinc_of_ne_zero hp.ne',Real.norm_eq_abs,abs_div,abs_of_pos hp,← one_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hp.le

/-- A symmetric four-by-four matrix is recorded using its six edge values. -/
def fourGram (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,a,b,c; a,1,d,e; b,d,1,f; c,e,f,1]

/-- The unit-intensity sine-process fourth factorial density. Evenness of
sinc permits either orientation of each pair of arguments. -/
def fourDensity (x y z w : ℝ) : ℝ :=
  (fourGram (S (y-x)) (S (z-x)) (S (w-x)) (S (z-y)) (S (w-y)) (S (w-z))).det

theorem fourGram_two_separated_pairs (a f : ℝ) :
    (fourGram a 0 0 0 0 f).det = (1-a^2)*(1-f^2) := by
  simp [fourGram,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,
    Fin.succAbove,Matrix.of_apply]
  ring

theorem fourDensity_two_points_escape (x y : ℝ) :
    Tendsto (fun R : ℝ => fourDensity x y R (2*R)) atTop (𝓝 (1-S (y-x)^2)) := by
  have hk (j : ℝ) (hj : 0 < j) (c : ℝ) :
      Tendsto (fun R : ℝ => S (j*R-c)) atTop (𝓝 0) :=
    S_tendsto.comp (tendsto_atTop_add_const_right _ (-c) (tendsto_id.const_mul_atTop hj))
  let A (R : ℝ) := fourGram (S (y-x)) (S (R-x)) (S (2*R-x))
    (S (R-y)) (S (2*R-y)) (S (2*R-R))
  have hm : Tendsto A atTop (𝓝 (fourGram (S (y-x)) 0 0 0 0 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [A,fourGram,show ∀ r : ℝ, 2*r-r = r by intro r; ring]
    all_goals first | exact tendsto_const_nhds | exact S_tendsto |
      exact hk 2 (by norm_num) _ | simpa only [one_mul] using hk 1 zero_lt_one x |
      simpa only [one_mul] using hk 1 zero_lt_one y
  have hd := (continuous_id.matrix_det.tendsto _).comp hm
  simp only [id_eq] at hd
  rw [fourGram_two_separated_pairs] at hd
  simpa only [fourDensity,A,zero_pow (by decide : 2 ≠ 0),sub_zero,mul_one,Function.comp_def] using hd

end RiemannResearch.Analysis.DysonFourPoint

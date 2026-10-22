import RiemannResearch.Analysis.ProjectionSourceImprovement
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Correlation-normalized corrections for an actual projection residual

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Sections 1--6. All correlations below are signed. Normal equations, rather
than a totalized inverse, make singular cases explicit. No arithmetic
lower bound for the gain is assumed implicitly.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.CorrelationCorrection
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ProjectionCompression
open RiemannResearch.LinearAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inner_sq_le (x y : H) :
    (inner ℝ x y)^2 ≤ ‖x‖^2 * ‖y‖^2 := by
  have h := abs_real_inner_le_norm x y
  have hh := mul_self_le_mul_self (abs_nonneg (inner ℝ x y)) h
  simpa only [← pow_two, sq_abs, mul_pow] using hh

theorem screened_norm_sq_le (P : Submodule ℝ H) [P.HasOrthogonalProjection] (x : H) :
    ‖residual P x‖^2 ≤ ‖x‖^2 := by
  have h := projection_pythagoras P x
  change ‖x‖^2 = ‖P.starProjection x‖^2 + ‖residual P x‖^2 at h
  nlinarith [sq_nonneg ‖P.starProjection x‖]

theorem nested_gain (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b : H) :
    ‖residual P b‖^2 - ‖residual Q b‖^2 =
      ‖Q.starProjection b - P.starProjection b‖^2 := by
  have hu : Q.starProjection b - P.starProjection b ∈ Q :=
    Q.sub_mem (Q.starProjection_apply_mem b) (hPQ (P.starProjection_apply_mem b))
  have ho := Submodule.starProjection_inner_eq_zero b
    (Q.starProjection b - P.starProjection b) hu
  have he : residual P b =
      residual Q b + (Q.starProjection b - P.starProjection b) := by
    unfold RiemannResearch.Analysis.ProjectionSourceImprovement.residual
    abel
  rw [he, norm_add_sq_real]
  change inner ℝ (residual Q b) (Q.starProjection b - P.starProjection b) = 0 at ho
  rw [ho]
  ring

theorem nested_correlation (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (b z : H) (hz : z ∈ Q) :
    inner ℝ (residual P b) z =
      inner ℝ (Q.starProjection b - P.starProjection b) z := by
  have ho := Submodule.starProjection_inner_eq_zero b z hz
  simp only [RiemannResearch.Analysis.ProjectionSourceImprovement.residual, inner_sub_left] at *
  linarith

theorem nested_correlation_sq_le (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b z : H) (hz : z ∈ Q) :
    (inner ℝ (residual P b) z)^2 ≤
      (‖residual P b‖^2 - ‖residual Q b‖^2) * ‖z‖^2 := by
  rw [nested_gain P Q hPQ, nested_correlation P Q b z hz]
  exact inner_sq_le _ _

/-- Explicit witness: positivity is required, so division by zero is not
silently interpreted as a zero reconstruction cost. -/
theorem normalized_witness (e u : H) (D G : ℝ) (hG : 0 < G)
    (hc : inner ℝ e u = G) (hu : ‖u‖^2 ≤ G) :
    inner ℝ e ((D / G) • u) = D ∧
      ‖(D / G) • u‖^2 ≤ D^2 / G := by
  constructor
  · rw [real_inner_smul_right, hc, div_mul_cancel₀ _ (ne_of_gt hG)]
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ (D/G)^2 * G := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hG]

/-- Combining a screened raw correction with an orthogonal fresh optimum
adds their gains without discarding a mixed term by an inequality. -/
theorem completed_witness (e u v : H) (D G R : ℝ)
    (hc : inner ℝ e u = G) (hv : inner ℝ e v = R)
    (hu : ‖u‖^2 ≤ G) (hn : ‖v‖^2 = R)
    (ho : inner ℝ u v = 0) (hpos : 0 < G + R) :
    inner ℝ e ((D / (G+R)) • (u+v)) = D ∧
      ‖(D / (G+R)) • (u+v)‖^2 ≤ D^2 / (G+R) := by
  apply normalized_witness e (u+v) D (G+R) hpos
  · rw [inner_add_right, hc, hv]
  · rw [norm_add_sq_real, ho, hn]
    linarith

theorem gain_bound_of_witness (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b u : H) (huQ : u ∈ Q) (G : ℝ)
    (hc : inner ℝ (residual P b) u = G) (hu : ‖u‖^2 ≤ G) :
    G ≤ ‖residual P b‖^2 - ‖residual Q b‖^2 := by
  have hgain : 0 ≤ ‖residual P b‖^2 - ‖residual Q b‖^2 := by
    rw [nested_gain P Q hPQ]
    positivity
  have hG : 0 ≤ G := le_trans (sq_nonneg _) hu
  have hcs := nested_correlation_sq_le P Q hPQ b u huQ
  rw [hc] at hcs
  have hmul := mul_le_mul_of_nonneg_left hu hgain
  nlinarith

/-- Sharp lower cost for any feasible vector; this is not merely an upper
bound for a selected coefficient representation. -/
theorem feasible_cost_lower (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b w : H) (hw : w ∈ Q) (D : ℝ)
    (hc : inner ℝ (residual P b) w = D)
    (hg : 0 < ‖residual P b‖^2 - ‖residual Q b‖^2) :
    D^2 / (‖residual P b‖^2 - ‖residual Q b‖^2) ≤ ‖w‖^2 := by
  apply (div_le_iff₀ hg).mpr
  have h := nested_correlation_sq_le P Q hPQ b w hw
  rw [hc] at h
  simpa [mul_comm] using h

theorem zero_gain_infeasible (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b : H)
    (hg : ‖residual P b‖^2 - ‖residual Q b‖^2 = 0) (D : ℝ) (hD : D ≠ 0) :
    ¬ ∃ w ∈ Q, inner ℝ (residual P b) w = D := by
  rintro ⟨w, hw, hc⟩
  have h := nested_correlation_sq_le P Q hPQ b w hw
  rw [hg, hc, zero_mul] at h
  exact hD (by nlinarith [sq_nonneg D])

/-- The sharp lower cost is attained by the actual nested projection
increment. In the zero-gain case the preceding theorem gives infeasibility. -/
theorem optimal_normalized_increment (P Q : Submodule ℝ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : P ≤ Q) (b : H) (D : ℝ)
    (hg : 0 < ‖residual P b‖^2 - ‖residual Q b‖^2) :
    let t := Q.starProjection b - P.starProjection b
    let δ := ‖residual P b‖^2 - ‖residual Q b‖^2
    let w := (D/δ) • t
    w ∈ Q ∧ w ∈ Pᗮ ∧ inner ℝ (residual P b) w = D ∧ ‖w‖^2 = D^2/δ := by
  dsimp
  let t := Q.starProjection b - P.starProjection b
  have htQ : t ∈ Q := Q.sub_mem (Q.starProjection_apply_mem b)
    (hPQ (P.starProjection_apply_mem b))
  have htP : t ∈ Pᗮ := by
    apply (P.mem_orthogonal t).mpr
    intro y hy
    have hp := Submodule.starProjection_inner_eq_zero b y hy
    have hq := Submodule.starProjection_inner_eq_zero b y (hPQ hy)
    rw [real_inner_comm]
    dsimp [t]
    simp only [inner_sub_left] at *
    linarith
  have hn := nested_gain P Q hPQ b
  have hc : inner ℝ (residual P b) t =
      ‖residual P b‖^2 - ‖residual Q b‖^2 := by
    rw [nested_correlation P Q b t htQ, real_inner_self_eq_norm_sq]
    exact hn.symm
  refine ⟨Q.smul_mem _ htQ, (Pᗮ).smul_mem _ htP, ?_, ?_⟩
  · rw [real_inner_smul_right]
    change (D / (‖residual P b‖^2 - ‖residual Q b‖^2)) *
      inner ℝ (residual P b) t = D
    rw [hc, div_mul_cancel₀ _ (ne_of_gt hg)]
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← hn]
    field_simp [ne_of_gt hg]

/-- Exact signed raw two-column Gram quadratic. -/
theorem pair_energy (x y : H) (a b : ℝ) :
    ‖a • x + b • y‖^2 =
      a^2 * ‖x‖^2 + 2*a*b*inner ℝ x y + b^2 * ‖y‖^2 := by
  simp only [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem pair_trace_bound (x y : H) (a b : ℝ) :
    ‖a • x + b • y‖^2 ≤ (a^2+b^2) * (‖x‖^2+‖y‖^2) := by
  have h := sq_nonneg ‖b • x - a • y‖
  have he := pair_energy x y b (-a)
  simp only [neg_smul, ← sub_eq_add_neg] at he
  rw [he] at h
  rw [pair_energy]
  nlinarith

/-- The trace witness is explicit and uses the two actual signed sources.
It remains valid when the columns are dependent. -/
theorem pair_trace_witness (P : Submodule ℝ H) [P.HasOrthogonalProjection]
    (b x y : H) (D : ℝ)
    (hh : 0 < (inner ℝ (residual P b) x)^2 + (inner ℝ (residual P b) y)^2) :
    let h₂ := inner ℝ (residual P b) x
    let h₃ := inner ℝ (residual P b) y
    let s := h₂^2 + h₃^2
    let w := (D/s) • residual P (h₂ • x + h₃ • y)
    inner ℝ (residual P b) w = D ∧
      ‖w‖^2 ≤ D^2 * (‖x‖^2+‖y‖^2) / s := by
  dsimp
  constructor
  · rw [real_inner_smul_right, residual_inner, inner_add_right,
      real_inner_smul_right, real_inner_smul_right]
    convert div_mul_cancel₀ D (ne_of_gt hh) using 1 <;> ring
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hs := screened_norm_sq_le P
      ((inner ℝ (residual P b) x) • x + (inner ℝ (residual P b) y) • y)
    have ht := pair_trace_bound x y (inner ℝ (residual P b) x)
      (inner ℝ (residual P b) y)
    calc
      _ ≤ (D / ((inner ℝ (residual P b) x)^2 +
          (inner ℝ (residual P b) y)^2))^2 *
          (((inner ℝ (residual P b) x)^2 + (inner ℝ (residual P b) y)^2) *
            (‖x‖^2+‖y‖^2)) :=
        mul_le_mul_of_nonneg_left (hs.trans ht) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hh]

variable {ι : Type*} [Fintype ι]

/-- Every actual finite source lies in the range of its signed Gram map,
even when the columns are linearly dependent. -/
theorem normal_equations_exist (e : H) (v : ι → H) :
    ∃ c : ι → ℝ, ∀ i, inner ℝ (v i) (finiteSchurCombination v c) =
      inner ℝ (v i) e := by
  classical
  let S := Submodule.span ℝ (Set.range v)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (S.starProjection_apply_mem e)
  refine ⟨c, fun i => ?_⟩
  have hv : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have ho := Submodule.starProjection_inner_eq_zero e (v i) hv
  unfold finiteSchurCombination
  rw [hc, real_inner_comm (S.starProjection e) (v i), real_inner_comm e (v i)]
  rw [inner_sub_left] at ho
  linarith

/-- Raw normal equations retain all signed Gram entries. Screening cannot
increase energy and does not change correlation with the actual residual. -/
theorem raw_normal_witness (P : Submodule ℝ H) [P.HasOrthogonalProjection]
    (b : H) (v : ι → H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (v i) (finiteSchurCombination v c) =
      inner ℝ (v i) (residual P b)) :
    let G := ∑ i, c i * inner ℝ (v i) (residual P b)
    ‖finiteSchurCombination v c‖^2 = G ∧
    inner ℝ (residual P b) (residual P (finiteSchurCombination v c)) = G ∧
    ‖residual P (finiteSchurCombination v c)‖^2 ≤ G := by
  dsimp
  have hn : ‖finiteSchurCombination v c‖^2 =
      ∑ i, c i * inner ℝ (v i) (residual P b) := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; unfold finiteSchurCombination
    simp only [sum_inner, real_inner_smul_left, hc]
  refine ⟨hn, ?_, ?_⟩
  · rw [residual_inner, real_inner_comm]
    simp [finiteSchurCombination, sum_inner, real_inner_smul_left]
  · rw [← hn]
    exact screened_norm_sq_le P _

/-- The finite trace bound holds for the optimal raw normal-equation gain,
not just for the whole enlarged-space gain. -/
theorem normal_equations_trace_bound (e : H) (v : ι → H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (v i) (finiteSchurCombination v c) = inner ℝ (v i) e) :
    (∑ i, (inner ℝ (v i) e)^2) ≤
      (∑ i, ‖v i‖^2) * ‖finiteSchurCombination v c‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [← hc i]
  exact inner_sq_le _ _

/-- Exact two-by-two inverse-Gram value, including the signed mixed term.
Only nonsingularity is needed for this algebraic identity. -/
theorem two_by_two_gain_formula (a b c h₂ h₃ x y : ℝ)
    (h₂eq : a*x+c*y = h₂) (h₃eq : c*x+b*y = h₃)
    (hdet : a*b-c^2 ≠ 0) :
    x*h₂+y*h₃ = (b*h₂^2-2*c*h₂*h₃+a*h₃^2)/(a*b-c^2) := by
  apply (eq_div_iff hdet).mpr
  rw [← h₂eq, ← h₃eq]
  ring

end RiemannResearch.Analysis.CorrelationCorrection

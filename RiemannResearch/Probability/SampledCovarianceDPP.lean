import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.Probability.DeterminantalWindow
import RiemannResearch.Probability.DeterminantalDiagonal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.FieldSimp

/-!
# DPPs constructed from sampled Hilbert-space covariance

Source: user-provided `V_vector_space_RH.pdf`, Sections 2--3, for the sampled
covariance. The positive-contraction DPP construction follows Lyons,
*Determinantal probability measures*, arXiv:math/0204325, Sections 7--8.

For arbitrary real Hilbert vectors v_j and nonnegative weights w_j, the sole
normalization is sum_j w_j ||v_j||^2 <= 1. The resulting covariance kernel on
an orthonormal coordinate family has both finite principal positivity and
complement positivity proved below. Thus an actual DPP is constructed without
assuming covariance positivity. The ground set may be infinite.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical

namespace RiemannResearch.Probability.DPP.SampledCovariance
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

variable {H α J κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype J]

private theorem sum_posSemidef [Fintype κ] [DecidableEq κ]
    (A : J → Matrix κ κ ℝ) (hA : ∀ j, (A j).PosSemidef) :
    (∑ j, A j).PosSemidef := by
  apply Finset.sum_induction
  · exact fun _ _ ha hb => ha.add hb
  · exact Matrix.PosSemidef.zero
  · exact fun j _ => hA j

/-- A rank-one outer product is its normalized projection times its energy;
the identity includes the zero-vector case. -/
theorem norm_sq_mul_projectionKernel (v : H) (e : α → H) (i k : α) :
    ‖v‖ ^ 2 * kernel (ℝ ∙ v) e i k =
      inner ℝ v (e i) * inner ℝ v (e k) := by
  by_cases hv : v = 0
  · subst v
    simp [kernel]
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  simp [kernel, Submodule.starProjection_singleton,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  <;> field_simp [hn]
  <;> ring

/-- The weighted empirical covariance in a real orthonormal coordinate family. -/
def covarianceKernel (w : J → ℝ) (v : J → H) (e : α → H) (i k : α) : ℝ :=
  ∑ j, w j * (inner ℝ (v j) (e i) * inner ℝ (v j) (e k))

theorem covarianceKernel_eq_weighted_projections
    (w : J → ℝ) (v : J → H) (e : α → H) (i k : α) :
    covarianceKernel w v e i k =
      ∑ j, (w j * ‖v j‖ ^ 2) * kernel (ℝ ∙ v j) e i k := by
  simp_rw [mul_assoc, norm_sq_mul_projectionKernel]
  rfl

theorem covariance_principal_posSemidef [Fintype κ] [DecidableEq κ]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (v : J → H) (e : α → H) (a : κ → α) :
    (Matrix.of (fun i k => covarianceKernel w v e (a i) (a k))).PosSemidef := by
  have he : Matrix.of (fun i k => covarianceKernel w v e (a i) (a k)) =
      ∑ j, (w j * ‖v j‖ ^ 2) • Matrix.of (fun i k => kernel (ℝ ∙ v j) e (a i) (a k)) := by
    ext i k
    simp [covarianceKernel_eq_weighted_projections, Matrix.sum_apply]
  rw [he]
  exact sum_posSemidef _ (fun j =>
    (principal_posSemidef (ℝ ∙ v j) e a).smul (mul_nonneg (hw j) (sq_nonneg _)))

/-- Exact decomposition of the complementary kernel, including the unused
normalization mass. This identity is the contraction proof. -/
theorem complement_principal_eq [Fintype κ] [DecidableEq κ]
    (w : J → ℝ) (v : J → H) (e : α → H) (a : κ → α) :
    1 - Matrix.of (fun i k => covarianceKernel w v e (a i) (a k)) =
      (1 - ∑ j, w j * ‖v j‖ ^ 2) • (1 : Matrix κ κ ℝ) +
        ∑ j, (w j * ‖v j‖ ^ 2) •
          (1 - Matrix.of (fun i k => kernel (ℝ ∙ v j) e (a i) (a k))) := by
  ext i k
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, covarianceKernel_eq_weighted_projections]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem covariance_complement_posSemidef [Fintype κ] [DecidableEq κ]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (v : J → H)
    (hbudget : ∑ j, w j * ‖v j‖ ^ 2 ≤ 1) (e : α → H) (a : κ → α)
    (he : ∀ i k, inner ℝ (e (a i)) (e (a k)) = if i = k then 1 else 0) :
    (1 - Matrix.of (fun i k => covarianceKernel w v e (a i) (a k))).PosSemidef := by
  rw [complement_principal_eq]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hbudget)
  · apply sum_posSemidef
    intro j
    exact (identity_sub_principal_posSemidef (ℝ ∙ v j) e a he).smul
      (mul_nonneg (hw j) (sq_nonneg _))

variable (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (v : J → H)
    (hbudget : ∑ j, w j * ‖v j‖ ^ 2 ≤ 1) (e : α → H)
    (he : ∀ i k, inner ℝ (e i) (e k) = if i = k then 1 else 0)

include he in
private theorem coordinate_restriction (I : Finset α) :
    ∀ i k : I, inner ℝ (e i.1) (e k.1) = if i = k then 1 else 0 := by
  intro i k
  rw [he]
  by_cases hik : i = k
  · subst k
    simp
  · have hv : i.1 ≠ k.1 := fun h => hik (Subtype.ext h)
    simp [hik, hv]

/-- An actual probability law from sample vectors and their energy budget. -/
def law : Measure (α → Bool) :=
  contractionDPP (covarianceKernel w v e)
    (fun I => covariance_principal_posSemidef w hw v e (fun i : I => i.1))
    (fun I => covariance_complement_posSemidef w hw v hbudget e (fun i : I => i.1)
      (coordinate_restriction e he I))

instance law_probability : IsProbabilityMeasure (law w hw v hbudget e he) := by
  unfold law
  infer_instance

/-- Every finite inclusion event equals the corresponding covariance determinant. -/
theorem law_isDPP :
    IsDPP (law w hw v hbudget e he) (fun x => {i | x i = true})
      (covarianceKernel w v e) :=
  contractionDPP_isDPP _ _ _

/-- The actual complementary random subset has kernel `I-K`, so the exact
residual decomposition above also describes its finite hole correlations. -/
theorem law_holes_isDPP :
    IsDPP (law w hw v hbudget e he) (fun x => {i | x i = false})
      (fun i k => (if i = k then 1 else 0) - covarianceKernel w v e i k) := by
  constructor
  · intro i
    exact (measurableSet_singleton false).preimage (measurable_pi_apply i)
  · intro n a
    have ha : ∀ i k, inner ℝ (e (a i)) (e (a k)) = if i = k then 1 else 0 := by
      intro i k
      simpa only [a.injective.eq_iff] using he (a i) (a k)
    have hpos (S : Finset (Fin n)) : 0 ≤ exactWeight
        (Matrix.of (fun i k => covarianceKernel w v e (a i) (a k))) S :=
      exactWeight_nonneg _ (covariance_principal_posSemidef w hw v e a)
        (covariance_complement_posSemidef w hw v hbudget e a ha) S
    have hh := (law_isDPP w hw v hbudget e he).finite_gap a hpos
    convert hh using 1
    · congr 1
      ext x
      simp
    · congr 1
      ext i k
      simp [Matrix.sub_apply, Matrix.one_apply, a.injective.eq_iff]

/-- The sample count may grow. Entrywise covariance convergence is precisely
what transfers these actual laws to the independent diagonal limit; positivity
and probability-law existence are supplied by the proved energy-budget bounds. -/
theorem law_configuration_tendsto_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ → ℕ) (weights : (n : ℕ) → Fin (m n) → ℝ)
    (hweights : ∀ n j, 0 ≤ weights n j) (samples : (n : ℕ) → Fin (m n) → H)
    (henergy : ∀ n, ∑ j, weights n j * ‖samples n j‖ ^ 2 ≤ 1)
    (coords : α → H)
    (hcoords : ∀ i k, inner ℝ (coords i) (coords k) = if i = k then 1 else 0)
    (p : α → ℝ)
    (hlim : ∀ i k, Filter.Tendsto
      (fun n => covarianceKernel (weights n) (samples n) coords i k) Filter.atTop
      (nhds (diagonalKernel p i k))) (a : ι ↪ α) (S : Finset ι) :
    Filter.Tendsto (fun n =>
      (law (weights n) (hweights n) (samples n) (henergy n) coords hcoords).real
        {x | ∀ i, x (a i) = decide (i ∈ S)}) Filter.atTop
      (nhds (∏ i, if i ∈ S then p (a i) else 1 - p (a i))) := by
  exact contractionDPP_configuration_tendsto_diagonal
    (fun n => covarianceKernel (weights n) (samples n) coords)
    (fun n I => covariance_principal_posSemidef (weights n) (hweights n)
      (samples n) coords (fun i : I => i.1))
    (fun n I => covariance_complement_posSemidef (weights n) (hweights n)
      (samples n) (henergy n) coords (fun i : I => i.1)
      (coordinate_restriction coords hcoords I)) p hlim a S

end RiemannResearch.Probability.DPP.SampledCovariance

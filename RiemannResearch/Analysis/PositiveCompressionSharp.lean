import RiemannResearch.Analysis.PositiveCompressionCertificate
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sharp displacement and certified Richardson iteration

For a positive contraction D satisfying the quadratic form D² ≤ D,
the correction for an orthogonal residual obeys 8‖d‖² ≤ ‖r‖².
This is the constant in the Pareto-first manuscript, related to the
generalized Wielandt inequality (Lin and Sinnamon, 2012). The proof below
uses only the displayed quadratic-form hypotheses.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.PositiveCompressionCertificate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (V : Submodule ℝ E) [V.HasOrthogonalProjection]

theorem compression_reflection_norm_le (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x)) (x : E) (hx : x ∈ V) :
    ‖x - (2:ℝ) • V.starProjection (D x)‖ ≤ ‖x‖ := by
  have hp : ‖V.starProjection (D x)‖ ^ 2 ≤ inner ℝ x (V.starProjection (D x)) := by
    rw [inner_projection V x (D x) hx]
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (projection_norm_le V (D x))).trans (hfirm x)
  have he := norm_sub_sq_real x ((2:ℝ) • V.starProjection (D x))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    real_inner_smul_right] at he
  nlinarith [norm_nonneg (x - (2:ℝ) • V.starProjection (D x)), norm_nonneg x]

def richardsonStep (D : E →L[ℝ] E) (a v : E) : E :=
  v + (2/3:ℝ) • (a-normalOperator V D v)

theorem richardsonStep_fixed (D : E →L[ℝ] E) (a d : E)
    (heq : normalOperator V D d = a) : richardsonStep V D a d = d := by
  simp [richardsonStep, heq]

theorem richardsonStep_mem (D : E →L[ℝ] E) (a v : E) (ha : a ∈ V) (hv : v ∈ V) :
    richardsonStep V D a v ∈ V :=
  V.add_mem hv (V.smul_mem _ (V.sub_mem ha
    (V.add_mem hv (V.starProjection_apply_mem _))))

theorem richardsonStep_contract (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (a v w : E) (hv : v ∈ V) (hw : w ∈ V) :
    ‖richardsonStep V D a v-richardsonStep V D a w‖ ≤ (1/3:ℝ)*‖v-w‖ := by
  have he : richardsonStep V D a v-richardsonStep V D a w =
      (1/3:ℝ) • ((v-w)-(2:ℝ) • V.starProjection (D (v-w))) := by
    simp only [richardsonStep, normalOperator_apply, map_sub]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ)≤1/3)]
  exact mul_le_mul_of_nonneg_left
    (compression_reflection_norm_le V D hfirm (v-w) (V.sub_mem hv hw)) (by norm_num)

def richardsonIterate (D : E →L[ℝ] E) (a : E) : ℕ → E
  | 0 => 0
  | n+1 => richardsonStep V D a (richardsonIterate D a n)

theorem richardsonIterate_mem (D : E →L[ℝ] E) (a : E) (ha : a ∈ V) (n : ℕ) :
    richardsonIterate V D a n ∈ V := by
  induction n with
  | zero => exact V.zero_mem
  | succ n ih => exact richardsonStep_mem V D a _ ha ih

/-- A solver error bound after any number of exact steps. Inexact solves can
instead use the a posteriori certificate from PositiveCompressionCertificate. -/
theorem richardsonIterate_error (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (a d : E) (ha : a ∈ V) (hd : d ∈ V)
    (heq : normalOperator V D d = a) (n : ℕ) :
    ‖d-richardsonIterate V D a n‖ ≤ (1/3:ℝ)^n*‖d‖ := by
  induction n with
  | zero => simp [richardsonIterate]
  | succ n ih =>
    change ‖d-richardsonStep V D a (richardsonIterate V D a n)‖ ≤ _
    calc
      _ = ‖richardsonStep V D a d -
          richardsonStep V D a (richardsonIterate V D a n)‖ := by
        rw [richardsonStep_fixed V D a d heq]
      _ ≤ (1/3:ℝ)*‖d-richardsonIterate V D a n‖ :=
        richardsonStep_contract V D hfirm a d _ hd (richardsonIterate_mem V D a ha n)
      _ ≤ (1/3:ℝ)*((1/3:ℝ)^n*‖d‖) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- The scalar inequality behind the sharp factor, with no normalization of r. -/
theorem unit_forcing_sharp (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (x r : E) (hx : ‖x‖ = 1) (hr : inner ℝ r x = 0)
    (δ : ℝ) (heq : inner ℝ r (D x) = δ * (1 + inner ℝ x (D x))) :
    8*δ^2 ≤ ‖r‖ ^ 2 := by
  let t := inner ℝ x (D x)
  let y := D x-t • x
  have ht : 0 ≤ t := (sq_nonneg ‖D x‖).trans (hfirm x)
  have hy : inner ℝ r y = δ*(1+t) := by
    simp only [y, inner_sub_right, real_inner_smul_right, hr, mul_zero, sub_zero]
    exact heq
  have hyy : ‖y‖ ^ 2 ≤ t-t^2 := by
    have hn := norm_sub_sq_real (D x) (t • x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hx, mul_one,
      real_inner_smul_right] at hn
    have hc : inner ℝ (D x) x = t := real_inner_comm _ _
    rw [hc] at hn
    have hf := hfirm x
    change ‖D x‖ ^ 2 ≤ t at hf
    dsimp only [y]
    nlinarith
  have hc := real_inner_mul_inner_self_le r y
  simp only [real_inner_self_eq_norm_sq, hy] at hc
  have hmul := mul_le_mul_of_nonneg_left hyy (sq_nonneg ‖r‖)
  have hpoly := mul_nonneg (sq_nonneg ‖r‖) (sq_nonneg (1-3*t))
  have h : (8*δ^2)*(1+t)^2 ≤ ‖r‖ ^ 2*(1+t)^2 := by
    nlinarith only [hc, hmul, hpoly]
  by_contra hbad
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hbad)
    (sq_pos_of_pos (by linarith : 0 < 1+t))
  exact (not_lt_of_ge h) hlt

theorem solution_sharp_sq (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (hsym : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (d r : E) (hd : d ∈ V) (hr : r ∈ Vᗮ)
    (heq : normalOperator V D d = V.starProjection (D r)) :
    8*‖d‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  by_cases hz : d = 0
  · simp [hz]
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hz
  let x := ‖d‖⁻¹ • d
  have hx : x ∈ V := V.smul_mem _ hd
  have hxn : ‖x‖ = 1 := by
    simp [x, norm_smul, hn.ne']
  have hdx : d = ‖d‖ • x := by
    dsimp only [x]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hrx : inner ℝ r x = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hx hr
  apply unit_forcing_sharp D hfirm x r hxn hrx ‖d‖
  have he := congrArg (fun z => inner ℝ x z) heq
  rw [normalOperator_apply, inner_add_right,
    inner_projection V x (D d) hx, inner_projection V x (D r) hx] at he
  rw [hdx, map_smul, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hxn, one_pow, mul_one, real_inner_smul_right] at he
  have hsymm : inner ℝ x (D r) = inner ℝ r (D x) := by
    rw [← hsym, real_inner_comm]
  rw [hsymm] at he
  linarith

def richardsonKernel (D : E →L[ℝ] E) : E →L[ℝ] E :=
  (1/3:ℝ) • ContinuousLinearMap.id ℝ E -
    (2/3:ℝ) • (V.starProjection.comp D)

theorem richardsonStep_eq (D : E →L[ℝ] E) (a v : E) :
    richardsonStep V D a v = (2/3:ℝ) • a + richardsonKernel V D v := by
  simp only [richardsonStep, normalOperator_apply, richardsonKernel, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  module

/-- The rescaled inverse series with its exact finite truncation. -/
theorem richardsonIterate_series (D : E →L[ℝ] E) (a : E) (n : ℕ) :
    richardsonIterate V D a n =
      (2/3:ℝ) • ∑ k ∈ Finset.range n, ((richardsonKernel V D)^k) a := by
  induction n with
  | zero => simp [richardsonIterate]
  | succ n ih =>
    have hs : richardsonKernel V D
        (∑ k ∈ Finset.range n, ((richardsonKernel V D)^k) a) =
        ∑ k ∈ Finset.range n, ((richardsonKernel V D)^(k+1)) a := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ']
      rfl
    rw [richardsonIterate, richardsonStep_eq, ih, map_smul, hs,
      Finset.sum_range_succ']
    simp only [pow_zero, one_apply_eq_self, smul_add]
    exact add_comm _ _

theorem richardsonIterate_tendsto (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (a d : E) (ha : a ∈ V) (hd : d ∈ V)
    (heq : normalOperator V D d = a) :
    Tendsto (richardsonIterate V D a) atTop (𝓝 d) := by
  have ht : Tendsto (fun n : ℕ => (1/3:ℝ)^n*‖d‖) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)).mul_const ‖d‖
    simpa only [zero_mul] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  rw [dist_eq_norm, norm_sub_rev]
  exact (richardsonIterate_error V D hfirm a d ha hd heq n).trans_lt hn


/-- The off-diagonal compression has norm at most one half. This gives a
universal complete-energy certificate even before arithmetic cancellation. -/
theorem forcing_sharp_sq (D : E →L[ℝ] E)
    (hfirm : ∀ x, ‖D x‖ ^ 2 ≤ inner ℝ x (D x))
    (r : E) (hr : r ∈ Vᗮ) :
    4 * ‖V.starProjection (D r)‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have hPr : V.starProjection r = 0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero V.zero_mem
    intro v hv
    rw [sub_zero, real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv hr
  have he : V.starProjection (D r-(1/2:ℝ) • r) = V.starProjection (D r) := by
    rw [map_sub, map_smul, hPr, smul_zero, sub_zero]
  have hc := projection_norm_le V (D r-(1/2:ℝ) • r)
  rw [he] at hc
  have hc2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc
  have hn := norm_sub_sq_real (D r) ((1/2:ℝ) • r)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ)≤1/2),
    real_inner_smul_right, ← real_inner_comm (D r) r] at hn
  nlinarith [hfirm r]

end RiemannResearch.Analysis.PositiveCompressionCertificate

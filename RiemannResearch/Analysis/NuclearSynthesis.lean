import RiemannResearch.Analysis.SquareSummableSynthesis
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nuclear representations from square-summable columns

The RH consumer is `RH/WeilDampedPrimeOperator`. The construction proves
the Hilbert-Schmidt product estimate through an actual summable rank-one
expansion, using Bessel's inequality and a Hilbert basis.

Source: the standard Hilbert-Schmidt/trace-class product argument, e.g.
Jordan Bell, Trace class operators and Hilbert-Schmidt operators (2016),
Theorem 18, https://jordanbell.info/LaTeX/mathematics/traceclass/.
This citation supports the strategy and terminology. No spectral or
positivity conclusion is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.SquareSummableSynthesis
variable {ι κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem analysis_orthonormal_sum_le (u : lp (fun _ : ι => H) 2)
    {v : κ → H} (hv : Orthonormal ℂ v) (s : Finset κ) :
    ∑ k ∈ s, ‖analysis u (v k)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  classical
  have hs (k : κ) : Summable (fun i => ‖inner ℂ (u i) (v k)‖ ^ 2) :=
    summable_sq (analysis u (v k))
  calc
    _ = ∑' i, ∑ k ∈ s, ‖inner ℂ (u i) (v k)‖ ^ 2 := by
      simp_rw [norm_sq, analysis_apply]
      exact (Summable.tsum_finsetSum (fun k (_ : k ∈ s) => hs k)).symm
    _ ≤ ∑' i, ‖u i‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro i
        simpa only [norm_inner_symm] using hv.sum_inner_products_le (u i) (s := s)
      · exact summable_sum (fun k (_ : k ∈ s) => hs k)
      · exact summable_sq u
    _ = _ := (norm_sq u).symm

theorem analysis_orthonormal_summable (u : lp (fun _ : ι => H) 2)
    {v : κ → H} (hv : Orthonormal ℂ v) :
    Summable (fun k => ‖analysis u (v k)‖ ^ 2) :=
  summable_of_sum_le (fun k => sq_nonneg _) (analysis_orthonormal_sum_le u hv)

theorem analysis_orthonormal_tsum_le (u : lp (fun _ : ι => H) 2)
    {v : κ → H} (hv : Orthonormal ℂ v) :
    (∑' k, ‖analysis u (v k)‖ ^ 2) ≤ ‖u‖ ^ 2 :=
  le_of_tendsto (analysis_orthonormal_summable u hv).hasSum
    (Filter.Eventually.of_forall (analysis_orthonormal_sum_le u hv))

def analysisOnOrthonormal (u : lp (fun _ : ι => H) 2)
    {v : κ → H} (hv : Orthonormal ℂ v) : lp (fun _ : κ => Coeff ι) 2 :=
  ⟨fun k => analysis u (v k), (memℓp_gen_iff (by norm_num)).2
    (by simpa using analysis_orthonormal_summable u hv)⟩

theorem analysisOnOrthonormal_norm_le (u : lp (fun _ : ι => H) 2)
    {v : κ → H} (hv : Orthonormal ℂ v) :
    ‖analysisOnOrthonormal u hv‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg _)
  change (∑' k, ‖analysis u (v k)‖ ^ (2 : ENNReal).toReal) ≤ ‖u‖ ^ (2 : ENNReal).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    analysis_orthonormal_tsum_le u hv

def rankOne (x y : H) : H →L[ℂ] H := (innerSL ℂ y).smulRight x

@[simp] theorem rankOne_apply (x y z : H) : rankOne x y z = inner ℂ y z • x := rfl

theorem rankOne_norm_le (x y : H) : ‖rankOne x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  rw [rankOne_apply, norm_smul]
  calc
    ‖inner ℂ y z‖ * ‖x‖ ≤ (‖y‖ * ‖z‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (norm_inner_le_norm y z) (norm_nonneg x)
    _ = (‖x‖ * ‖y‖) * ‖z‖ := by ring

theorem rankOne_summable (p q : lp (fun _ : κ => H) 2) :
    Summable (fun k => rankOne (p k) (q k)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => rankOne_norm_le _ _)
    (lp.summable_mul (by simpa using Real.HolderConjugate.two_two) p q)

theorem product_nuclear_representation
    (u v : lp (fun _ : ι => H) 2) (U : H →ₗᵢ[ℂ] H) (b : HilbertBasis κ ℂ H) :
    ∃ p q : κ → Coeff ι,
      Summable (fun k => ‖p k‖ * ‖q k‖) ∧
      (∑' k, ‖p k‖ * ‖q k‖) ≤ ‖u‖ * ‖v‖ ∧
      HasSum (fun k => rankOne (p k) (q k))
        ((analysis u).comp (U.toContinuousLinearMap.comp (synthesis v))) := by
  let p := analysisOnOrthonormal u (b.orthonormal.comp_linearIsometry U)
  let q := analysisOnOrthonormal v b.orthonormal
  have hpq := lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two) p q
  refine ⟨p, q, hpq.1, ?_, ?_⟩
  · exact hpq.2.trans (mul_le_mul
      (analysisOnOrthonormal_norm_le u _) (analysisOnOrthonormal_norm_le v _)
      (norm_nonneg q) (norm_nonneg u))
  · have hs := rankOne_summable p q
    have he : (∑' k, rankOne (p k) (q k)) =
        (analysis u).comp (U.toContinuousLinearMap.comp (synthesis v)) := by
      apply ContinuousLinearMap.ext
      intro x
      let ev : (Coeff ι →L[ℂ] Coeff ι) →L[ℂ] Coeff ι :=
        ({ toFun := fun T => T x
           map_add' := by intros; rfl
           map_smul' := by intros; rfl } :
          (Coeff ι →L[ℂ] Coeff ι) →ₗ[ℂ] Coeff ι).mkContinuous ‖x‖ (by
            intro T
            change ‖T x‖ ≤ ‖x‖ * ‖T‖
            simpa only [mul_comm] using T.le_opNorm x)
      have h_eval := ev.hasSum hs.hasSum
      have hh := (analysis u).hasSum
        (U.toContinuousLinearMap.hasSum (b.hasSum_repr (synthesis v x)))
      have hfun : (fun k => ev (rankOne (p k) (q k))) =
          (fun k => analysis u (U ((b.repr (synthesis v x) k) • b k))) := by
        funext k
        change inner ℂ (analysis v (b k)) x • analysis u (U (b k)) = _
        simp only [map_smul, HilbertBasis.repr_apply_apply, synthesis,
          ContinuousLinearMap.adjoint_inner_right]
      rw [hfun] at h_eval
      exact h_eval.unique hh
    rw [← he]
    exact hs.hasSum

end RiemannResearch.Analysis.SquareSummableSynthesis

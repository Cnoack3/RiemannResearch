import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Synthesis from square-summable Hilbert-space columns

The RH consumer is the actual damped prime-power synthesis map in
`RH/WeilDampedSynthesis`. The map is constructed as the adjoint of its
bounded analysis map. No operator existence or convergence assumption is used.

Source: standard Hilbert-space duality and the user-provided prime-side
factorization continuation (November 15, 2026), Priority 1.
-/

noncomputable section
open Classical
open scoped InnerProductSpace
namespace RiemannResearch.Analysis.SquareSummableSynthesis
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Coeff (ι : Type*) := lp (fun _ : ι => ℂ) 2

theorem summable_sq (u : lp (fun _ : ι => H) 2) :
    Summable (fun i => ‖u i‖ ^ 2) := by
  simpa using (lp.memℓp u).summable (by norm_num)

theorem norm_sq (u : lp (fun _ : ι => H) 2) :
    ‖u‖ ^ 2 = ∑' i, ‖u i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u

def analysisVec (u : lp (fun _ : ι => H) 2) (x : H) : Coeff ι :=
  ⟨fun i => inner ℂ (u i) x, (memℓp_gen_iff (by norm_num)).2 (by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
      simpa only [mul_pow] using
        pow_le_pow_left₀ (norm_nonneg (inner ℂ (u i) x)) (norm_inner_le_norm _ _) 2)
      ((summable_sq u).mul_right (‖x‖ ^ 2)))⟩

theorem analysisVec_norm (u : lp (fun _ : ι => H) 2) (x : H) :
    ‖analysisVec u x‖ ≤ ‖u‖ * ‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    ∑' i, ‖analysisVec u x i‖ ^ 2 ≤ ∑' i, ‖u i‖ ^ 2 * ‖x‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro i
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (u i) x) 2).trans_eq (mul_pow _ _ _)
      · exact summable_sq (analysisVec u x)
      · exact (summable_sq u).mul_right _
    _ = (‖u‖ * ‖x‖) ^ 2 := by rw [tsum_mul_right, ← norm_sq u, mul_pow]

def analysis (u : lp (fun _ : ι => H) 2) : H →L[ℂ] Coeff ι :=
  ({ toFun := analysisVec u
     map_add' := by intro x y; ext i; exact inner_add_right _ _ _
     map_smul' := by intro c x; ext i; exact inner_smul_right _ _ _ } : H →ₗ[ℂ] Coeff ι).mkContinuous
    ‖u‖ (analysisVec_norm u)

def synthesis (u : lp (fun _ : ι => H) 2) : Coeff ι →L[ℂ] H :=
  (analysis u).adjoint

@[simp] theorem analysis_apply (u : lp (fun _ : ι => H) 2) (x : H) (i : ι) :
    analysis u x i = inner ℂ (u i) x := rfl

theorem synthesis_single [DecidableEq ι] (u : lp (fun _ : ι => H) 2) (i : ι) :
    synthesis u (lp.single 2 i 1) = u i := by
  apply ext_inner_right ℂ
  intro x
  rw [synthesis, ContinuousLinearMap.adjoint_inner_left]
  simp [lp.inner_single_left, analysis_apply]

theorem synthesis_norm_le (u : lp (fun _ : ι => H) 2) :
    ‖synthesis u‖ ≤ ‖u‖ := by
  rw [synthesis, ContinuousLinearMap.adjoint.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _


theorem synthesis_single_smul [DecidableEq ι] (u : lp (fun _ : ι => H) 2)
    (i : ι) (z : ℂ) :
    synthesis u (lp.single 2 i z) = z • u i := by
  have h : lp.single 2 i z = z • (lp.single 2 i (1 : ℂ) : Coeff ι) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ι => ℂ) 2 i z (1 : ℂ)
  rw [h, map_smul, synthesis_single]

theorem synthesis_hasSum [DecidableEq ι] (u : lp (fun _ : ι => H) 2) (c : Coeff ι) :
    HasSum (fun i => c i • u i) (synthesis u c) := by
  simpa only [synthesis_single_smul] using
    (synthesis u).hasSum (lp.hasSum_single (by norm_num) c)

theorem ext_single [DecidableEq ι] {A B : Coeff ι →L[ℂ] H}
    (h : ∀ i, A (lp.single 2 i 1) = B (lp.single 2 i 1)) : A = B := by
  ext c
  have he (i : ι) : A (lp.single 2 i (c i)) = B (lp.single 2 i (c i)) := by
    have hi : lp.single 2 i (c i) = c i • (lp.single 2 i (1 : ℂ) : Coeff ι) := by
      simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ι => ℂ) 2 i (c i) (1 : ℂ)
    rw [hi, map_smul, map_smul, h]
  have hA := A.hasSum (lp.hasSum_single (by norm_num) c)
  have hB := B.hasSum (lp.hasSum_single (by norm_num) c)
  have hfun := funext he
  rw [hfun] at hA
  exact hA.unique hB

def mask (s : Set ι) (u : lp (fun _ : ι => H) 2) : lp (fun _ : ι => H) 2 :=
  ⟨s.indicator u, (lp.memℓp u).mono' (by
    intro i
    classical
    by_cases hi : i ∈ s <;> simp [Set.indicator_apply, hi])⟩

@[simp] theorem mask_apply (s : Set ι) (u : lp (fun _ : ι => H) 2) (i : ι) :
    mask s u i = s.indicator u i := rfl

theorem mask_norm_le (s : Set ι) (u : lp (fun _ : ι => H) 2) : ‖mask s u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num)
  intro i
  classical
  by_cases hi : i ∈ s <;> simp [mask_apply, Set.indicator_apply, hi]

def projection (s : Set ι) : Coeff ι →L[ℂ] Coeff ι :=
  ({ toFun := mask s
     map_add' := by
       intro x y
       ext i
       classical
       change (if i ∈ s then x i + y i else 0) =
         (if i ∈ s then x i else 0) + (if i ∈ s then y i else 0)
       by_cases hi : i ∈ s <;> simp [hi]
     map_smul' := by
       intro z x
       ext i
       classical
       by_cases hi : i ∈ s <;> simp [mask_apply, Set.indicator_apply, hi] } :
       Coeff ι →ₗ[ℂ] Coeff ι).mkContinuous 1 (by
         intro x
         change ‖mask s x‖ ≤ 1 * ‖x‖
         simpa only [one_mul] using mask_norm_le s x)

@[simp] theorem projection_apply (s : Set ι) (x : Coeff ι) (i : ι) :
    projection s x i = s.indicator x i := rfl

theorem projection_single [DecidableEq ι] (s : Set ι) (i : ι) :
    projection s (lp.single 2 i 1) =
      if i ∈ s then lp.single 2 i 1 else 0 := by
  classical
  ext j
  by_cases hi : i ∈ s <;> by_cases hj : j = i <;>
    simp [projection_apply, Set.indicator_apply, lp.single_apply, Pi.single_apply, hi, hj]

theorem synthesis_comp_projection [DecidableEq ι] (s : Set ι)
    (u : lp (fun _ : ι => H) 2) :
    (synthesis u).comp (projection s) = synthesis (mask s u) := by
  apply ext_single
  intro i
  classical
  rw [ContinuousLinearMap.comp_apply, projection_single]
  by_cases hi : i ∈ s <;> simp [hi, synthesis_single, mask_apply, Set.indicator_apply]

theorem synthesis_column_square_sum [DecidableEq ι] (u : lp (fun _ : ι => H) 2) :
    Summable (fun i => ‖synthesis u (lp.single 2 i 1)‖ ^ 2) ∧
      (∑' i, ‖synthesis u (lp.single 2 i 1)‖ ^ 2) = ‖u‖ ^ 2 := by
  simp only [synthesis_single]
  exact ⟨summable_sq u, (norm_sq u).symm⟩

end RiemannResearch.Analysis.SquareSummableSynthesis

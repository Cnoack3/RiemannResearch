import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# Exact prime-power evaluation threshold
Source: V_vector_space_RH.pdf, Section 6, equation (6.3).
In isometric coordinates c(q)=h(q)q^(-sigma), evaluation is sum c(q)k(q).
This proves the exact boundedness threshold and includes the failure at the
critical boundary, using Mathlib's prime reciprocal divergence theorem.
The finite-functional criterion is proved in both directions.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.PrimePowerEvaluation
abbrev Site := {n : ℕ // IsPrimePow n}
theorem summable_rpow_iff (r : ℝ) :
    Summable (fun q : Site => (q.1 : ℝ)^r) ↔ r < -1 := by
  constructor
  · intro h
    let e : Nat.Primes → Site := fun p => ⟨p.1, p.property.isPrimePow⟩
    have he : Function.Injective e := by
      intro p q h
      apply Subtype.ext
      simpa [e] using congrArg (fun x : Site => x.1) h
    have hs : Summable (fun p : Nat.Primes => (p.1 : ℝ)^r) := h.comp_injective (i := e) he
    exact Nat.Primes.summable_rpow.mp hs
  · intro hr
    exact (Real.summable_nat_rpow.mpr hr).subtype _

def feature (σ : ℝ) (w : ℂ) (q : Site) : ℂ :=
  Complex.exp (-(w - (σ : ℂ)) * (Real.log (q.1 : ℝ) : ℂ))

theorem feature_norm_sq (σ : ℝ) (w : ℂ) (q : Site) :
    ‖feature σ w q‖ ^ 2 = (q.1 : ℝ) ^ (-2 * (w.re - σ)) := by
  have hq : (0 : ℝ) < q.1 := Nat.cast_pos.mpr q.property.pos
  rw [feature, Complex.norm_exp, ← Real.exp_nat_mul, Real.rpow_def_of_pos hq]
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem feature_memℓp_iff (σ : ℝ) (w : ℂ) :
    Memℓp (feature σ w) 2 ↔ σ + 1 / 2 < w.re := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, feature_norm_sq, summable_rpow_iff]
  constructor <;> intro h <;> linarith

def FiniteBound {ι : Type*} (k : ι → ℂ) (C : ℝ) : Prop :=
  ∀ (S : Finset ι) (c : ι → ℂ),
    ‖∑ i ∈ S, c i * k i‖ ^ 2 ≤ C * ∑ i ∈ S, ‖c i‖ ^ 2

theorem finite_bound_of_summable {ι : Type*} (k : ι → ℂ)
    (hk : Summable (fun i => ‖k i‖ ^ 2)) :
    FiniteBound k (∑' i, ‖k i‖ ^ 2) := by
  intro S c
  have hn : ‖∑ i ∈ S, c i * k i‖ ≤ ∑ i ∈ S, ‖c i‖ * ‖k i‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun i => c i * k i)
  calc
    _ ≤ (∑ i ∈ S, ‖c i‖ * ‖k i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (∑ i ∈ S, ‖c i‖ ^ 2) * ∑ i ∈ S, ‖k i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖c i‖) (fun i => ‖k i‖)
    _ ≤ (∑ i ∈ S, ‖c i‖ ^ 2) * ∑' i, ‖k i‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hk.sum_le_tsum S (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

theorem summable_of_finite_bound {ι : Type*} (k : ι → ℂ) {C : ℝ}
    (h : FiniteBound k C) : Summable (fun i => ‖k i‖ ^ 2) := by
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := max C 0)
  intro S
  have hb := h S (fun i => star (k i))
  have hp (z : ℂ) : star z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [mul_comm]
    change z * (starRingEnd ℂ) z = _
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  simp only [norm_star] at hb
  simp_rw [hp] at hb
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hb
  have hn : 0 ≤ ∑ i ∈ S, ‖k i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : C ≤ max C 0 := le_max_left _ _
  have hz : 0 ≤ max C 0 := le_max_right _ _
  nlinarith

theorem exists_finite_bound_iff (σ : ℝ) (w : ℂ) :
    (∃ C : ℝ, FiniteBound (feature σ w) C) ↔ σ + 1 / 2 < w.re := by
  have he : Summable (fun q => ‖feature σ w q‖ ^ 2) ↔ σ + 1 / 2 < w.re := by
    simp only [feature_norm_sq, summable_rpow_iff]
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨C, hC⟩
    exact he.mp (summable_of_finite_bound _ hC)
  · intro hw
    exact ⟨_, finite_bound_of_summable _ (he.mpr hw)⟩

theorem no_finite_bound_at_boundary (σ : ℝ) (w : ℂ)
    (hw : w.re ≤ σ + 1 / 2) : ¬ ∃ C : ℝ, FiniteBound (feature σ w) C := by
  rw [exists_finite_bound_iff]
  exact not_lt.mpr hw
end RiemannResearch.Analysis.PrimePowerEvaluation

namespace RiemannResearch.Analysis.PrimePowerEvaluation
def vector (σ : ℝ) (w : ℂ) (hw : σ + 1 / 2 < w.re) :
    lp (fun _ : Site => ℂ) 2 :=
  ⟨feature σ w, (feature_memℓp_iff σ w).mpr hw⟩

theorem vector_norm_sq (σ : ℝ) (w : ℂ) (hw : σ + 1 / 2 < w.re) :
    ‖vector σ w hw‖ ^ 2 = ∑' q : Site, (q.1 : ℝ)^(-2 * (w.re - σ)) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (vector σ w hw)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, vector, feature_norm_sq] using h

theorem evaluation_hasSum (c : lp (fun _ : Site => ℂ) 2)
    (σ : ℝ) (w : ℂ) (hw : σ + 1 / 2 < w.re) :
    HasSum (fun q => c q * feature σ w q)
      (inner ℂ (star (vector σ w hw)) c) := by
  have he (q : Site) :
      inner ℂ (star (vector σ w hw) q) (c q) = c q * feature σ w q := by
    rw [RCLike.inner_apply']
    change star (star (feature σ w q)) * c q = _
    rw [star_star, mul_comm]
  simpa only [he] using lp.hasSum_inner (𝕜 := ℂ) (star (vector σ w hw)) c

theorem evaluation_bound (c : lp (fun _ : Site => ℂ) 2)
    (σ : ℝ) (w : ℂ) (hw : σ + 1 / 2 < w.re) :
    ‖∑' q, c q * feature σ w q‖ ^ 2 ≤
      ‖c‖ ^ 2 * ∑' q : Site, (q.1 : ℝ)^(-2 * (w.re - σ)) := by
  rw [(evaluation_hasSum c σ w hw).tsum_eq, ← vector_norm_sq σ w hw]
  have hi := norm_inner_le_norm (𝕜 := ℂ) (star (vector σ w hw)) c
  rw [norm_star] at hi
  calc
    _ ≤ (‖vector σ w hw‖ * ‖c‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = _ := by ring
end RiemannResearch.Analysis.PrimePowerEvaluation

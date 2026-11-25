import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A finite orthonormal subtraction for the two real parts of a complex functional -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LaguerreKernelTail

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The part left after subtracting the first K real orthonormal coordinates. -/
def kernelTail (v : ℕ → H) (K : ℕ) (x : H) : H :=
  x - ∑ j ∈ Finset.range K, inner ℝ (v j) x • v j

private theorem inner_partial_kernel (v : ℕ → H) (hv : Orthonormal ℝ v)
    (K : ℕ) (x : H) {i : ℕ} (hi : i ∈ Finset.range K) :
    inner ℝ (v i) (∑ j ∈ Finset.range K, inner ℝ (v j) x • v j) = inner ℝ (v i) x := by
  rw [inner_sum]
  simp_rw [real_inner_smul_right, orthonormal_iff_ite.mp hv]
  simp [hi]

/-- Subtract exactly the squared moduli of the removed real coordinates. -/
theorem kernelTail_energy (v : ℕ → H) (hv : Orthonormal ℝ v) (K : ℕ) (x : H) :
    ‖kernelTail v K x‖ ^ 2 = ‖x‖ ^ 2 -
      ∑ j ∈ Finset.range K, (inner ℝ (v j) x) ^ 2 := by
  let P := ∑ j ∈ Finset.range K, inner ℝ (v j) x • v j
  have hPx : inner ℝ P x = ∑ j ∈ Finset.range K, (inner ℝ (v j) x) ^ 2 := by
    simp only [P, sum_inner, real_inner_smul_left, pow_two]
  have hPP : ‖P‖ ^ 2 = ∑ j ∈ Finset.range K, (inner ℝ (v j) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (∑ j ∈ Finset.range K, inner ℝ (v j) x • v j) P = _
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, show inner ℝ (v i) P = _ from inner_partial_kernel v hv K x hi]
    ring
  change ‖x - P‖ ^ 2 = _
  have hxp : inner ℝ x P = ∑ j ∈ Finset.range K, (inner ℝ (v j) x) ^ 2 :=
    (real_inner_comm ..).trans hPx
  rw [norm_sub_sq_real, hxp, hPP]
  ring

/-- A matched real probe only pairs with the unmatched kernel tail. -/
theorem matched_inner_kernelTail (v : ℕ → H) (K : ℕ) (f x : H)
    (hf : ∀ i ∈ Finset.range K, inner ℝ f (v i) = 0) :
    inner ℝ f (kernelTail v K x) = inner ℝ f x := by
  rw [kernelTail, inner_sub_right, inner_sum]
  have hz : (∑ j ∈ Finset.range K, inner ℝ f (inner ℝ (v j) x • v j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [real_inner_smul_right, hf j hj, mul_zero]
  rw [hz, sub_zero]

private theorem real_inner_sq_le (f x : H) :
    (inner ℝ f x) ^ 2 ≤ ‖f‖ ^ 2 * ‖x‖ ^ 2 := by
  have h : |inner ℝ f x| ≤ ‖f‖ * ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f x
  simpa only [sq_abs, mul_pow] using
    pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Bound a complex transform of a real matched vector. Here x and y are the
real and imaginary kernels. The constant is the exact squared residual energy
of the two kernels in the real Hilbert space. -/
theorem matched_complex_kernel_sq_le (v : ℕ → H) (hv : Orthonormal ℝ v)
    (K : ℕ) (f x y : H) (hf : ∀ i ∈ Finset.range K, inner ℝ f (v i) = 0) :
    (inner ℝ f x) ^ 2 + (inner ℝ f y) ^ 2 ≤
      ‖f‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2 -
        ∑ j ∈ Finset.range K, ((inner ℝ (v j) x) ^ 2 + (inner ℝ (v j) y) ^ 2)) := by
  have hx := real_inner_sq_le f (kernelTail v K x)
  have hy := real_inner_sq_le f (kernelTail v K y)
  rw [matched_inner_kernelTail v K f x hf, kernelTail_energy v hv] at hx
  rw [matched_inner_kernelTail v K f y hf, kernelTail_energy v hv] at hy
  rw [Finset.sum_add_distrib]
  linarith only [hx, hy]

end RiemannResearch.Analysis.LaguerreKernelTail

import RiemannResearch.RH.ReciprocalChargeDilationArithmetic
import RiemannResearch.NumberTheory.QuotientKernelEnergyLimit

/-!
# The scalar energy limit for a pair of dilated reciprocal-charge kernels

The normalization constant h+1 is removed by the homogeneous kernel theorem.
Every hypothesis is provided by exact finite arithmetic identities, the elementary
reciprocal Möbius bound, and PNT. No RH-strength hypothesis is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.QuotientWindow

private theorem reciprocalSum_abs_le_one_for_dilation (M : ℕ) :
    |mobiusReciprocalSum M| ≤ 1 := by
  by_cases hM : M = 0
  · simp [hM, mobiusReciprocalSum]
  · exact mobiusReciprocalSum_abs_le_one M (Nat.pos_of_ne_zero hM)

/-- The same exact quotient-window identity holds for both dilation charges together. -/
theorem dilationMobiusKernel_window (h N d : ℕ) (hh : 0 < h) (hd : 0 < d) :
    dilationMobiusKernel h (N / d) - dilationMobiusKernel h (N / (d + 1)) =
      ∑ n ∈ window N d, dilationMobiusCoefficient h n := by
  have hab : N / (d + 1) ≤ N / d := by
    have haN := Nat.div_mul_le_self N (d + 1)
    apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith
  have hdis : Disjoint (Finset.Icc 1 (N / (d + 1))) (window N d) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [window, Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  have hu : Finset.Icc 1 (N / (d + 1)) ∪ window N d = Finset.Icc 1 (N / d) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with hn | hn
      · obtain ⟨hn0, hna⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨hn0, hna.trans hab⟩
      · have hnw : N / (d + 1) < n ∧ n ≤ N / d := Finset.mem_Ioc.mp hn
        exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hnw.1, hnw.2⟩
    · intro hn
      obtain ⟨hn0, hnb⟩ := Finset.mem_Icc.mp hn
      by_cases hna : n ≤ N / (d + 1)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hn0, hna⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hna, hnb⟩))
  rw [← dilationMobiusCoefficient_sum h (N / d) hh,
    ← dilationMobiusCoefficient_sum h (N / (d + 1)) hh,
    ← hu, Finset.sum_union hdis]
  ring

/-- The full scalar energy at cutoff M converges to the exact combined charge energy. -/
theorem dilationMobiusKernel_square_energy_tendsto (h : ℕ) (hh : 0 < h) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M,
      (k : ℝ) * ((k : ℝ) + 1) *
        (dilationMobiusKernel h (M / k) / (k : ℝ) -
          dilationMobiusKernel h (M / (k + 1)) / ((k : ℝ) + 1)) ^ 2)
      atTop (𝓝 (∑' n, dilationMobiusCoefficient h n ^ 2)) := by
  apply quotient_kernel_square_energy_tendsto_scaled
    (dilationMobiusKernel h) (dilationMobiusCoefficient h) ((h : ℝ) + 1)
    (by positivity) (dilationMobiusCoefficient_zero h)
  · intro n hn
    exact dilationMobiusCoefficient_abs_le h n hh hn
  · intro M
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
    calc
      |dilationMobiusKernel h M| ≤ |mobiusReciprocalSum M| +
          |mobiusReciprocalSum (M / h)| := abs_add_le _ _
      _ ≤ 2 := by linarith [reciprocalSum_abs_le_one_for_dilation M,
        reciprocalSum_abs_le_one_for_dilation (M / h)]
      _ ≤ (h : ℝ) + 1 := by linarith
  · exact dilationMobiusKernel_tendsto_zero h hh
  · intro N d hd
    exact dilationMobiusKernel_window h N d hh hd

end RiemannResearch.RH.Pareto

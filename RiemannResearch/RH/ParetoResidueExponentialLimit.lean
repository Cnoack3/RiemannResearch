import RiemannResearch.NumberTheory.DirichletExponential
import RiemannResearch.RH.ParetoPrimeLimitLegality
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The actual residue convolution exponential and its unit limit

Source: the user's Pareto convolution-exponential argument, 13 November 2026.
Coefficientwise convergence of the true infinite exponential is unconditional.
The Hilbert-space assembly below records the common square-summable envelope
as an explicit analytic input, to be supplied by the separate norm estimate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.DirichletExponential

/-- Finite Dirichlet powers preserve coefficientwise convergence. -/
theorem convolutionPower_tendsto
    (f : ℕ → ArithmeticFunction ℝ) (g : ArithmeticFunction ℝ)
    (hpoint : ∀ n, Tendsto (fun k => f k n) atTop (𝓝 (g n))) (r n : ℕ) :
    Tendsto (fun k => ((f k) ^ r) n) atTop (𝓝 ((g ^ r) n)) := by
  induction r generalizing n with
  | zero => simpa only [pow_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ArithmeticFunction ℝ) n)
        atTop (𝓝 ((1 : ArithmeticFunction ℝ) n)))
  | succ r ih =>
      simp only [pow_succ, ArithmeticFunction.mul_apply]
      exact tendsto_finsetSum _ fun d _ => (ih d.1).mul (hpoint d.2)

/-- Uniformly bounded arithmetic inputs permit passage of a coefficientwise
limit through the actual infinite Dirichlet exponential series. -/
theorem convolutionExp_tendsto_of_uniform_bound
    (f : ℕ → ArithmeticFunction ℝ) (g : ArithmeticFunction ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ k n, |f k n| ≤ C)
    (hpoint : ∀ n, Tendsto (fun k => f k n) atTop (𝓝 (g n))) (n : ℕ) :
    Tendsto (fun k => convolutionExp (f k) n) atTop
      (𝓝 (convolutionExp g n)) := by
  unfold convolutionExp
  apply tendsto_tsum_of_dominated_convergence
    (Real.summable_pow_div_factorial (C * ((n : ℝ) + 1)))
  · intro r
    exact (convolutionPower_tendsto f g hpoint r n).div_const (r.factorial : ℝ)
  · apply Filter.Eventually.of_forall
    intro k r
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show 0 ≤ (r.factorial : ℝ) from Nat.cast_nonneg _)]
    exact div_le_div_of_nonneg_right
      (convolutionPower_abs_le (f k) hC (hbound k) r n n le_rfl)
      (Nat.cast_nonneg _)

/-- The convolution exponential of zero is the Dirichlet unit. -/
@[simp] theorem convolutionExp_zero_input (n : ℕ) :
    convolutionExp (0 : ArithmeticFunction ℝ) n = if n = 1 then 1 else 0 := by
  calc
    convolutionExp (0 : ArithmeticFunction ℝ) n =
        (((0 : ArithmeticFunction ℝ) ^ 0) n) / (Nat.factorial 0 : ℝ) := by
      apply tsum_eq_single 0
      intro r hr
      simp [zero_pow hr]
    _ = _ := by simp [ArithmeticFunction.one_apply]

/-- Every fixed normalized residue coefficient tends to zero as its conductor
increases: eventually that coefficient is exactly n/k. -/
theorem residueAF_tendsto_zero (n : ℕ) :
    Tendsto (fun k => residueAF k n) atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)))
  have hn : Tendsto (fun k : ℕ => (n : ℝ) / (k : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (n : ℝ)
  apply hn.congr'
  filter_upwards [eventually_gt_atTop n] with k hk
  simp only [residueAF_apply, Nat.mod_eq_of_lt hk]

/-- The actual infinite residue convolution exponentials converge at every
coefficient to δ₁; no prime assumption or Hilbert input is used. -/
theorem residueAF_exp_tendsto_unit (n : ℕ) :
    Tendsto (fun k => convolutionExp (residueAF k) n) atTop
      (𝓝 (if n = 1 then (1 : ℝ) else 0)) := by
  simpa only [convolutionExp_zero_input] using
    convolutionExp_tendsto_of_uniform_bound residueAF (0 : ArithmeticFunction ℝ)
      (C := 1) (by norm_num) residueAF_abs_le_one
      (fun m => by simpa using residueAF_tendsto_zero m) n

/-- The unit coefficient is a lower bound for every residue exponential. -/
theorem residueAF_exp_unit_lower (k n : ℕ) :
    (if n = 1 then (1 : ℝ) else 0) ≤ convolutionExp (residueAF k) n := by
  have h := (residueAF_exp_summable k n).le_tsum 0 (fun r _ =>
    div_nonneg (convolutionPower_nonneg (residueAF k) (residueAF_nonneg k) r n)
      (Nat.cast_nonneg _))
  simpa only [convolutionExp, convolutionPower_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] using h

end RiemannResearch.NumberTheory.DirichletExponential

namespace RiemannResearch.RH.Pareto.ConvolutionExponential

open RiemannResearch.NumberTheory.DirichletExponential
open RiemannResearch.RH.ArithmeticCumulative

/-- The arithmetic input is exactly the existing physical normalized residue. -/
theorem residueAF_eq_residueFraction (k n : ℕ) :
    residueAF k n = residueFraction k n := rfl

/-- Exact identification with the already bundled physical Pareto atom. -/
theorem normalizedResidueHilbert_sequence_eq_residueAF (k : ℕ) (hk : 0 < k) :
    hilbertSequence (normalizedResidueHilbert k hk) = fun n => residueAF k n := by
  rw [normalizedResidueHilbert_sequence]
  rfl

/-- A common square-summable physical envelope puts every actual exponential
in the Pareto Hilbert space. -/
theorem residueAF_exp_square_summable {G : ℕ → ℝ}
    (hG : Summable (fun n => positiveWeight n * G n ^ 2))
    (hbound : ∀ k n, convolutionExp (residueAF k) n ≤ G n) (k : ℕ) :
    Summable (fun n => positiveWeight n * convolutionExp (residueAF k) n ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) _ hG
  intro n
  apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg n)
  have he : 0 ≤ convolutionExp (residueAF k) n :=
    convolutionExp_nonneg _ (residueAF_nonneg k) n
  have hb := hbound k n
  simpa only [pow_two] using mul_le_mul hb hb he (he.trans hb)

/-- The genuine exponential, embedded using its full infinite physical energy. -/
def residueExpHilbert (k : ℕ)
    (h : Summable (fun n => positiveWeight n * convolutionExp (residueAF k) n ^ 2)) :
    ThresholdHilbert :=
  sequenceHilbert (convolutionExp (residueAF k)) h

@[simp] theorem residueExpHilbert_sequence (k : ℕ)
    (h : Summable (fun n => positiveWeight n * convolutionExp (residueAF k) n ^ 2)) :
    hilbertSequence (residueExpHilbert k h) = convolutionExp (residueAF k) :=
  hilbertSequence_sequenceHilbert _ _ (convolutionExp_zero _)

/-- A common square-summable envelope upgrades the unconditional coefficient
limit to convergence in the actual complete Pareto Hilbert space. -/
theorem residueExpHilbert_tendsto_unit {G : ℕ → ℝ}
    (hG : Summable (fun n => positiveWeight n * G n ^ 2))
    (hbound : ∀ k n, convolutionExp (residueAF k) n ≤ G n) :
    Tendsto (fun k => residueExpHilbert k (residueAF_exp_square_summable hG hbound k))
      atTop (𝓝 (paretoPointHilbert 0)) := by
  apply tendsto_of_dominated_physical_coordinates _ _ G hG
  · intro n
    simpa only [residueExpHilbert_sequence, hilbertSequence_paretoPoint,
      paretoPointSequence, Nat.zero_add] using residueAF_exp_tendsto_unit n
  · intro k n
    simp only [residueExpHilbert_sequence, hilbertSequence_paretoPoint,
      paretoPointSequence, Nat.zero_add]
    have hδ : 0 ≤ (if n = 1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have hu := residueAF_exp_unit_lower k n
    have hb := hbound k n
    have hnonneg : 0 ≤ convolutionExp (residueAF k) n -
        (if n = 1 then (1 : ℝ) else 0) := sub_nonneg.mpr hu
    have hle : convolutionExp (residueAF k) n -
        (if n = 1 then (1 : ℝ) else 0) ≤ G n :=
      (sub_le_self _ hδ).trans hb
    simpa only [pow_two] using mul_le_mul hle hle hnonneg (hnonneg.trans hle)

end RiemannResearch.RH.Pareto.ConvolutionExponential

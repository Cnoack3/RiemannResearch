import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith

/-!
# Exact products of relative residual gains

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §8.3.
The report's residual is a *squared* Hilbert norm; `d` below denotes that
nonnegative scalar energy. The finite product identity is exact. Under strict
relative gains `0 ≤ r n < 1`, that energy tends to zero exactly when the gains
are not summable. No arithmetic lower bound on the actual gains is assumed or
claimed here.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ResidualGain

/-- Fraction of the initial residual left after the first `n` relative gains. -/
def survivalProduct (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (1 - r i)

@[simp] theorem survivalProduct_zero (r : ℕ → ℝ) : survivalProduct r 0 = 1 := by
  simp [survivalProduct]

theorem survivalProduct_succ (r : ℕ → ℝ) (n : ℕ) :
    survivalProduct r (n + 1) = survivalProduct r n * (1 - r n) := by
  simp [survivalProduct, Finset.prod_range_succ]

/-- The exact finite identity precedes any estimate of gains. -/
theorem recurrence_eq_mul_product {d r : ℕ → ℝ}
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) (n : ℕ) :
    d n = d 0 * survivalProduct r n := by
  induction n with
  | zero => simp
  | succ n ih => rw [hrec, ih, survivalProduct_succ, mul_assoc]

theorem survivalProduct_pos {r : ℕ → ℝ} (hr : ∀ n, r n < 1) (n : ℕ) :
    0 < survivalProduct r n := by
  apply Finset.prod_pos
  intro i _
  exact sub_pos.mpr (hr i)

theorem survivalProduct_nonneg {r : ℕ → ℝ} (hr : ∀ n, r n ≤ 1) (n : ℕ) :
    0 ≤ survivalProduct r n := by
  apply Finset.prod_nonneg
  intro i _
  exact sub_nonneg.mpr (hr i)

theorem survivalProduct_le_exp_neg_sum {r : ℕ → ℝ} (hr : ∀ n, r n ≤ 1)
    (n : ℕ) :
    survivalProduct r n ≤ Real.exp (-(∑ i ∈ Finset.range n, r i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [survivalProduct_succ, Finset.sum_range_succ, neg_add, Real.exp_add]
    apply mul_le_mul ih _ (sub_nonneg.mpr (hr n)) (Real.exp_nonneg _)
    have h := Real.add_one_le_exp (-r n)
    linarith

/-- Nonsummable nonnegative gains exhaust the residual. -/
theorem survivalProduct_tendsto_zero_of_not_summable {r : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n ≤ 1) (hs : ¬Summable r) :
    Tendsto (survivalProduct r) atTop (𝓝 0) := by
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg h0).mp hs
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (survivalProduct_nonneg h1) (survivalProduct_le_exp_neg_sum h1)

/-- For summable strict gains, the surviving fraction has an explicit positive
limit. This identity is stronger than just saying the residual stays nonzero. -/
theorem survivalProduct_tendsto_exp_log_of_summable {r : ℕ → ℝ}
    (h1 : ∀ n, r n < 1) (hs : Summable r) :
    Tendsto (survivalProduct r) atTop
      (𝓝 (Real.exp (∑' i, Real.log (1 - r i)))) := by
  have hlog : Summable (fun i => Real.log (1 - r i)) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable hs.neg
  exact (Real.hasProd_of_hasSum_log
    (fun i => sub_pos.mpr (h1 i)) hlog.hasSum).tendsto_prod_nat

/-- The complete gain-product criterion, with the no-finite-termination
hypothesis expressed by strict gains. -/
theorem survivalProduct_tendsto_zero_iff_not_summable {r : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n < 1) :
    Tendsto (survivalProduct r) atTop (𝓝 0) ↔ ¬Summable r := by
  constructor
  · intro hz hs
    have he := survivalProduct_tendsto_exp_log_of_summable h1 hs
    have hzero := tendsto_nhds_unique hz he
    exact (ne_of_gt (Real.exp_pos _)) hzero.symm
  · exact survivalProduct_tendsto_zero_of_not_summable h0
      (fun n => (h1 n).le)

/-- Consumer for any exact residual-gain recurrence, including the nested
orthogonal-projection residuals in the source report. -/
theorem residual_tendsto_zero_iff_not_summable {d r : ℕ → ℝ}
    (hd : 0 < d 0) (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) :
    Tendsto d atTop (𝓝 0) ↔ ¬Summable r := by
  have hformula := recurrence_eq_mul_product hrec
  constructor
  · intro hz hs
    have hp := survivalProduct_tendsto_exp_log_of_summable h1 hs
    have he : Tendsto d atTop
        (𝓝 (d 0 * Real.exp (∑' i, Real.log (1 - r i)))) := by
      have hh : Tendsto (fun n => d 0 * survivalProduct r n) atTop
          (𝓝 (d 0 * Real.exp (∑' i, Real.log (1 - r i)))) :=
        tendsto_const_nhds.mul hp
      exact hh.congr' (Filter.Eventually.of_forall (fun n => (hformula n).symm))
    have hzero := tendsto_nhds_unique hz he
    exact (ne_of_gt (mul_pos hd (Real.exp_pos _))) hzero.symm
  · intro hs
    have hp := survivalProduct_tendsto_zero_of_not_summable h0
      (fun n => (h1 n).le) hs
    have hh : Tendsto (fun n => d 0 * survivalProduct r n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hp :
        Tendsto (fun n => d 0 * survivalProduct r n) atTop (𝓝 (d 0 * 0)))
    exact hh.congr' (Filter.Eventually.of_forall (fun n => (hformula n).symm))

/-!
Source: user-provided argument, `RH_Controlled_Conductor_Schur_2026-09-10.md`, §7.
The logarithmic and additive forms below do not prove arithmetic gain divergence.
-/

/-- The additive version of the exact product identity: no gains or mixed
contributions are discarded. -/
theorem recurrence_eq_initial_sub_sum {d r : ℕ → ℝ}
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) (n : ℕ) :
    d n = d 0 - ∑ i ∈ Finset.range n, d i * r i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec, Finset.sum_range_succ]
    nlinarith

/-- Strict relative gains preserve positivity at every finite stage. -/
theorem recurrence_pos {d r : ℕ → ℝ} (hd : 0 < d 0)
    (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) (n : ℕ) :
    0 < d n := by
  rw [recurrence_eq_mul_product hrec n]
  exact mul_pos hd (survivalProduct_pos h1 n)

/-- Exact logarithmic accounting for the residual; this is an equality at
every finite scale. -/
theorem log_recurrence_eq_initial_sub_sum {d r : ℕ → ℝ} (hd : 0 < d 0)
    (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) (n : ℕ) :
    Real.log (d n) = Real.log (d 0) -
      ∑ i ∈ Finset.range n, -Real.log (1 - r i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec, Real.log_mul
      (ne_of_gt (recurrence_pos hd h1 hrec n))
      (ne_of_gt (sub_pos.mpr (h1 n))), Finset.sum_range_succ]
    linarith

/-- Each relative gain is bounded by its exact logarithmic gain. -/
theorem gain_le_neg_log_one_sub {t : ℝ} (ht : t < 1) :
    t ≤ -Real.log (1 - t) := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr ht)
  linarith

/-- Under strict nonnegative gains, the logarithmic gains and ordinary gains
are summable simultaneously. -/
theorem summable_neg_log_one_sub_iff {r : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n < 1) :
    Summable (fun n => -Real.log (1 - r n)) ↔ Summable r := by
  constructor
  · intro hs
    exact Summable.of_nonneg_of_le h0
      (fun n => gain_le_neg_log_one_sub (h1 n)) hs
  · intro hs
    have hlog := Real.summable_log_one_add_of_summable hs.neg
    simpa only [sub_eq_add_neg] using hlog.neg

/-- The two divergent-sum conditions in Section 7 are exactly equivalent.
Together with `residual_tendsto_zero_iff_not_summable`, this gives the complete
three-way criterion without a new arithmetic divergence assumption. -/
theorem log_gain_sum_tendsto_atTop_iff {r : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n < 1) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, -Real.log (1 - r n)) atTop atTop ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, r n) atTop atTop := by
  have hlog0 : ∀ n, 0 ≤ -Real.log (1 - r n) :=
    fun n => (h0 n).trans (gain_le_neg_log_one_sub (h1 n))
  calc
    _ ↔ ¬Summable (fun n => -Real.log (1 - r n)) :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg hlog0).symm
    _ ↔ ¬Summable r := not_congr (summable_neg_log_one_sub_iff h0 h1)
    _ ↔ _ := not_summable_iff_tendsto_nat_atTop_of_nonneg h0

end RiemannResearch.Analysis.ResidualGain

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real contractive product calculus

The intended RH consumer is Burnol's zero product in Theorem 1.2 of
J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann
Hypothesis*, arXiv:math/9910055, https://arxiv.org/abs/math/9910055.

The results here are elementary product calculus, independently formalized
to support that application. They do not establish the analytic identification
of a projection norm with Burnol's zero product. In particular, convergence
of logarithms, where used below, is an explicit hypothesis.

Cutoff products are used rather than a totalized infinite product, so the
statements remain explicit about the existence and value of limits.
-/

open scoped BigOperators Topology
open Filter

namespace Real

/-- The product of the first `N` factors. Repeated indices encode multiplicity. -/
noncomputable def partialProduct (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, a k

@[simp] theorem partialProduct_zero (a : ℕ → ℝ) : partialProduct a 0 = 1 := by
  simp [partialProduct]

theorem partialProduct_succ (a : ℕ → ℝ) (N : ℕ) :
    partialProduct a (N + 1) = partialProduct a N * a N := by
  simp [partialProduct, Finset.prod_range_succ]

theorem one_sub_partialProduct_succ (a : ℕ → ℝ) (N : ℕ) :
    1 - partialProduct a (N + 1) =
      (1 - partialProduct a N) + partialProduct a N * (1 - a N) := by
  rw [partialProduct_succ]
  ring

/-- The exact defect telescope; no sign or convergence assumptions are needed. -/
theorem one_sub_partialProduct_eq_sum (a : ℕ → ℝ) (N : ℕ) :
    1 - partialProduct a N =
      ∑ k ∈ Finset.range N, partialProduct a k * (1 - a k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih, one_sub_partialProduct_succ]

theorem partialProduct_nonneg (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (N : ℕ) :
    0 ≤ partialProduct a N := by
  exact Finset.prod_nonneg fun k _ => ha k

theorem partialProduct_succ_le (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) (N : ℕ) :
    partialProduct a (N + 1) ≤ partialProduct a N := by
  rw [partialProduct_succ]
  exact mul_le_of_le_one_right (partialProduct_nonneg a ha0 N) (ha1 N)

theorem partialProduct_antitone (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) :
    Antitone (partialProduct a) := by
  exact antitone_nat_of_succ_le (partialProduct_succ_le a ha0 ha1)

theorem partialProduct_le_one (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) (N : ℕ) :
    partialProduct a N ≤ 1 := by
  simpa using partialProduct_antitone a ha0 ha1 (Nat.zero_le N)

theorem partialProduct_le_factor (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {k N : ℕ} (hk : k < N) : partialProduct a N ≤ a k := by
  calc
    partialProduct a N ≤ partialProduct a (k + 1) :=
      partialProduct_antitone a ha0 ha1 (Nat.succ_le_iff.mpr hk)
    _ = partialProduct a k * a k := partialProduct_succ a k
    _ ≤ 1 * a k := mul_le_mul_of_nonneg_right (partialProduct_le_one a ha0 ha1 k)
      (ha0 k)
    _ = a k := one_mul _

/-- Every sequence of factors in `[0,1]` has a cutoff-product limit. -/
theorem tendsto_partialProduct_iInf (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) :
    Tendsto (partialProduct a) atTop (𝓝 (⨅ N, partialProduct a N)) := by
  apply tendsto_atTop_ciInf (partialProduct_antitone a ha0 ha1)
  refine ⟨0, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact partialProduct_nonneg a ha0 N

theorem partialProduct_limit_le_factor (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) (k : ℕ) :
    L ≤ a k := by
  apply le_of_tendsto hL
  filter_upwards [eventually_ge_atTop (k + 1)] with N hN
  exact partialProduct_le_factor a ha0 ha1 (lt_of_lt_of_le (Nat.lt_succ_self k) hN)

theorem partialProduct_limit_lt_one (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L))
    {k : ℕ} (hk : a k < 1) : L < 1 := by
  exact lt_of_le_of_lt (partialProduct_limit_le_factor a ha0 ha1 hL k) hk

/-- A contractive cutoff product tends to one exactly when every factor is one. -/
theorem tendsto_partialProduct_one_iff (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) :
    Tendsto (partialProduct a) atTop (𝓝 1) ↔ ∀ k, a k = 1 := by
  constructor
  · intro h k
    exact le_antisymm (ha1 k) (partialProduct_limit_le_factor a ha0 ha1 h k)
  · intro h
    have hfun : partialProduct a = fun _ => 1 := by
      funext N
      simp [partialProduct, h]
    rw [hfun]
    exact tendsto_const_nhds

/-- The finite defect telescope passes to limits without sign hypotheses. -/
theorem tendsto_partialProduct_defect_sums (a : ℕ → ℝ)
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, partialProduct a k * (1 - a k))
      atTop (𝓝 (1 - L)) := by
  simpa only [← one_sub_partialProduct_eq_sum] using
    (tendsto_const_nhds.sub hL :
      Tendsto (fun N => 1 - partialProduct a N) atTop (𝓝 (1 - L)))

/-- For contractive factors the infinite weighted defect sum equals the lost product mass. -/
theorem hasSum_partialProduct_defects (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) :
    HasSum (fun k => partialProduct a k * (1 - a k)) (1 - L) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => mul_nonneg (partialProduct_nonneg a ha0 k) (sub_nonneg.mpr (ha1 k)))
    (1 - L)).2
  exact tendsto_partialProduct_defect_sums a hL

theorem tsum_partialProduct_defects (a : ℕ → ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) :
    ∑' k, partialProduct a k * (1 - a k) = 1 - L :=
  (hasSum_partialProduct_defects a ha0 ha1 hL).tsum_eq

/-- The constant sequence records the contribution of a repeated zero. -/
theorem partialProduct_const (a : ℝ) (N : ℕ) :
    partialProduct (fun _ => a) N = a ^ N := by
  simp [partialProduct]

/-- An exact finite multiplicity formula. -/
theorem one_sub_pow_eq_mul_sum (a : ℝ) (m : ℕ) :
    1 - a ^ m = (1 - a) * ∑ k ∈ Finset.range m, a ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Finset.sum_range_succ]
      calc
        1 - a ^ m * a = (1 - a ^ m) + a ^ m * (1 - a) := by ring
        _ = (1 - a) * (∑ k ∈ Finset.range m, a ^ k) + a ^ m * (1 - a) := by
          rw [ih]
        _ = (1 - a) * ((∑ k ∈ Finset.range m, a ^ k) + a ^ m) := by ring

theorem partialProduct_pow (a : ℕ → ℝ) (m N : ℕ) :
    partialProduct (fun k => a k ^ m) N = partialProduct a N ^ m := by
  induction N with
  | zero => simp
  | succ N ih => rw [partialProduct_succ, partialProduct_succ, ih, mul_pow]

/-- The finite logarithmic identity requires positive factors. -/
theorem partialProduct_eq_exp_sum_log (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (N : ℕ) :
    partialProduct a N = Real.exp (∑ k ∈ Finset.range N, Real.log (a k)) := by
  unfold partialProduct
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun k _ => (Real.exp_log (ha k)).symm

/-- Summability of logarithms supplies an exact, positive product limit. -/
theorem tendsto_partialProduct_exp_tsum_log (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hs : Summable (fun k => Real.log (a k))) :
    Tendsto (partialProduct a) atTop (𝓝 (Real.exp (∑' k, Real.log (a k)))) := by
  have hsum := hs.hasSum.tendsto_sum_nat
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hsum
  have hfun : partialProduct a =
      fun N => Real.exp (∑ k ∈ Finset.range N, Real.log (a k)) := by
    funext N
    exact partialProduct_eq_exp_sum_log a ha N
  rw [hfun]
  exact hexp

theorem partialProduct_limit_eq_exp_tsum_log (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hs : Summable (fun k => Real.log (a k)))
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) :
    L = Real.exp (∑' k, Real.log (a k)) := by
  exact tendsto_nhds_unique hL (tendsto_partialProduct_exp_tsum_log a ha hs)

theorem partialProduct_limit_pos_of_summable_log (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hs : Summable (fun k => Real.log (a k)))
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) : 0 < L := by
  rw [partialProduct_limit_eq_exp_tsum_log a ha hs hL]
  exact Real.exp_pos _

theorem log_partialProduct_limit_eq_tsum_log (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hs : Summable (fun k => Real.log (a k)))
    {L : ℝ} (hL : Tendsto (partialProduct a) atTop (𝓝 L)) :
    Real.log L = ∑' k, Real.log (a k) := by
  rw [partialProduct_limit_eq_exp_tsum_log a ha hs hL, Real.log_exp]

end Real

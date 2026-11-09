import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.Analysis.ClosedInvariantCalculus
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Global logarithmic floor dilations in the Pareto Hilbert space

The normalized dilation U_m = D_m / sqrt(m) is an isometry, where
D_m f(n) = m f(floor(n/m)). For s > 1 we construct, in operator norm,

  globalLog s = sum_{m >= 2} (Lambda(m)/log(m)) m^(-s) U_m.

Thus globalLog (sigma + 1/2) is the Dirichlet-convolution logarithm
sum (Lambda(m)/log(m)) m^(-sigma) T_m for unscaled floor dilation T_m.
This is NOT the Banach-algebra logarithm of the single operator T_m.

All terms preserve the actual legal closed space. At s = 2, a finite
telescoping majorant proves norm <= 3/4, so I - globalLog 2 has a
convergent Neumann inverse preserving that space in both directions.
The full source scalar is constructed by a convergent arithmetic sum;
no Euler-product or numerical zeta estimate is assumed.

Provenance: the full-conductor Ramanujan/logarithm research agenda, combined
with ThresholdHilbertDilation, MobiusResidualFirstCoordinate, and
ClosedInvariantCalculus. This module makes no density or RH claim.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.GlobalLogDilation
open CoefficientStabilization
open RiemannResearch.Analysis.ClosedInvariantCalculus

def logWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n + 2) / Real.log (n + 2 : ℕ)

theorem logWeight_nonneg (n : ℕ) : 0 ≤ logWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega)))

theorem logWeight_le_one (n : ℕ) : logWeight n ≤ 1 := by
  apply (div_le_one (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega)))).mpr
  exact ArithmeticFunction.vonMangoldt_le_log

def normalizedDilation (n : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertNormalizedDilation (n + 2) (by omega)).toContinuousLinearMap

theorem normalizedDilation_norm_le (n : ℕ) : ‖normalizedDilation n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖hilbertNormalizedDilation (n + 2) _ f‖ ≤ 1 * ‖f‖
  exact le_of_eq ((hilbertNormalizedDilation (n + 2) (by omega)).norm_map f |>.trans (one_mul ‖f‖).symm)

def logTerm (s : ℝ) (n : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s)) • normalizedDilation n

theorem logTerm_norm_le (s : ℝ) (n : ℕ) :
    ‖logTerm s n‖ ≤ ((n + 2 : ℕ) : ℝ) ^ (-s) := by
  rw [logTerm, norm_smul, Real.norm_of_nonneg
    (mul_nonneg (logWeight_nonneg n) (Real.rpow_nonneg (by positivity) _))]
  calc
    logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s) * ‖normalizedDilation n‖
        ≤ logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s) * 1 :=
      mul_le_mul_of_nonneg_left (normalizedDilation_norm_le n)
        (mul_nonneg (logWeight_nonneg n) (Real.rpow_nonneg (by positivity) _))
    _ ≤ ((n + 2 : ℕ) : ℝ) ^ (-s) := by
      simpa using mul_le_mul_of_nonneg_right (logWeight_le_one n)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ)) (-s))

theorem summable_logTerm_norm {s : ℝ} (hs : 1 < s) :
    Summable (fun n => ‖logTerm s n‖) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (logTerm_norm_le s) ((summable_nat_add_iff 2).mpr hp)

theorem summable_logTerm {s : ℝ} (hs : 1 < s) : Summable (logTerm s) :=
  (summable_logTerm_norm hs).of_norm

def globalLog (s : ℝ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ∑' n, logTerm s n

theorem globalLog_partial_tendsto {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, logTerm s n) atTop (𝓝 (globalLog s)) :=
  (summable_logTerm hs).hasSum.tendsto_sum_nat

theorem logTerm_mem_invariantAlgebra (s : ℝ) (n : ℕ) :
    logTerm s n ∈ invariantAlgebra closedSpace := by
  intro f hf
  change (logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s)) •
    ((1 / Real.sqrt (n + 2 : ℕ)) • hilbertDilation (n + 2) (by omega) f) ∈ closedSpace
  exact closedSpace.smul_mem _ (closedSpace.smul_mem _ (closedSpace_dilation hf _ _))

theorem globalLog_mem_invariantAlgebra (s : ℝ) :
    globalLog s ∈ invariantAlgebra closedSpace :=
  tsum_mem_invariantAlgebra closedSpace isClosed_closure (logTerm_mem_invariantAlgebra s)

theorem logTerm_inner_one (s : ℝ) (n : ℕ) (f : ThresholdHilbert) :
    inner ℝ (logTerm s n f) hilbertOne =
      (logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s) / Real.sqrt (n + 2 : ℕ)) *
        inner ℝ f hilbertOne := by
  change inner ℝ ((logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s)) •
    ((1 / Real.sqrt (n + 2 : ℕ)) • hilbertDilation (n + 2) (by omega) f)) hilbertOne = _
  rw [real_inner_smul_left, real_inner_smul_left, hilbert_inner_one,
    hilbertDilation_mean, ← hilbert_inner_one]
  ring


def meanTerm (s : ℝ) (n : ℕ) : ℝ :=
  logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s) / Real.sqrt (n + 2 : ℕ)
def meanFactor (s : ℝ) : ℝ := inner ℝ (globalLog s hilbertOne) hilbertOne

theorem reciprocal_square_partial_bound (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n + 2 : ℕ) : ℝ) ^ 2) ≤
      3 / 4 - (3 / 2) / ((N + 2 : ℕ) : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hm : (2 : ℝ) ≤ (N + 2 : ℕ) := by exact_mod_cast (show 2 ≤ N + 2 by omega)
    have ht : (1 : ℝ) / ((N + 2 : ℕ) : ℝ) ^ 2 ≤
        (3 / 2) / ((N + 2 : ℕ) : ℝ) - (3 / 2) / ((N + 3 : ℕ) : ℝ) := by
      have ha : (0 : ℝ) < (N + 2 : ℕ) := by positivity
      have hb : (0 : ℝ) < (N + 3 : ℕ) := by positivity
      apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
      field_simp
      push_cast at hm ⊢
      nlinarith
    have he : N + 1 + 2 = N + 3 := by omega
    simp only [he]
    linarith

theorem globalLog_hasSum_inner {s : ℝ} (hs : 1 < s) (f : ThresholdHilbert) :
    HasSum (fun n => inner ℝ (logTerm s n f) hilbertOne)
      (inner ℝ (globalLog s f) hilbertOne) := by
  have h := (innerSL ℝ hilbertOne).hasSum
    ((ContinuousLinearMap.apply ℝ ThresholdHilbert f).hasSum (summable_logTerm hs).hasSum)
  change HasSum (fun n => inner ℝ hilbertOne (logTerm s n f))
    (inner ℝ hilbertOne (globalLog s f)) at h
  simpa only [real_inner_comm] using h

theorem meanTerm_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (meanTerm s) (meanFactor s) := by
  change HasSum (fun n => logWeight n * ((n + 2 : ℕ) : ℝ) ^ (-s) /
    Real.sqrt (n + 2 : ℕ)) (inner ℝ (globalLog s hilbertOne) hilbertOne)
  simpa only [logTerm_inner_one, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    mul_one, meanTerm, meanFactor] using globalLog_hasSum_inner hs hilbertOne

theorem globalLog_inner_one {s : ℝ} (hs : 1 < s) (f : ThresholdHilbert) :
    inner ℝ (globalLog s f) hilbertOne = meanFactor s * inner ℝ f hilbertOne := by
  have h : HasSum (fun n => meanTerm s n * inner ℝ f hilbertOne)
      (inner ℝ (globalLog s f) hilbertOne) := by
    simpa only [meanTerm, logTerm_inner_one] using globalLog_hasSum_inner hs f
  exact h.unique ((meanTerm_hasSum hs).mul_right _)

theorem globalLog_two_norm_le : ‖globalLog 2‖ ≤ 3 / 4 := by
  have hN (N : ℕ) : ‖∑ n ∈ Finset.range N, logTerm 2 n‖ ≤ (3 : ℝ) / 4 := by
    calc
      ‖∑ n ∈ Finset.range N, logTerm 2 n‖
          ≤ ∑ n ∈ Finset.range N, ‖logTerm 2 n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ)),
          Real.rpow_two, one_div] using logTerm_norm_le 2 n
      _ ≤ 3 / 4 - (3 / 2) / ((N + 2 : ℕ) : ℝ) := reciprocal_square_partial_bound N
      _ ≤ 3 / 4 := sub_le_self _ (by positivity)
  exact le_of_tendsto (globalLog_partial_tendsto (by norm_num : (1 : ℝ) < 2)).norm
    (Eventually.of_forall hN)

theorem globalLog_two_norm_lt_one : ‖globalLog 2‖ < 1 := by
  linarith [globalLog_two_norm_le]

def logFilter : ThresholdHilbert →L[ℝ] ThresholdHilbert := 1 - globalLog 2

def logFilterInverse : ThresholdHilbert →L[ℝ] ThresholdHilbert := neumann (globalLog 2)

theorem logFilter_mul_inverse : logFilter * logFilterInverse = 1 :=
  one_sub_mul_neumann (summable_geometric_of_norm_lt_one globalLog_two_norm_lt_one)

theorem logFilter_inverse_mul : logFilterInverse * logFilter = 1 :=
  neumann_mul_one_sub (summable_geometric_of_norm_lt_one globalLog_two_norm_lt_one)

theorem logFilter_mem_iff (f : ThresholdHilbert) :
    logFilter f ∈ closedSpace ↔ f ∈ closedSpace :=
  one_sub_apply_mem_iff closedSpace isClosed_closure (globalLog_mem_invariantAlgebra 2)
    (summable_geometric_of_norm_lt_one globalLog_two_norm_lt_one) f

theorem logFilter_inner_one (f : ThresholdHilbert) :
    inner ℝ (logFilter f) hilbertOne = (1 - meanFactor 2) * inner ℝ f hilbertOne := by
  change inner ℝ (f - globalLog 2 f) hilbertOne = _
  rw [inner_sub_left, globalLog_inner_one (by norm_num : (1 : ℝ) < 2)]
  ring


/-- A uniform bound on the complete global operator applied to any vector. -/
theorem globalLog_two_apply_norm_le (f : ThresholdHilbert) :
    ‖globalLog 2 f‖ ≤ (3 / 4) * ‖f‖ :=
  ((globalLog 2).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right globalLog_two_norm_le (norm_nonneg f))

theorem logFilter_norm_lower (f : ThresholdHilbert) :
    (1 / 4) * ‖f‖ ≤ ‖logFilter f‖ := by
  have htri := norm_add_le (logFilter f) (globalLog 2 f)
  have he : logFilter f + globalLog 2 f = f := by
    change (f - globalLog 2 f) + globalLog 2 f = f
    exact sub_add_cancel _ _
  rw [he] at htri
  linarith [globalLog_two_apply_norm_le f]

theorem logFilter_norm_upper (f : ThresholdHilbert) :
    ‖logFilter f‖ ≤ (7 / 4) * ‖f‖ := by
  have htri := norm_sub_le f (globalLog 2 f)
  change ‖f - globalLog 2 f‖ ≤ _
  linarith [globalLog_two_apply_norm_le f]

/-- The source multiplier cannot vanish. -/
theorem logFilter_source_factor_pos : 0 < 1 - meanFactor 2 := by
  have h1 : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have h := real_inner_le_norm (globalLog 2 hilbertOne) hilbertOne
  rw [h1, mul_one] at h
  have hb := globalLog_two_apply_norm_le hilbertOne
  rw [h1, mul_one] at hb
  change 0 < 1 - inner ℝ (globalLog 2 hilbertOne) hilbertOne
  linarith

/-- User-facing damping parameter: sigma is the exponent on floor dilation.
The internal parameter s is sigma + 1/2, because normalized dilation is used. -/
def floorLog (σ : ℝ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  globalLog (σ + 1 / 2)

theorem floorLog_partial_tendsto {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, logTerm (σ + 1 / 2) n) atTop
      (𝓝 (floorLog σ)) :=
  globalLog_partial_tendsto (by linarith)

end RiemannResearch.RH.Pareto.GlobalLogDilation

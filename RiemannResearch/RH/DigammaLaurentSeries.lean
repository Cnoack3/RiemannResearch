import RiemannResearch.RH.DigammaSmallArgument
import RiemannResearch.RH.ParetoZetaSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# All-order Laurent truncations of the actual digamma function

Each truncation has a literal positive convergent rational-series remainder.
For 0 < z < 1 the error tends to zero geometrically; thus the small-argument
Laurent series is a convergent identity for the Gamma logarithmic derivative,
not a divergent large-argument Bernoulli expansion.  The convergent
coefficient formula is NIST DLMF 5.7.4 (https://dlmf.nist.gov/5.7.E4).
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.DigammaSmallArgument

noncomputable section

def laurentRemainderTerm (z : ℝ) (N n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ (N + 1) * ((n : ℝ) + 1 + z))

def laurentRemainder (z : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, laurentRemainderTerm z N n

def laurentTerm (z : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * z ^ (k + 1) * positivePSeries (k + 2)

theorem laurentRemainderTerm_pos {z : ℝ} (hz : 0 < z) (N n : ℕ) :
    0 < laurentRemainderTerm z N n := by unfold laurentRemainderTerm; positivity

theorem laurentRemainderTerm_le {z : ℝ} (hz : 0 < z) (N n : ℕ) :
    laurentRemainderTerm z N n ≤ 1 / (((n : ℝ) + 1) ^ (N + 2)) := by
  unfold laurentRemainderTerm
  apply one_div_le_one_div_of_le (by positivity)
  rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem summable_laurentRemainderTerm {z : ℝ} (hz : 0 < z) (N : ℕ) :
    Summable (laurentRemainderTerm z N) := by
  exact (positivePSeries_summable (N + 2) (by omega)).of_nonneg_of_le
    (fun n => (laurentRemainderTerm_pos hz N n).le) (laurentRemainderTerm_le hz N)

theorem laurentRemainder_pos {z : ℝ} (hz : 0 < z) (N : ℕ) :
    0 < laurentRemainder z N := by
  exact (summable_laurentRemainderTerm hz N).tsum_pos
    (fun n => (laurentRemainderTerm_pos hz N n).le) 0
      (laurentRemainderTerm_pos hz N 0)

theorem laurentRemainder_le_coefficient {z : ℝ} (hz : 0 < z) (N : ℕ) :
    laurentRemainder z N ≤ positivePSeries (N + 2) := by
  exact Summable.tsum_le_tsum (laurentRemainderTerm_le hz N)
    (summable_laurentRemainderTerm hz N) (positivePSeries_summable (N + 2) (by omega))

theorem positivePSeries_le_two (N : ℕ) : positivePSeries (N + 2) ≤ positivePSeries 2 := by
  exact Summable.tsum_le_tsum
    (fun n => one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg n (α := ℝ)]) (by omega)))
    (positivePSeries_summable (N + 2) (by omega)) (positivePSeries_summable 2 le_rfl)

theorem laurentRemainder_le_two {z : ℝ} (hz : 0 < z) (N : ℕ) :
    laurentRemainder z N ≤ positivePSeries 2 :=
  (laurentRemainder_le_coefficient hz N).trans (positivePSeries_le_two N)

theorem laurentRemainderTerm_recurrence {z : ℝ} (hz : 0 < z) (N n : ℕ) :
    laurentRemainderTerm z N n = 1 / (((n : ℝ) + 1) ^ (N + 2)) -
      z * laurentRemainderTerm z (N + 1) n := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 + z ≠ 0 := by positivity
  unfold laurentRemainderTerm
  rw [show N + 1 + 1 = N + 2 by omega,
    show N + 2 = (N + 1) + 1 by omega, pow_succ]
  field_simp
  ring

theorem laurentRemainder_recurrence {z : ℝ} (hz : 0 < z) (N : ℕ) :
    laurentRemainder z N = positivePSeries (N + 2) -
      z * laurentRemainder z (N + 1) := by
  have hs := (positivePSeries_summable (N + 2) (by omega)).hasSum.sub
    ((summable_laurentRemainderTerm hz (N + 1)).hasSum.mul_left z)
  have he : (fun n : ℕ =>
      1 / (((n : ℝ) + 1) ^ (N + 2)) - z * laurentRemainderTerm z (N + 1) n) =
      laurentRemainderTerm z N := by
    funext n
    exact (laurentRemainderTerm_recurrence hz N n).symm
  rw [he] at hs
  exact (summable_laurentRemainderTerm hz N).hasSum.unique hs

theorem digamma_regular_part_eq_remainder_zero {z : ℝ} (hz : 0 < z) :
    (Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z =
      z * laurentRemainder z 0 := by
  have hs := (hasSum_reciprocal_difference_positive
    (show 0 < z + 1 by positivity)).neg
  have hd := re_digamma_add_one hz
  have ht := (summable_laurentRemainderTerm hz 0).hasSum.mul_left z
  have he : (fun n : ℕ => z * laurentRemainderTerm z 0 n) =
      (fun n : ℕ => -(1 / ((n : ℝ) + (z + 1)) - 1 / ((n : ℝ) + 1))) := by
    funext n
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + z ≠ 0 := by positivity
    unfold laurentRemainderTerm
    norm_num only [zero_add, pow_one]
    field_simp
    ring
  rw [he] at ht
  have hv := ht.unique hs
  change z * laurentRemainder z 0 =
    -(-(Complex.digamma ((z + 1 : ℝ) : ℂ)).re - Real.eulerMascheroniConstant) at hv
  linarith

/-- Every finite Laurent truncation, with its exact signed remainder. -/
theorem digamma_laurent_truncation {z : ℝ} (hz : 0 < z) (N : ℕ) :
    (Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z =
      (∑ k ∈ Finset.range N, laurentTerm z k) +
      (-1 : ℝ) ^ N * z ^ (N + 1) * laurentRemainder z N := by
  induction N with
  | zero => simpa using digamma_regular_part_eq_remainder_zero hz
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rw [ih, laurentRemainder_recurrence hz N]
    unfold laurentTerm
    simp only [pow_succ]
    ring

/-- The error has the sign of the first omitted Laurent term and is bounded
by that term's absolute coefficient. -/
theorem digamma_laurent_signed_error {z : ℝ} (hz : 0 < z) (N : ℕ) :
    0 < (-1 : ℝ) ^ N *
      (((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) -
        (∑ k ∈ Finset.range N, laurentTerm z k)) ∧
    (-1 : ℝ) ^ N *
      (((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) -
        (∑ k ∈ Finset.range N, laurentTerm z k)) ≤
      z ^ (N + 1) * positivePSeries (N + 2) := by
  have hs : (-1 : ℝ) ^ N * (-1 : ℝ) ^ N = 1 := by
    rw [← mul_pow]
    norm_num
  have he : (-1 : ℝ) ^ N *
      (((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) -
        (∑ k ∈ Finset.range N, laurentTerm z k)) =
      z ^ (N + 1) * laurentRemainder z N := by
    rw [digamma_laurent_truncation hz N, add_sub_cancel_left]
    calc
      _ = ((-1 : ℝ) ^ N * (-1 : ℝ) ^ N) * z ^ (N + 1) *
        laurentRemainder z N := by ring
      _ = _ := by rw [hs]; ring
  rw [he]
  exact ⟨mul_pos (pow_pos hz _) (laurentRemainder_pos hz N),
    mul_le_mul_of_nonneg_left (laurentRemainder_le_coefficient hz N) (by positivity)⟩

/-- A single geometric bound usable uniformly over all truncation orders. -/
theorem digamma_laurent_error_bound {z : ℝ} (hz : 0 < z) (N : ℕ) :
    |((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) -
      (∑ k ∈ Finset.range N, laurentTerm z k)| ≤
        z ^ (N + 1) * positivePSeries 2 := by
  rw [digamma_laurent_truncation hz N, add_sub_cancel_left]
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hz _), abs_of_pos (laurentRemainder_pos hz N)]
  exact mul_le_mul_of_nonneg_left (laurentRemainder_le_two hz N) (by positivity)

theorem summable_norm_laurentTerm {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    Summable (fun k : ℕ => ‖laurentTerm z k‖) := by
  have hnorm : ‖z‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hz]
  have hs := (summable_geometric_of_norm_lt_one hnorm).mul_left
    (z * positivePSeries 2)
  apply hs.of_nonneg_of_le (fun k => norm_nonneg _) ?_
  intro k
  have hp : 0 < positivePSeries (k + 2) :=
    positivePSeries_pos (k + 2) (by omega)
  have hn : ‖laurentTerm z k‖ = z ^ (k + 1) * positivePSeries (k + 2) := by
    unfold laurentTerm
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Real.norm_eq_abs, abs_of_pos hz,
      Real.norm_eq_abs, abs_of_pos hp]
  rw [hn]
  calc
    _ ≤ z ^ (k + 1) * positivePSeries 2 :=
      mul_le_mul_of_nonneg_left (positivePSeries_le_two k) (by positivity)
    _ = (z * positivePSeries 2) * z ^ k := by rw [pow_succ]; ring

/-- The full small-argument Laurent series converges to the actual digamma
regular part on 0 < z < 1. -/
theorem hasSum_digamma_laurent {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (laurentTerm z)
      ((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (show |z| < 1 by rwa [abs_of_pos hz])
  have hg : Tendsto (fun N : ℕ => z ^ (N + 1) * positivePSeries 2)
      atTop (𝓝 0) := by
    convert hp.mul_const (z * positivePSeries 2) using 1
    · funext N
      rw [pow_succ]
      ring
    · simp
  have he : Tendsto (fun N : ℕ =>
      |((Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z) -
        (∑ k ∈ Finset.range N, laurentTerm z k)|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun N => abs_nonneg _) (digamma_laurent_error_bound hz)
  apply (summable_norm_laurentTerm hz hz1).of_norm.hasSum_iff_tendsto_nat.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, abs_sub_comm] using he

/-- Exact convergent Laurent series with the pole and Euler constant visible. -/
theorem digamma_eq_laurent_tsum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (Complex.digamma (z : ℂ)).re =
      -Real.eulerMascheroniConstant - 1 / z + ∑' k : ℕ, laurentTerm z k := by
  have h := (hasSum_digamma_laurent hz hz1).tsum_eq
  linarith

/-- The actual Riemann zeta values are the Laurent coefficients, including
the odd coefficients. -/
theorem digamma_laurent_truncation_zeta {z : ℝ} (hz : 0 < z) (N : ℕ) :
    (Complex.digamma (z : ℂ)).re + Real.eulerMascheroniConstant + 1 / z =
      (∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * z ^ (k + 1) * (riemannZeta ((k + 2 : ℕ) : ℂ)).re) +
      (-1 : ℝ) ^ N * z ^ (N + 1) * laurentRemainder z N := by
  have he : (∑ k ∈ Finset.range N, laurentTerm z k) =
      ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * z ^ (k + 1) * (riemannZeta ((k + 2 : ℕ) : ℂ)).re := by
    apply Finset.sum_congr rfl
    intro k _
    unfold laurentTerm
    rw [positivePSeries_eq_zeta_re (k + 2) (by omega)]
  rw [← he]
  exact digamma_laurent_truncation hz N

/-- A full convergent digamma–zeta Laurent identity on the positive unit interval. -/
theorem digamma_eq_zeta_laurent_tsum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (Complex.digamma (z : ℂ)).re = -Real.eulerMascheroniConstant - 1 / z +
      ∑' k : ℕ, (-1 : ℝ) ^ k * z ^ (k + 1) *
        (riemannZeta ((k + 2 : ℕ) : ℂ)).re := by
  rw [digamma_eq_laurent_tsum hz hz1]
  congr 1
  apply tsum_congr
  intro k
  unfold laurentTerm
  rw [positivePSeries_eq_zeta_re (k + 2) (by omega)]

def crtLaurentTerm (Q r : ℕ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (((r : ℝ) + 1) ^ (k + 1) - (r : ℝ) ^ (k + 1)) *
    positivePSeries (k + 2) / (Q : ℝ) ^ (k + 2)

/-- The full convergent fixed-residue CRT Laurent series has the literal
Pareto progression mass as its sum, after its physical head is removed. -/
theorem hasSum_progressionWeight_laurent (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r + 1 < Q) :
    HasSum (crtLaurentTerm Q r) (progressionWeight Q r - positiveWeight r) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrQR : (r : ℝ) + 1 < Q := by exact_mod_cast hrQ
  have hQ0 : (Q : ℝ) ≠ 0 := ne_of_gt hQR
  have hx : 0 < (r : ℝ) / Q := div_pos hrR hQR
  have hx1 : (r : ℝ) / Q < 1 := (div_lt_one hQR).mpr (by linarith)
  have hy : 0 < ((r : ℝ) + 1) / Q := by positivity
  have hy1 : ((r : ℝ) + 1) / Q < 1 := (div_lt_one hQR).mpr hrQR
  have hs := ((hasSum_digamma_laurent hy hy1).sub
    (hasSum_digamma_laurent hx hx1)).div_const (Q : ℝ)
  have he : (fun k : ℕ =>
      (laurentTerm (((r : ℝ) + 1) / Q) k - laurentTerm ((r : ℝ) / Q) k) /
        (Q : ℝ)) = crtLaurentTerm Q r := by
    funext k
    unfold laurentTerm crtLaurentTerm
    simp only [div_pow, pow_succ]
    field_simp
  rw [he] at hs
  have hv :
      (((Complex.digamma ((((r : ℝ) + 1) / Q : ℝ) : ℂ)).re +
          Real.eulerMascheroniConstant + 1 / (((r : ℝ) + 1) / Q)) -
        ((Complex.digamma (((r : ℝ) / Q : ℝ) : ℂ)).re +
          Real.eulerMascheroniConstant + 1 / ((r : ℝ) / Q))) / (Q : ℝ) =
      progressionWeight Q r - positiveWeight r := by
    rw [progressionWeight_eq_digamma Q r hQ hr (by omega)]
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    unfold positiveWeight
    field_simp
    ring
  rw [hv] at hs
  exact hs

/-- Exact all-coefficient expansion of the physical CRT residue weight. -/
theorem progressionWeight_eq_laurent_tsum (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r + 1 < Q) :
    progressionWeight Q r = positiveWeight r + ∑' k : ℕ, crtLaurentTerm Q r k := by
  have h := (hasSum_progressionWeight_laurent Q r hQ hr hrQ).tsum_eq
  linarith

/-- Exact CRT Laurent expansion using the actual zeta coefficients. -/
theorem progressionWeight_eq_zeta_laurent_tsum (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r + 1 < Q) :
    progressionWeight Q r = positiveWeight r +
      ∑' k : ℕ, (-1 : ℝ) ^ k *
        (((r : ℝ) + 1) ^ (k + 1) - (r : ℝ) ^ (k + 1)) *
        (riemannZeta ((k + 2 : ℕ) : ℂ)).re / (Q : ℝ) ^ (k + 2) := by
  rw [progressionWeight_eq_laurent_tsum Q r hQ hr hrQ]
  congr 1
  apply tsum_congr
  intro k
  unfold crtLaurentTerm
  rw [positivePSeries_eq_zeta_re (k + 2) (by omega)]

end
end RiemannResearch.RH.Pareto.DigammaSmallArgument

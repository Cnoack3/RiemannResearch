import RiemannResearch.Analysis.ReciprocalAbel
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# Reciprocal energy from complete finite prefix bounds

Exact finite Abel summation transfers a linear prefix estimate into a bound
for the entire summable reciprocal energy. The RH consumer is the actual raw
Mobius far tail. No arithmetic prefix provider is asserted by this module.

Source: direct summation by parts, developed for the user's RH continuation,
September 24, 2026. The intended classical large-sieve input is documented in
RH/RawMobiusFarTailLargeSieve20260924.md; it is not assumed as an axiom here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis

private theorem prefix_weighted_abel (a w : ℕ → ℝ) (L : ℕ) :
    (∑ i ∈ Finset.range L, a i * w i) =
      (∑ i ∈ Finset.range L, a i) * w L +
        ∑ i ∈ Finset.range L,
          (∑ j ∈ Finset.range (i+1), a j) * (w i-w (i+1)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [ih]
    ring

/-- A finite reciprocal-energy estimate from a complete prefix bound. -/
theorem reciprocal_energy_sum_le_of_prefix
    (a : ℕ → ℝ) (q C : ℝ) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hp : ∀ L : ℕ, (∑ i ∈ Finset.range L, a i) ≤ C*(q+L))
    (L : ℕ) :
    (∑ i ∈ Finset.range L, a i / ((q+i+1)*(q+i+2))) ≤
      2*C/(q+2) := by
  let w : ℕ → ℝ := fun i => 1/((q+i+1)*(q+i+2))
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hd (i : ℕ) : w i-w (i+1) =
      2/((q+i+1)*(q+i+2)*(q+i+3)) := by
    dsimp [w]
    push_cast
    field_simp
    ring
  have hd0 (i : ℕ) : 0 ≤ w i-w (i+1) := by rw [hd]; positivity
  have ht (L : ℕ) :
      (∑ i ∈ Finset.range L, (q+i+1)*(w i-w (i+1))) =
        2/(q+2)-2/(q+L+2) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, hd]
      push_cast
      field_simp
      ring
  have he := prefix_weighted_abel a w L
  have hb := mul_le_mul_of_nonneg_right (hp L) (hw L)
  have hs : (∑ i ∈ Finset.range L,
      (∑ j ∈ Finset.range (i+1), a j)*(w i-w (i+1))) ≤
      C*(2/(q+2)-2/(q+L+2)) := by
    rw [← ht, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (hp (i+1)) (hd0 i)
    push_cast at h
    nlinarith only [h]
  have hu : C*(q+L)*w L + C*(2/(q+2)-2/(q+L+2)) =
      2*C/(q+2)-C/(q+L+1) := by
    dsimp [w]
    field_simp
    ring
  have htail : 0 ≤ C/(q+L+1) := by positivity
  have hsum : (∑ i ∈ Finset.range L, a i / ((q+i+1)*(q+i+2))) =
      ∑ i ∈ Finset.range L, a i*w i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    ring
  rw [hsum, he]
  linarith

/-- The same prefix bound controls the entire summable reciprocal tail. -/
theorem reciprocal_energy_tsum_le_of_prefix
    (a : ℕ → ℝ) (q C : ℝ) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hp : ∀ L : ℕ, (∑ i ∈ Finset.range L, a i) ≤ C*(q+L))
    (hs : Summable (fun i : ℕ => a i / ((q+i+1)*(q+i+2)))) :
    (∑' i : ℕ, a i / ((q+i+1)*(q+i+2))) ≤ 2*C/(q+2) := by
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  exact Eventually.of_forall (reciprocal_energy_sum_le_of_prefix a q C hq hC hp)

/-- Exact finite endpoint bound for an affine prefix estimate.
The intercept and slope are independent; no sign on the slope or summands
is needed for this finite inequality. -/
theorem reciprocal_energy_sum_le_of_affine_prefix
    (a : ℕ → ℝ) (q b C : ℝ) (hq : 0 ≤ q)
    (hp : ∀ L : ℕ, (∑ i ∈ Finset.range L, a i) ≤ b+C*L)
    (L : ℕ) :
    (∑ i ∈ Finset.range L, a i / ((q+i+1)*(q+i+2))) ≤
      (b+C*(q+2))/((q+1)*(q+2)) - C/(q+L+1) := by
  let w : ℕ → ℝ := fun i => 1/((q+i+1)*(q+i+2))
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hd (i : ℕ) : w i-w (i+1) =
      2/((q+i+1)*(q+i+2)*(q+i+3)) := by
    dsimp [w]
    push_cast
    field_simp
    ring
  have hd0 (i : ℕ) : 0 ≤ w i-w (i+1) := by rw [hd]; positivity
  have ht (L : ℕ) :
      (∑ i ∈ Finset.range L, (b+C*(i+1))*(w i-w (i+1))) =
        C*(2/(q+2)-2/(q+L+2))+(b-C*q)*(w 0-w L) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, hd]
      dsimp [w]
      push_cast
      field_simp
      ring
  have he := prefix_weighted_abel a w L
  have hb := mul_le_mul_of_nonneg_right (hp L) (hw L)
  have hs : (∑ i ∈ Finset.range L,
      (∑ j ∈ Finset.range (i+1), a j)*(w i-w (i+1))) ≤
      (C*(2/(q+2)-2/(q+L+2))+(b-C*q)*(w 0-w L)) := by
    rw [← ht]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (hp (i+1)) (hd0 i)
    push_cast at h
    nlinarith only [h]
  have hu : (b+C*L)*w L +
      (C*(2/(q+2)-2/(q+L+2))+(b-C*q)*(w 0-w L)) =
      (b+C*(q+2))/((q+1)*(q+2))-C/(q+L+1) := by
    dsimp [w]
    field_simp
    ring
  have hsum : (∑ i ∈ Finset.range L, a i / ((q+i+1)*(q+i+2))) =
      ∑ i ∈ Finset.range L, a i*w i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    ring
  rw [hsum, he]
  linarith

/-- Affine prefix transfer for any summable reciprocal tail.
A dual large-sieve estimate has intercept `(N^2-1)*C`, independently of
the physical cutoff `q`. This theorem leaves that provider explicit.
Source: Abel summation; Kowalski, *Amplification Arguments for Large Sieve
Inequalities*, equations (2)--(3), motivates the application. -/
theorem reciprocal_energy_tsum_le_of_affine_prefix
    (a : ℕ → ℝ) (q b C : ℝ) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hp : ∀ L : ℕ, (∑ i ∈ Finset.range L, a i) ≤ b+C*L)
    (hs : Summable (fun i : ℕ => a i / ((q+i+1)*(q+i+2)))) :
    (∑' i : ℕ, a i / ((q+i+1)*(q+i+2))) ≤
      (b+C*(q+2))/((q+1)*(q+2)) := by
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro L
  have h := reciprocal_energy_sum_le_of_affine_prefix a q b C hq hp L
  have ht : 0 ≤ C/(q+L+1) := by positivity
  linarith

/-- Bounded signed partial sums give a reciprocal tail bound with two
denominator factors, preserving cancellation. -/
theorem reciprocal_tsum_abs_le_of_abs_prefix
    (a : ℕ → ℝ) (q B : ℝ) (hq : 0 ≤ q)
    (hp : ∀ L : ℕ, |∑ i ∈ Finset.range L, a i| ≤ B)
    (hs : Summable (fun i : ℕ => a i / ((q+i+1)*(q+i+2)))) :
    |∑' i : ℕ, a i / ((q+i+1)*(q+i+2))| ≤ B/((q+1)*(q+2)) := by
  have hu := reciprocal_energy_tsum_le_of_affine_prefix
    a q B 0 hq le_rfl
    (fun L => by simpa using (le_abs_self _).trans (hp L)) hs
  have hn : Summable (fun i : ℕ => (-a i) / ((q+i+1)*(q+i+2))) := by
    simpa only [neg_div] using hs.neg
  have hl := reciprocal_energy_tsum_le_of_affine_prefix
    (fun i => -a i) q B 0 hq le_rfl
    (fun L => by
      simpa only [Finset.sum_neg_distrib, zero_mul, add_zero] using
        (neg_le_abs (∑ i ∈ Finset.range L, a i)).trans (hp L)) hn
  simp only [zero_mul, add_zero, neg_div, tsum_neg] at hu hl
  exact abs_le.mpr ⟨by linarith, hu⟩


end RiemannResearch.Analysis

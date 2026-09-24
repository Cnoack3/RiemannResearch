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

end RiemannResearch.Analysis

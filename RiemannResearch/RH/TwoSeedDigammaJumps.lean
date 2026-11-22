import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-! # Digamma sums over the jumps of a periodic Pareto trial

The wrap at the end of the period contributes the value at zero. This matters
for the squared error of residue trials, which equals one at that site. -/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private def psiNode (L r : ℕ) : ℝ :=
  (Complex.digamma (((r : ℝ) / L : ℝ) : ℂ)).re

private theorem period_summation_by_parts (h b : ℕ → ℝ) (L : ℕ) :
    (∑ i ∈ Finset.range L, h (i + 1) * (b (i + 2) - b (i + 1))) +
      (∑ i ∈ Finset.range L, (h (i + 1) - h i) * b (i + 1)) =
      h L * b (L + 1) - h 0 * b 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ]
    linarith only [ih, show h (L + 1) * (b (L + 2) - b (L + 1)) +
      (h (L + 1) - h L) * b (L + 1) = h (L + 1)*b (L + 2) - h L*b (L + 1) by ring]

/-- Exact signed correction at the jump sites of a periodic sequence.
A summand at a site where the two consecutive values agree is zero. -/
def digammaJumpSum (L : ℕ) (h : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range L, (h (i + 1) - h i) * psiNode L (i + 1)

/-- Discrete summation by parts followed by the digamma recurrence at the
wrap of the period. Every positive Pareto site is included. -/
theorem periodic_paretoMean_eq_digamma_jumps (L : ℕ) (hL : 0 < L)
    (h : ℕ → ℝ) {C : ℝ} (hb : ∀ k, |h k| ≤ C)
    (hp : ∀ k, h (k + L) = h k) :
    paretoMean h = h 0 - digammaJumpSum L h / L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hwrap : psiNode L (L + 1) = psiNode L 1 + L := by
    have he : ((L : ℝ)+1)/L = 1/(L : ℝ)+1 := by field_simp; ring
    have hd := re_digamma_add_one (x := 1 / (L : ℝ)) (by positivity)
    simpa [psiNode, Nat.cast_add, he, hLr.ne'] using hd
  have hsum : paretoMean h =
      (∑ i ∈ Finset.range L, h (i + 1) * (psiNode L (i + 2) - psiNode L (i + 1))) / L := by
    rw [periodic_paretoMean L hL h hb hp, Fin.sum_univ_eq_sum_range
      (fun i : ℕ => progressionWeight L (i + 1) * h (i + 1)) L, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [progressionWeight_eq_digamma L (i + 1) hL (by omega) (by have := Finset.mem_range.mp hi; omega)]
    simp only [psiNode, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (i : ℝ)+2 = (i + 1)+1 by ring]
    ring
  have htel := period_summation_by_parts h (psiNode L) L
  change _ + digammaJumpSum L h = _ at htel
  rw [hwrap, show h L = h 0 by simpa using hp 0] at htel
  have hsum' : (∑ i ∈ Finset.range L, h (i + 1) * (psiNode L (i + 2) - psiNode L (i + 1))) =
      h 0 * L - digammaJumpSum L h := by
    linarith only [htel, mul_add (h 0) (psiNode L 1) (L : ℝ)]
  rw [hsum, hsum', sub_div, mul_div_cancel_right₀ _ hLr.ne']

/-- The full squared error of a periodic trial vanishing at zero, evaluated
using the jumps of its squared residual. -/
theorem paretoError_eq_one_sub_digamma_jumps (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hb : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + L) = f k) (h0 : f 0 = 0) :
    paretoError f = 1 - digammaJumpSum L (fun k => (1 - f k)^2) / L := by
  have hh (k : ℕ) : |1 - f k| ≤ 1 + C :=
    (abs_sub _ _).trans (by simpa using add_le_add_left (hb k) (1 : ℝ))
  have hs (k : ℕ) : |(1 - f k)^2| ≤ (1 + C)^2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hh k) 2
  have h := periodic_paretoMean_eq_digamma_jumps L hL (fun k => (1 - f k)^2) hs
    (fun k => by rw [hp])
  rw [h0] at h
  simpa only [paretoError, paretoMean, paretoInner, pow_two, sub_zero, one_mul] using h

end
end RiemannResearch.RH.Pareto

import RiemannResearch.RH.ParetoAnnihilatorOneSided
import RiemannResearch.RH.CanonicalMobiusWindowCancellation

/-!
# A moving Möbius window for the Pareto annihilator

Christian Noack's quadratic-window handoff asks for a pairing bound that
retains the tail beyond the window with coefficient of order `N`.
The local cancellation bound for the canonical head and its global bound
can both be used on the near tail.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- A two-cutoff pairing bound with the same outer-tail error at both cutoffs.
The global Möbius bound controls that shared error even when the local
cancellation estimate is larger. -/
theorem annihilator_mean_abs_le_mobius_window
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (N K : ℕ) (hN : 0 < N)
    (ε U W δ : ℝ) (hε : 0 ≤ ε) (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (hM : ∀ t : ℕ, N ≤ t →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ))
    (hm : |mobiusReciprocalSum N| ≤ ε)
    (hnear : (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) ≤ U + δ)
    (hfar : (∑' k : ℕ, positiveWeight (k+K*N) * |hilbertSequence z (k+K*N)|) ≤ W + δ) :
    |inner ℝ z hilbertOne| ≤
      (2 + ε * (K : ℝ) * ((K : ℝ)+2) * ((N+1 : ℕ) : ℝ)) * U +
      (1 + 2 * (N : ℝ)) * (W + 2 * δ) := by
  let B := 1 + ε * (K : ℝ) * ((K : ℝ)+2) * ((N+1 : ℕ) : ℝ)
  let b := min B (2 * (N : ℝ)) / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : 0 ≤ b := div_nonneg (le_min hB (by positivity)) hNR.le
  have hbn : b * (N : ℝ) = min B (2 * (N : ℝ)) :=
    div_mul_cancel₀ _ hNR.ne'
  have hmid (j : ℕ) (hj : N < j) (hj' : j ≤ K * N) :
      |canonicalMobiusHead N j| ≤ b * (N : ℝ) := by
    rw [hbn]
    apply le_min
    · exact canonicalMobiusHead_window_bound N j K ε hε hj
        (hj'.trans (Nat.mul_le_mul_left K (Nat.le_succ _))) hM hm
    · exact canonicalMobiusHead_abs_le_two_mul N hN j
  have hglobal : 1 + b * (N : ℝ) ≤ 1 + 2 * (N : ℝ) := by
    rw [hbn]
    linarith only [min_le_right B (2 * (N : ℝ))]
  have hlocal : 1 + b * (N : ℝ) ≤
      2 + ε * (K : ℝ) * ((K : ℝ)+2) * ((N+1 : ℕ) : ℝ) := by
    rw [hbn]
    have h := min_le_left B (2 * (N : ℝ))
    dsimp [B] at h ⊢
    linarith
  calc
    _ ≤ _ := annihilator_mean_abs_le_window_tails z hz N K hN b hb hmid
    _ ≤ (1 + b * (N : ℝ)) * (U+δ) + (1 + 2 * (N : ℝ)) * (W+δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hnear (by positivity))
        (mul_le_mul_of_nonneg_left hfar (by positivity))
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hlocal hU
      have h2 := mul_le_mul_of_nonneg_right hglobal hδ
      linarith only [h1, h2]

end RiemannResearch.RH.Pareto.CoefficientStabilization

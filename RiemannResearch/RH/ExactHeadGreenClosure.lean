import RiemannResearch.Analysis.GreenProfileBounds
import RiemannResearch.Analysis.FiniteProfileEnergy
import RiemannResearch.RH.ParetoExactHeadResidual
import Mathlib.Tactic.Linarith

/-!
# A weaker Green-profile criterion for RH
Source: user-provided "Exact-Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, sections 7, 9--10 and agenda R4/R5.
The existing legal exact-head residual theorem lets bounded energy replace
vanishing energy. Consequently it suffices to control W E by C q and to bound
the signed profile moment above, even on a cofinal set of cutoffs.
This is a conditional research reduction. Legal exact heads, the root identity,
tail control and actual relative profile/moment bounds must all be supplied.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadGreenClosure
open RiemannResearch.Analysis.GreenProfileBounds
open RiemannResearch.Analysis.FiniteProfileEnergy

/-- Cofinal bounded profile data suffice. No convergence, bounded coefficients,
prime number theorem or nonsingularity hypothesis is required. -/
theorem riemannHypothesis_of_cofinal_relative_profile
    (A : Set ℕ) (hA : ∀ n ∈ A, 0 < n)
    (f : ℕ → ThresholdHilbert) (hf : ∀ N, f N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    (q r tau m terminal : ℕ → ℝ) (C a B T : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hdata : ∀ J, ∃ N, J ≤ N ∧
      0 ≤ q N ∧ r N = q N + tau N ∧
      tau N ^ 2 ≤ a * q N ∧ (r N - m N) ^ 2 ≤ C * q N ∧
      m N ≤ B ∧ terminal N ≤ T ∧
      ‖hilbertOne - f N‖ ^ 2 = terminal N + q N) :
    RiemannHypothesis := by
  choose n hn hq hr ht he hm hterminal hsplit using hdata
  apply riemannHypothesis_of_bounded_exact_head_residuals A hA
    (fun N => f (n N)) (fun N => hf (n N))
    (fun N k hk hkN => hhead (n N) k hk (hkN.trans (hn N)))
    (T + 2 * B + 2 * C + 2 * a)
  intro N
  rw [hsplit N]
  have h := energy_le_of_relative_profile (hq N) hC ha (hr N) (ht N) (he N) (hm N)
  linarith [hterminal N]

/-- Finite signed profile form of the cofinal criterion. The squared error is
proved by exact weighted Cauchy--Schwarz, not assumed as an extra obligation. -/
theorem riemannHypothesis_of_cofinal_profile_energy
    {ι : Type*} (A : Set ℕ) (hA : ∀ n ∈ A, 0 < n)
    (f : ℕ → ThresholdHilbert) (hf : ∀ N, f N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    (s : ℕ → Finset ι) (w sign b h : ℕ → ι → ℝ)
    (q tau terminal : ℕ → ℝ) (C a B T : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hdata : ∀ J, ∃ N, J ≤ N ∧
      (∀ i ∈ s N, 0 ≤ w N i) ∧ (∀ i ∈ s N, sign N i ^ 2 ≤ 1) ∧
      0 ≤ q N ∧ pairing (s N) (w N) (sign N) (b N) = q N + tau N ∧
      tau N ^ 2 ≤ a * q N ∧
      mass (s N) (w N) * energy (s N) (w N) (fun i => b N i - h N i) ≤ C * q N ∧
      pairing (s N) (w N) (sign N) (h N) ≤ B ∧ terminal N ≤ T ∧
      ‖hilbertOne - f N‖ ^ 2 = terminal N + q N) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_relative_profile A hA f hf hhead q
    (fun N => pairing (s N) (w N) (sign N) (b N)) tau
    (fun N => pairing (s N) (w N) (sign N) (h N)) terminal C a B T hC ha
  intro J
  obtain ⟨N, hN, hw, hsign, hq, hr, ht, he, hm, hterminal, hsplit⟩ := hdata J
  exact ⟨N, hN, hq, hr, ht,
    (signed_profile_error_sq_le (s N) (w N) (sign N) (b N) (h N) hw hsign).trans he,
    hm, hterminal, hsplit⟩

end RiemannResearch.RH.Pareto.ExactHeadGreenClosure

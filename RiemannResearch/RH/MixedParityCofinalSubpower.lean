import RiemannResearch.RH.MixedConductorHead
import RiemannResearch.RH.LegalExactHeadSubpolynomial

/-! # Complete cost of cofinal mixed Pareto interpolation

Apply the localized legal-space Mellin obstruction to a mixed trial for a legal target minus the constant. A subpolynomial squared residual on exact expanding heads implies RH. -/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- A right zero gives a power lower bound for the actual mixed interpolation cost. -/
theorem mixed_parity_agenda_cost_barrier {z v : ThresholdHilbert}
    (hzV : z ∈ closedSpace) (hvM : v ∈ mixedClosure) (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n → hilbertSequence v k = hilbertSequence z k - 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hsz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) * (n : ℝ) ^ (2 * s.re - 1) ≤
      (‖z - hilbertOne‖ + ‖v‖) ^ 2 := by
  have hx := closedSpace_le_legalClosure (closedSpace.sub_mem hzV (mixedClosure_le_closedSpace hvM))
  have hfit : ∀ k, 0 < k → k < n → hilbertSequence (z - v) k = 1 := by
    intro k hk hkn
    rw [hilbertSequence_sub, Pi.sub_apply, hhead k hk hkn]
    ring
  have h := legal_exact_head_residual_power_lower {d : ℕ | 0 < d} (fun _ hd => hd) hx n hn hfit s hs hs1 hsz
  have hneg : hilbertOne - (z - v) = -(z - hilbertOne - v) := by abel
  rw [hneg, norm_neg] at h
  exact h.trans ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_sub_le (z - hilbertOne) v))

/-- Cofinal mixed fits of z−1 with a subpolynomial complete residual certificate force RH. -/
theorem rh_of_mixed_agenda_cofinal_subpower {z : ThresholdHilbert} (hzV : z ∈ closedSpace)
    (v : ℕ → ThresholdHilbert) (hvM : ∀ i, v i ∈ mixedClosure)
    (n : ℕ → ℕ) (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hhead : ∀ i k, 0 < k → k < n i → hilbertSequence (v i) k = hilbertSequence z k - 1)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖z - hilbertOne - v i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_legal_exact_head_subpolynomial
    {d : ℕ | 0 < d} (fun _ hd => hd) (fun i => z - v i) n C hn
  · intro i
    exact closedSpace_le_legalClosure (closedSpace.sub_mem hzV (mixedClosure_le_closedSpace (hvM i)))
  · intro i k hk hkn
    rw [hilbertSequence_sub, Pi.sub_apply, hhead i k hk hkn]
    ring
  · exact hC
  · intro i
    have he : hilbertOne - (z - v i) = -(z - hilbertOne - v i) := by abel
    simpa only [he, norm_neg] using hbound i
  · exact hsub

#print axioms mixed_parity_agenda_cost_barrier
#print axioms rh_of_mixed_agenda_cofinal_subpower
end RiemannResearch.RH.Pareto.PrimePowerSchur

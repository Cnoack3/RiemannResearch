import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Cofinal exact-head legal trials with subpolynomial finite certificates imply RH

The only quantitative arithmetic premise is the subpolynomial growth of the
certificate, together with its proved complete-energy bound.  The zeta-zero
detector is derived from the actual Mellin theorem in LocalizedMellinObstruction.
No arithmetic growth estimate is asserted here.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.SubpolynomialWindow

/-- A cofinal family of genuine legal trials with exact expanding heads and
subpolynomial complete-energy certificates proves the actual Riemann hypothesis.
The real-valued cofinality hypothesis is the direct input to the log-growth API. -/
theorem riemannHypothesis_of_cofinal_legal_exact_head_subpolynomial
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hhead : ∀ i k, 0 < k → k < n i → hilbertSequence (f i) k = 1)
    (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖hilbertOne - f i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < (2 * s.re - 1) / ‖s‖ ^ 2 :=
    div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) 2)
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hfloor : ∀ᶠ i : ℕ in atTop,
      ((2 * s.re - 1) / ‖s‖ ^ 2) * (n i : ℝ) ^ (2 * s.re - 1) ≤ C i + 1 := by
    filter_upwards [hn1] with i hi
    have hiNat : 1 ≤ n i := by exact_mod_cast hi
    exact (legal_exact_head_residual_power_lower A hA (hf i)
      (n i) hiNat (hhead i) s hs hs1 hz).trans (hbound i)
  exact no_positive_power_floor (fun i => (n i : ℝ)) C 1
    ((2 * s.re - 1) / ‖s‖ ^ 2) (2 * s.re - 1)
    hn hC (by norm_num) hc ha hsub hfloor

end RiemannResearch.RH.Pareto

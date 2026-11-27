import RiemannResearch.Analysis.MontgomeryThreePrimeSchwartz
import RiemannResearch.Analysis.MontgomeryCompactGapTests

/-!
# A three-prime arithmetic criterion for the actual positive-gap conjecture

Section 4 of the supplied Mellin / prime-orbit handoff. The same two integer
coefficient functions determine the prime words for every centered smooth
cutoff. The arithmetic limit below is the hypothesis to be established.
-/

noncomputable section
open Filter MeasureTheory
open scoped FourierTransform Topology ContDiff

namespace RiemannResearch.Analysis.MontgomeryAllPairWordRounding

open MontgomeryPositiveGap

/-- Compact-uniform positive-gap PCC is equivalent to the exact sine-law
limits for all even smooth compactly supported tests on a fixed word mesh. -/
theorem exists_two_three_five_pcc_criterion :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let r : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ f : ℝ → ℝ, HasCompactSupport f → ContDiff ℝ ∞ f →
        (∀ x, f (-x) = f x) → ∀ R : ℝ, 0 < R → (∀ x, R ≤ |x| → f x = 0) →
        Tendsto (fun T => threePrimeFourierTest p q r (a T) (b T) T
          (fun v => (𝓕 (fun x => (f x : ℂ)) v).re)) atTop
          (𝓝 (∫ x in (0:ℝ)..R, f x * (1 - Real.sinc (Real.pi*x)^2)))) := by
  obtain ⟨a,b,hm,ha⟩ := exists_two_three_five_compact_smooth_reconstruction
  refine ⟨a,b,hm,?_⟩
  constructor
  · intro h f hc hd he R hR hs
    have ht := positiveGapPCC_iff_even_compact_smooth_tests.mp h f hd he R hR hs
    simpa only [sub_sub_cancel, sub_zero] using ht.sub (ha f hc hd he)
  · intro h
    apply positiveGapPCC_of_even_bump_limits
    intro g
    have he := ha g g.hasCompactSupport g.contDiff g.neg
    have ht := h g g.hasCompactSupport g.contDiff g.neg g.rOut g.rOut_pos
      (fun x hx => g.zero_of_le_dist (by simpa [Real.dist_eq] using hx))
    simpa only [sub_add_cancel, zero_add] using he.add ht

end RiemannResearch.Analysis.MontgomeryAllPairWordRounding

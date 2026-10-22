import RiemannResearch.RH.BurnolMellinContinuation
import RiemannResearch.RH.ParetoMellinFiniteEnergy
import RiemannResearch.RH.DampedMobiusMellinArithmetic

/-!
# The actual centered damped arithmetic family and Burnol's RH reduction

Source: J.-F. Burnol, arXiv:math/0202166, Lemma 4.3 and Theorem 4.2,
for the finite-energy Mellin/zero-shift strategy. The arithmetic family here
is the repository's real floor prefix, with arbitrary real centering.
The preceding modules prove its transform identity and the required
holomorphy. Only finite-energy realization at damping tending to zero is
left as an explicit research obligation. No common norm bound is required.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.Pareto

theorem centered_dampedMobius_mellin_cross_identity
    (f : ThresholdHilbert) {ε : ℝ} (hε : 0 ≤ ε) (C : ℝ)
    (hcoordinates : ∀ n : ℕ,
      hilbertSequence f n = dampedMobiusPrefix ε n - (n : ℝ) * C)
    (s : ℂ) (hs : 1 < s.re) :
    s * riemannZeta (s + (ε : ℂ)) * paretoMellin f s =
      riemannZeta s * (1 - (C : ℂ) * riemannZeta (s + (ε : ℂ))) := by
  have hshift : 1 ≤ (s + (ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hz := riemannZeta_ne_zero_of_one_le_re hshift
  have hi := paretoMellin_of_centered_dampedMobiusPrefix f hε C hcoordinates hs
  calc
    _ = (s * paretoMellin f s) * riemannZeta (s + (ε : ℂ)) := by ring
    _ = _ := by rw [hi]; field_simp [hz]

/-- Conditional research reduction. The only domain-specific assumption is
the existence of actual centered finite-energy prefixes at positive damping
parameters tending to zero. The constants and norms may depend on the stage. -/
theorem riemannHypothesis_of_centered_damped_finiteEnergy_sequence
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ j, ∃ (C : ℝ) (f : ThresholdHilbert), ∀ n : ℕ,
      hilbertSequence f n = dampedMobiusPrefix (ε j) n - (n : ℝ) * C) :
    RiemannHypothesis := by
  choose C F hcoordinates using henergy
  apply Burnol.riemannHypothesis_of_mellin_identity_sequence ε hpos hlim
    (fun j => (C j : ℂ)) (fun j => paretoMellin (F j))
  · exact fun j => paretoMellin_analyticOnNhd (F j)
  · intro j s hs
    exact centered_dampedMobius_mellin_cross_identity (F j) (hpos j).le (C j)
      (hcoordinates j) s hs

/-- A scalar-series version of the same reduction, with no abstract Hilbert
realization left for the caller to construct. Summability at a positive
sequence of damping parameters remains the open arithmetic assertion. -/
theorem riemannHypothesis_of_centered_damped_square_summable
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ j, ∃ C : ℝ, Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix (ε j) n - (n : ℝ) * C) ^ 2)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_centered_damped_finiteEnergy_sequence ε hpos hlim
  intro j
  obtain ⟨C, hC⟩ := henergy j
  let g : ℕ → ℝ := fun n => dampedMobiusPrefix (ε j) n - (n : ℝ) * C
  have hg0 : g 0 = 0 := by simp [g, dampedMobiusPrefix, arithmeticFloorPrefix]
  refine ⟨C, sequenceHilbert g hC, ?_⟩
  intro n
  exact congrFun (hilbertSequence_sequenceHilbert g hC hg0) n

end RiemannResearch.RH.Pareto

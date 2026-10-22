import RiemannResearch.RH.BurnolFiniteEnergyReduction

/-!
# Fixed damping and the small-damping obstruction

Source: J.-F. Burnol, "On an analytic estimate in the theory of the Riemann
zeta function and a theorem of Baez-Duarte", arXiv:math/0202166,
Corollary 4.1 and Theorem 4.2. The source supports the zero-propagation
strategy. We specialize the existing Mellin continuation to actual centered
arithmetic finite energy, and combine it with the isolated-zero obstruction.

At one fixed damping the conclusion is propagation of eligible zeros, not
their absence. Common numerator/denominator zeros have not been excluded.
The second theorem states exactly why finite energy at arbitrarily small
positive dampings is RH-strength, without assuming a uniform energy bound.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto

/-- Conditional research reduction: actual finite energy at one fixed
damping propagates every zero whose shifted argument remains in the open
Mellin half-plane. The substantive summability premise remains explicit. -/
theorem centered_damped_square_summable_zero_propagation
    {ε : ℝ} (hε : 0 ≤ ε) (C : ℝ)
    (henergy : Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * C) ^ 2))
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + ε < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (ρ - (ε : ℂ)) = 0 := by
  let g : ℕ → ℝ := fun n => dampedMobiusPrefix ε n - (n : ℝ) * C
  have hg0 : g 0 = 0 := by
    simp [g, dampedMobiusPrefix, arithmeticFloorPrefix]
  let f : ThresholdHilbert := sequenceHilbert g henergy
  have hcoordinates : ∀ n : ℕ,
      hilbertSequence f n = dampedMobiusPrefix ε n - (n : ℝ) * C := by
    intro n
    exact congrFun (hilbertSequence_sequenceHilbert g henergy hg0) n
  exact Burnol.zero_propagation_of_mellin_identity ε hε (C : ℂ)
    (paretoMellin f) (paretoMellin_analyticOnNhd f)
    (centered_dampedMobius_mellin_cross_identity f hε C hcoordinates)
    ρ hhalf hone hz

/-- An off-line zero rules out finite energy for every sufficiently small
positive damping, independently of the choice of real centering. This is
stronger than merely ruling out one specified sequence of dampings. -/
theorem right_half_zero_eventually_not_centered_damped_square_summable
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ C : ℝ,
      ¬ Summable (fun n : ℕ => positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) * C) ^ 2) := by
  obtain ⟨δ, hδ, hshift⟩ :=
    Burnol.right_half_zero_shift_obstruction ρ hhalf hone hz
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ C henergy
  have hs := hshift ε hε hεδ
  have hhalfε : (1 / 2 : ℝ) + ε < ρ.re := by
    have hr := hs.1
    simp only [Complex.sub_re, Complex.ofReal_re] at hr
    linarith
  exact hs.2.1 (centered_damped_square_summable_zero_propagation
    hε.le C henergy ρ hhalfε hone hz)

end RiemannResearch.RH.Pareto

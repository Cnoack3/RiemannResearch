import RiemannResearch.RH.ZetaConductorRegularization
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# The local zero-shift obstruction in Burnol's damping argument

Source: J.-F. Burnol, "On an analytic estimate in the theory of the Riemann
zeta function and a theorem of Baez-Duarte", arXiv:math/0202166,
Corollary 4.1 and Theorem 4.2. The source supports the zero-propagation
strategy. This module proves its isolated-zero step for Mathlib's actual
zeta function. It does not assert the paper's separate Mellin continuation
or square-integrability statements.

The RH implication below explicitly assumes propagation of an actual
zeta zero under arbitrarily small positive shifts. Producing that
propagation from a damped arithmetic L2 function is a separate obligation.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.RH.Burnol

/-- Every point away from the pole has a punctured zero-free neighborhood. -/
theorem zeta_eventually_ne_zero_punctured (ρ : ℂ) (hρ : ρ ≠ 1) :
    ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
  have ha := analyticOn_riemannZeta ρ hρ
  apply ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro h
  exact ZetaConductorRegularization.analyticOrderAt_riemannZeta_ne_top_of_ne_one hρ
    (analyticOrderAt_eq_top.mpr h)

/-- All sufficiently small nonzero positive horizontal shifts avoid zeros,
even if the starting point is itself a zero. -/
theorem zeta_small_left_shift_ne_zero (ρ : ℂ) (hρ : ρ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      riemannZeta (ρ - (ε : ℂ)) ≠ 0 := by
  have he := zeta_eventually_ne_zero_punctured ρ hρ
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hd : dist (ρ - (ε : ℂ)) ρ = ε := by
    rw [dist_eq_norm, show (ρ - (ε : ℂ)) - ρ = -(ε : ℂ) by ring]
    simp [Complex.norm_real, abs_of_pos hε]
  apply hb (by simpa only [hd] using hεδ)
  change ρ - (ε : ℂ) ≠ ρ
  intro hz
  have hz' := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.ofReal_re] at hz'
  linarith

/-- At any zero in the right half-strip, every sufficiently small positive
shift leaves the numerator nonzero at the shifted denominator zero. -/
theorem right_half_zero_shift_obstruction
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (1 / 2 : ℝ) < (ρ - (ε : ℂ)).re ∧
      riemannZeta (ρ - (ε : ℂ)) ≠ 0 ∧
      riemannZeta ((ρ - (ε : ℂ)) + (ε : ℂ)) = 0 := by
  have hρ : ρ ≠ 1 := by intro h; simp [h] at hone
  obtain ⟨δ, hδ, hn⟩ := zeta_small_left_shift_ne_zero ρ hρ
  refine ⟨min δ (ρ.re - 1 / 2), lt_min hδ (by linarith), ?_⟩
  intro ε hε he
  refine ⟨?_, hn ε hε (lt_of_lt_of_le he (min_le_left _ _)), ?_⟩
  · have he' := lt_of_lt_of_le he (min_le_right δ (ρ.re - 1 / 2))
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · simpa only [sub_add_cancel] using hz

/-- Burnol's zero-accumulation step. Only arbitrarily small admissible shifts
are needed; neither a common L2 bound nor a monotone damping sequence occurs.
The substantive zero-propagation hypothesis is kept explicit. -/
theorem riemannHypothesis_of_cofinal_zero_propagation
    (hprop : ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ riemannZeta (ρ - (ε : ℂ)) = 0) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro ρ hhalf hone hz
  have hρ : ρ ≠ 1 := by intro h; simp [h] at hone
  obtain ⟨δ, hδ, hn⟩ := zeta_small_left_shift_ne_zero ρ hρ
  obtain ⟨ε, hε, he, hzε⟩ := hprop ρ hhalf hone hz δ hδ
  exact hn ε hε he hzε

/-- A positive damping sequence tending to zero suffices for the propagation
argument, without any monotonicity or uniform norm premise. -/
theorem riemannHypothesis_of_zero_propagation_sequence
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hprop : ∀ j : ℕ, ∀ ρ : ℂ,
      (1 / 2 : ℝ) + ε j < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      riemannZeta (ρ - (ε j : ℂ)) = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_zero_propagation
  intro ρ hhalf hone hz δ hδ
  have hsmall := hlim.eventually
    (gt_mem_nhds (lt_min hδ (show (0 : ℝ) < ρ.re - 1 / 2 by linarith)))
  obtain ⟨j, hj⟩ := hsmall.exists
  have hjδ : ε j < δ := lt_of_lt_of_le hj (min_le_left _ _)
  have hjρ : ε j < ρ.re - 1 / 2 := lt_of_lt_of_le hj (min_le_right _ _)
  exact ⟨ε j, hpos j, hjδ, hprop j ρ (by linarith) hone hz⟩

end RiemannResearch.RH.Burnol

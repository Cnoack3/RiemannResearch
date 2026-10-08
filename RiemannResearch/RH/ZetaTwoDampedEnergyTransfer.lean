import RiemannResearch.RH.BurnolFixedDampingObstruction
import RiemannResearch.RH.DampedMobiusHalfEndpoint

/-!
# Transfer of the actual damped arithmetic energy to zeta(2) weights

Source: user-directed research continuation; see
`IndependentPrimeResearchContinuation20261007.md`, energy transfer and
small-damping research agenda. The analytic reduction is the existing
`BurnolFixedDampingObstruction` theorem.

The positive normalizer `Z` may be specialized to zeta(2). The energy
`normalizedEnergy Z f n` is then exactly |f(n)|^2 Q({n}), with Q({0}) = 0.
All analytic continuation and zero-shift arguments are imported from the
existing Burnol finite-energy reduction. This file supplies only the exact
weight comparison and its actual arithmetic consumers.

-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.ZetaTwo

/-- Unnormalized zeta(2) weight; Lean's division convention makes it zero at 0. -/
def reciprocalSquareWeight (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

/-- The normalized zeta(2) energy summand when `Z = ζ(2)`. -/
def normalizedEnergy (Z : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (reciprocalSquareWeight n * (f n) ^ 2) / Z

theorem reciprocalSquareWeight_nonneg (n : ℕ) :
    0 ≤ reciprocalSquareWeight n := by
  unfold reciprocalSquareWeight
  positivity

/-- The upper comparison includes the harmless zero coordinate. -/
theorem positiveWeight_le_reciprocalSquareWeight (n : ℕ) :
    positiveWeight n ≤ reciprocalSquareWeight n := by
  by_cases hn : n = 0
  · subst n
    simp [positiveWeight, reciprocalSquareWeight]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold positiveWeight reciprocalSquareWeight
    apply one_div_le_one_div_of_le (sq_pos_of_pos hn0)
    nlinarith

/-- Equivalently, one half of the inverse-square weight is below Pareto. -/
theorem reciprocalSquareWeight_le_twice_positiveWeight (n : ℕ) :
    reciprocalSquareWeight n ≤ 2 * positiveWeight n := by
  by_cases hn : n = 0
  · subst n
    simp [positiveWeight, reciprocalSquareWeight]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    unfold positiveWeight reciprocalSquareWeight
    rw [mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0)
      (mul_pos hn0 (by linarith))).2
    nlinarith

/-- The two unnormalized weighted square-summability conditions coincide. -/
theorem summable_reciprocalSquareEnergy_iff (f : ℕ → ℝ) :
    Summable (fun n => reciprocalSquareWeight n * (f n) ^ 2) ↔
      Summable (fun n => positiveWeight n * (f n) ^ 2) := by
  constructor
  · intro h
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg (f n)))
      (fun n => mul_le_mul_of_nonneg_right
        (positiveWeight_le_reciprocalSquareWeight n) (sq_nonneg (f n))) h
  · intro h
    have htwo : Summable (fun n => 2 * (positiveWeight n * (f n) ^ 2)) :=
      h.mul_left 2
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (reciprocalSquareWeight_nonneg n) (sq_nonneg (f n)))
      (fun n => ?_) htwo
    calc
      reciprocalSquareWeight n * (f n) ^ 2 ≤
          (2 * positiveWeight n) * (f n) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (reciprocalSquareWeight_le_twice_positiveWeight n) (sq_nonneg (f n))
      _ = 2 * (positiveWeight n * (f n) ^ 2) := by ring

/-- Multiplication by the positive probability normalizer changes no membership. -/
theorem summable_normalizedEnergy_iff_reciprocalSquareEnergy
    {Z : ℝ} (hZ : 0 < Z) (f : ℕ → ℝ) :
    Summable (normalizedEnergy Z f) ↔
      Summable (fun n => reciprocalSquareWeight n * (f n) ^ 2) := by
  constructor
  · intro h
    have hm : Summable (fun n => normalizedEnergy Z f n * Z) := h.mul_right Z
    apply hm.congr
    intro n
    exact div_mul_cancel₀ _ (ne_of_gt hZ)
  · intro h
    exact h.div_const Z

/-- Exact equivalence of zeta(2) and Pareto square-energy membership. -/
theorem summable_normalizedEnergy_iff_pareto
    {Z : ℝ} (hZ : 0 < Z) (f : ℕ → ℝ) :
    Summable (normalizedEnergy Z f) ↔
      Summable (fun n => positiveWeight n * (f n) ^ 2) :=
  (summable_normalizedEnergy_iff_reciprocalSquareEnergy hZ f).trans
    (summable_reciprocalSquareEnergy_iff f)

/-- The unconditional range includes the half-damping endpoint. -/
theorem canonical_damped_normalizedEnergy_of_half_le
    {Z ε : ℝ} (hZ : 0 < Z) (hε : (1 / 2 : ℝ) ≤ ε) :
    Summable (normalizedEnergy Z
      (fun n => dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re)) := by
  exact (summable_normalizedEnergy_iff_pareto hZ _).mpr
    (centered_dampedMobius_square_summable_of_half_le hε)

/-- In this inclusive range, the canonical real center is necessary as well. -/
theorem centered_damped_normalizedEnergy_iff_of_half_le
    {Z ε : ℝ} (hZ : 0 < Z) (hε : (1 / 2 : ℝ) ≤ ε) (C : ℝ) :
    Summable (normalizedEnergy Z
      (fun n => dampedMobiusPrefix ε n - (n : ℝ) * C)) ↔
      C = (1 / riemannZeta (1 + (ε : ℂ))).re :=
  (summable_normalizedEnergy_iff_pareto hZ _).trans
    (centered_dampedMobius_square_summable_iff_of_half_le hε C)

/-- The existing Burnol theorem transported to the actual zeta(2) energy.
No uniform norm bound, monotonicity, or convergence to one is assumed. -/
theorem riemannHypothesis_of_centered_damped_normalizedEnergy_sequence
    {Z : ℝ} (hZ : 0 < Z)
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ j, ∃ C : ℝ, Summable (normalizedEnergy Z
      (fun n => dampedMobiusPrefix (ε j) n - (n : ℝ) * C))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_centered_damped_square_summable ε hpos hlim
  intro j
  obtain ⟨C, hC⟩ := henergy j
  exact ⟨C, (summable_normalizedEnergy_iff_pareto hZ _).mp hC⟩

/-- The exact canonical centering used by the paper, as a real coordinate.
The analytic identity for this centering is supplied by the existing project.
The small-damping summability input is still explicit. -/
theorem riemannHypothesis_of_canonical_damped_normalizedEnergy_sequence
    {Z : ℝ} (hZ : 0 < Z)
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ j, Summable (normalizedEnergy Z
      (fun n => dampedMobiusPrefix (ε j) n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε j : ℂ))).re))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_centered_damped_normalizedEnergy_sequence hZ ε hpos hlim
  exact fun j => ⟨(1 / riemannZeta (1 + (ε j : ℂ))).re, henergy j⟩

/-- Arbitrarily small admissible positive dampings suffice, with arbitrary
centers and without choosing a damping sequence. -/
theorem riemannHypothesis_of_arbitrarily_small_centered_damped_normalizedEnergy
    {Z : ℝ} (hZ : 0 < Z)
    (henergy : ∀ δ : ℝ, 0 < δ → ∃ ε C : ℝ,
      0 < ε ∧ ε < δ ∧ Summable (normalizedEnergy Z
        (fun n => dampedMobiusPrefix ε n - (n : ℝ) * C))) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro ρ hhalf hone hz
  obtain ⟨δ, hδ, hbad⟩ :=
    right_half_zero_eventually_not_centered_damped_square_summable ρ hhalf hone hz
  obtain ⟨ε, C, hε, hεδ, hs⟩ := henergy δ hδ
  exact hbad ε hε hεδ C ((summable_normalizedEnergy_iff_pareto hZ _).mp hs)

/-- The same contradiction gives the full small-damping obstruction under Q. -/
theorem right_half_zero_eventually_not_centered_damped_normalizedEnergy
    {Z : ℝ} (hZ : 0 < Z)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ C : ℝ,
      ¬ Summable (normalizedEnergy Z
        (fun n => dampedMobiusPrefix ε n - (n : ℝ) * C)) := by
  obtain ⟨δ, hδ, hbad⟩ :=
    right_half_zero_eventually_not_centered_damped_square_summable ρ hhalf hone hz
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ C hs
  exact hbad ε hε hεδ C ((summable_normalizedEnergy_iff_pareto hZ _).mp hs)

end RiemannResearch.RH.Pareto.ZetaTwo

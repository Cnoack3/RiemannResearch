import RiemannResearch.Analysis.CofinalRemainderAbsorption
import RiemannResearch.RH.ParetoResidueZeroScreening
import RiemannResearch.RH.CenteredMeanSquarefreeConverse

/-!
# Relative error after screening by finitely many critical zeros

Section 9 of the Mellin/prime-orbit handoff uses strict absorption of the
remaining Pareto error. The limit of the *relative* remainder on failure of
RH is one. The first-order loss of the relative remainder has an explicit
coefficient determined by the screening ordinates and the limiting legal
projection error. A strict absorption bound on a cofinal set already suffices.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin

open MellinFrequency (criticalPoint)
open ParetoBeurlingMellinObstruction (normalizedResidueSpan)

variable {ι : Type*} [Fintype ι]

/-- If RH fails, the limiting distance of the constant from the closed legal
span is strictly positive. -/
theorem lcm_limit_error_pos_of_not_rh (h : ¬ RiemannHypothesis) :
    0 < ‖hilbertOne - normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2 := by
  by_contra! hn
  have he := le_antisymm hn (sq_nonneg _)
  let γ : Fin 0 → ℝ := Fin.elim0
  have hi : Function.Injective γ := fun i => Fin.elim0 i
  have hp : ∀ i, 0 < γ i := fun i => Fin.elim0 i
  have hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0 := fun i => Fin.elim0 i
  apply h
  apply riemannHypothesis_of_lcm_remainder γ hi hp hz
  simpa only [he] using lcmRemainder_tendsto_limit γ hi hp hz

/-- If RH fails, the relative remainder converges to one and its first-order
loss has an exact coefficient at the ordinary conductor cutoff scale. -/
theorem lcm_relative_remainder_asymptotics_of_not_rh (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hp : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) (h : ¬ RiemannHypothesis) :
    Tendsto (fun M => lcmRemainder (fun i => criticalPoint (γ i)) M / lcmError M)
      atTop (𝓝 1) ∧
    Tendsto (fun M : ℕ => (M : ℝ) *
      (lcmError M - lcmRemainder (fun i => criticalPoint (γ i)) M) / lcmError M)
      atTop (𝓝 ((2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) /
        ‖hilbertOne - normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2)) :=
  RiemannResearch.Analysis.common_positive_limit_relative_loss
    (lcm_limit_error_pos_of_not_rh h) lcmError_tendsto
    (lcmRemainder_tendsto_limit γ hγ hp hz) (lcmError_sub_remainder_cutoff_tendsto γ hγ hp hz)

/-- For each prescribed strict factor, cofinal absorption with some vanishing
additive budget is equivalent to RH. Under RH the difference of the two terms
itself supplies a budget, which can be taken in absolute value. -/
theorem riemannHypothesis_iff_cofinal_remainder_absorption (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hp : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) (θ : ℝ) (hθ : θ < 1) :
    RiemannHypothesis ↔ ∃ B : ℕ → ℝ, (∀ M, 0 ≤ B M) ∧ Tendsto B atTop (𝓝 0) ∧
      ∃ᶠ M in atTop, lcmRemainder (fun i => criticalPoint (γ i)) M ≤ θ * lcmError M + B M := by
  let E := ‖hilbertOne - normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2
  have hr : Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop (𝓝 E) :=
    lcmRemainder_tendsto_limit γ hγ hp hz
  refine Iff.trans (b := E = 0) ?_ (RiemannResearch.Analysis.common_limit_zero_iff_cofinal_absorption
    (sq_nonneg _) lcmError_tendsto hr hθ)
  constructor
  · intro h
    apply tendsto_nhds_unique hr
    exact (lcm_remainder_tendsto_zero_iff_naturalApproximation γ hγ hp hz).mpr
      (PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.mp h)
  · intro he
    change E = 0 at he
    apply riemannHypothesis_of_lcm_remainder γ hγ hp hz
    simpa only [he] using hr

/-- Pure relative absorption on arbitrarily large cutoffs controls the actual
total squared error at the reciprocal-cutoff scale with a zero-dependent constant. -/
theorem frequently_cutoff_error_bound_of_relative_absorption (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hp : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) (θ : ℝ) (hθ : θ < 1)
    (hrel : ∃ᶠ M in atTop, lcmRemainder (fun i => criticalPoint (γ i)) M ≤ θ * lcmError M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ M : ℕ in atTop, (M : ℝ) * lcmError M ≤
      (2 * (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) + ε) / (1 - θ) :=
  RiemannResearch.Analysis.frequently_scaled_error_le_of_relative_absorption
    (fun M : ℕ => Nat.cast_nonneg M) hθ
    (lcmError_sub_remainder_cutoff_tendsto γ hγ hp hz) hrel hε

end RiemannResearch.RH.Pareto.ResidueMellin

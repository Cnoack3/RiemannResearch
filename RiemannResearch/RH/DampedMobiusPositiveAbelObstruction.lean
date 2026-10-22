/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PositiveAbelObstruction
import RiemannResearch.RH.DampedMobiusLoglogStretchedMovingBand

/-!
# Fixed-subhalf obstruction for the supplied positive Abel certificate

Application of the general sublinear-profile obstruction to the endpoint profile
in `MertensStretchedContinuation20260927.md`. The signed error itself is not
bounded below here, and fixed-subhalf finite energy remains an open question.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Every fixed subhalf damping eventually lies outside the verified
optimized moving band, for every fixed band coefficient. This is a
limitation of that band condition, not an arithmetic impossibility. -/
theorem dampedMobius_loglog_stretched_fixed_subhalf_eventually_not_mem
    (ε c : ℝ) (hε : ε < (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    ∀ᶠ j in atTop, ¬ dampedMobiusLoglogStretchedBand c (M j) ε := by
  let L : ℕ → ℝ := fun j => 6 + Real.log ((M j + 1 : ℕ) : ℝ)
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM)))
  have hsmall := eventually_profile_lt_linear (logProductPower (1 / 11))
    (tendsto_logProductPower_div_self (1 / 11) (by norm_num) (by norm_num))
    c ((1 / 2 : ℝ) - ε) (by linarith)
  filter_upwards [hL.eventually hsmall] with j hj
  exact not_le.mpr hj

/-- The boundary term of the positive Abel certificate built using the
verified endpoint profile diverges for every fixed subhalf damping.
The shift from `M+1` in the increasing weight to `M+2` in the endpoint
residual is retained exactly. No lower bound on the actual error is used. -/
theorem dampedMobius_loglog_stretched_positiveAbel_terminal_tendsto_atTop
    (ε a C : ℝ) (hε : ε < (1 / 2 : ℝ)) (hC : 0 < C)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => C * Real.exp
      (((1 / 2 : ℝ) - ε) * Real.log ((M j + 1 : ℕ) : ℝ) -
        a * logProductPower (1 / 11) (6 + Real.log ((M j + 2 : ℕ) : ℝ))))
      atTop atTop := by
  let L : ℕ → ℝ := fun j => 6 + Real.log ((M j + 2 : ℕ) : ℝ)
  let s : ℕ → ℝ := fun j => Real.log ((M j + 1 : ℕ) : ℝ)
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 2).comp hM)))
  apply positiveAbel_shifted_terminal_tendsto_atTop (logProductPower (1 / 11))
    (tendsto_logProductPower_div_self (1 / 11) (by norm_num) (by norm_num))
    a ((1 / 2 : ℝ) - ε) C (6 + Real.log 2) (by linarith) hC L s hL
  apply Eventually.of_forall
  intro j
  have hmul : ((M j + 2 : ℕ) : ℝ) ≤ 2 * ((M j + 1 : ℕ) : ℝ) := by
    have hnonneg : 0 ≤ (M j : ℝ) := by positivity
    push_cast
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < ((M j + 2 : ℕ) : ℝ)) hmul
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlog
  dsimp [L, s]
  linarith

end RiemannResearch.RH.Pareto

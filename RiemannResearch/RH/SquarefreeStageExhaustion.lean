/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.MeanOneChargeBounds

/-!
# A concrete exhaustive squarefree divisor chain

The primorial construction discharges the finite common-period and exhaustion
premises in the physical mean-one approximation problem. It supplies a bounded
charge limit, without identifying that limit with the arithmetic endpoint.
Source: standard primorial identities in Mathlib; physical application developed
from PhysicalMeanOneAdvance20261008.md.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.SquarefreeStageExhaustion
open PhysicalPacketCore MeanOneChargeBounds

def primorialPeriod (n : ℕ) : ℕ := primorial (n + 3)

theorem primorialPeriod_squarefree (n : ℕ) : Squarefree (primorialPeriod n) :=
  squarefree_primorial (n + 3)

theorem primorialPeriod_pos (n : ℕ) : 0 < primorialPeriod n := primorial_pos _

theorem primorialPeriod_nested {n m : ℕ} (h : n ≤ m) :
    primorialPeriod n ∣ primorialPeriod m :=
  primorial_dvd_primorial (Nat.add_le_add_right h 3)

theorem primorialPeriod_six_dvd (n : ℕ) : 6 ∣ primorialPeriod n := by
  have h : primorial 3 = 6 := by decide
  rw [← h]
  exact primorial_dvd_primorial (by omega)

theorem primorialPeriod_gt_two (n : ℕ) : 2 < primorialPeriod n := by
  have h := Nat.le_of_dvd (primorialPeriod_pos n) (primorialPeriod_six_dvd n)
  omega

theorem squarefree_dvd_primorialPeriod (d n : ℕ) (hd : Squarefree d) (hdn : d ≤ n) :
    d ∣ primorialPeriod n :=
  dvd_trans hd.dvd_primorial (primorial_dvd_primorial (by omega))

theorem squarefree_eventually_dvd_primorialPeriod (d : ℕ) (hd : Squarefree d) :
    ∀ᶠ n in atTop, d ∣ primorialPeriod n := by
  filter_upwards [eventually_ge_atTop d] with n hn
  exact squarefree_dvd_primorialPeriod d n hd hn

/-- Every finite squarefree support has an actual squarefree common period,
containing conductor six and hence satisfying the physical inertia hypotheses. -/
theorem finite_squarefree_common_period (s : Finset ℕ)
    (hs : ∀ d ∈ s, Squarefree d) :
    ∃ L : ℕ, 2 < L ∧ Squarefree L ∧ 6 ∣ L ∧ ∀ d ∈ s, d ∣ L := by
  refine ⟨primorialPeriod (s.sup id), primorialPeriod_gt_two _,
    primorialPeriod_squarefree _, primorialPeriod_six_dvd _, ?_⟩
  intro d hd
  exact squarefree_dvd_primorialPeriod d _ (hs d hd) (Finset.le_sup (f := id) hd)

theorem primorialPeriod_tendsto_atTop : Tendsto primorialPeriod atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans ((Nat.le_add_right n 3).trans le_primorial_self)

/-- This is convergence to some charge, not an assertion of saturation. -/
theorem exists_primorial_charge_limit :
    ∃ C : ℝ, C ∈ Set.Icc (-8 * Real.sqrt 3) (-4 * Real.pi) ∧
      Tendsto (fun n => inverseCharge (divisorPackets (primorialPeriod n)))
        atTop (𝓝 C) :=
  exists_charge_limit_of_divisor_chain primorialPeriod
    (fun _ _ h => primorialPeriod_nested h) primorialPeriod_six_dvd primorialPeriod_gt_two

end RiemannResearch.RH.Pareto.SquarefreeStageExhaustion

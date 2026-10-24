import RiemannResearch.RH.ParetoMellinCapacityStability

/-!
# Independent Hilbert and Mellin exhaustion limits

Source: uniform physical capacity stability, 24 October 2026. The physical
approximants and observation depth may move at unrelated cofinal rates.
The exact full integral remainder is carried through the limit; the chosen
Mellin family need not be complete.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
variable {α : Type*} {l : Filter α}

/-- Even the finite probe family may change with the approximation index.
There is no separation constant and no bound on the number of observations. -/
theorem mellinPhysicalCapacity_moving_perturbation_tendsto
    (F : α → ThresholdHilbert) (f : ThresholdHilbert) (hF : Tendsto F l (𝓝 f))
    (N : α → ℕ) (s : (i : α) → Fin (N i) → ℂ)
    (hs : ∀ i j, (1 / 2 : ℝ) < (s i j).re)
    (hinj : ∀ i, Function.Injective (s i)) :
    Tendsto (fun i =>
      mellinInverseCapacity (s i) (fun j => paretoMellin (F i) (s i j)) -
      mellinInverseCapacity (s i) (fun j => paretoMellin f (s i j))) l (𝓝 0) := by
  have hd : Tendsto (fun i => ‖F i - f‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hF.sub (tendsto_const_nhds (x := f))).norm
  have hb : Tendsto (fun i => ‖F i - f‖ * (‖F i‖ + ‖f‖)) l (𝓝 0) := by
    simpa only [zero_mul] using hd.mul (hF.norm.add tendsto_const_nhds)
  apply squeeze_zero_norm _ hb
  intro i
  simpa only [Real.norm_eq_abs] using
    mellinPhysicalCapacity_abs_sub_le (F i) f (s i) (hs i)
      ((mellinCauchyGram_det_ne_zero_iff_injective (s i) (hs i)).mpr (hinj i))

/-- Observation depth and physical approximation have independent limits. -/
theorem mellinPrefixCapacity_moving_tendsto
    (F : α → ThresholdHilbert) (f : ThresholdHilbert) (hF : Tendsto F l (𝓝 f))
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re)
    (hinj : Function.Injective z) (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => mellinPrefixCapacity z (fun j => paretoMellin (F i) (z j)) (N i))
      l (𝓝 (mellinCapacityLimit f z)) := by
  have hd := mellinPhysicalCapacity_moving_perturbation_tendsto F f hF N
    (fun i j => z j.val) (fun i j => hz j.val)
    (fun i => hinj.comp Fin.val_injective)
  have hc := (mellinPrefixCapacity_physical_tendsto f z hz hinj).comp hN
  simpa only [mellinPrefixCapacity, sub_add_cancel, zero_add, Function.comp_apply]
    using hd.add hc

/-- The full integral remainder also has the independent two-parameter limit. -/
theorem mellinProjectionRemainder_moving_tendsto
    (F : α → ThresholdHilbert) (f : ThresholdHilbert) (hF : Tendsto F l (𝓝 f))
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re)
    (hinj : Function.Injective z) (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => mellinProjectionRemainder (F i) (fun j : Fin (N i) => z j.val))
      l (𝓝 (mellinUnobservedEnergy f z)) := by
  have he (i : α) : mellinProjectionRemainder (F i) (fun j : Fin (N i) => z j.val) =
      ‖F i‖ ^ 2 - mellinPrefixCapacity z (fun j => paretoMellin (F i) (z j)) (N i) := by
    have h := mellinPrefixInnovation_physical_completion (F i) z hz hinj (N i)
    rw [mellinPrefixInnovation_sum z _ hz hinj] at h
    linarith
  have ht := (hF.norm.pow 2).sub (mellinPrefixCapacity_moving_tendsto F f hF z hz hinj N hN)
  simpa only [he, mellinUnobservedEnergy] using ht

/-- A complete vanishing criterion retains both captured and unobserved energy.
The remainder cannot be omitted without an additional completeness theorem. -/
theorem mellin_zero_iff_moving_observations_vanish [NeBot l]
    (F : α → ThresholdHilbert) (f : ThresholdHilbert) (hF : Tendsto F l (𝓝 f))
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re)
    (hinj : Function.Injective z) (N : α → ℕ) (hN : Tendsto N l atTop) :
    f = 0 ↔
      Tendsto (fun i => mellinPrefixCapacity z (fun j => paretoMellin (F i) (z j)) (N i))
        l (𝓝 0) ∧
      Tendsto (fun i => mellinProjectionRemainder (F i) (fun j : Fin (N i) => z j.val))
        l (𝓝 0) := by
  have hc := mellinPrefixCapacity_moving_tendsto F f hF z hz hinj N hN
  have hr := mellinProjectionRemainder_moving_tendsto F f hF z hz hinj N hN
  rw [mellin_zero_iff_both_energies_zero f z hz hinj]
  constructor
  · rintro ⟨hc0, hr0⟩
    exact ⟨hc0 ▸ hc, hr0 ▸ hr⟩
  · rintro ⟨hc0, hr0⟩
    exact ⟨tendsto_nhds_unique hc hc0, tendsto_nhds_unique hr hr0⟩

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer
variable {α : Type*} {l : Filter α}

/-- Actual Q approximants inherit both independent limits through the bounded
complete-sequence map, without identifying the Q and Pareto optimizers. -/
theorem qMellin_moving_observations_tendsto
    (F : α → QHilbert) (f : QHilbert) (hF : Tendsto F l (𝓝 f))
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re)
    (hinj : Function.Injective z) (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => mellinPrefixCapacity z (fun j => qMellin (F i) (z j)) (N i))
      l (𝓝 (mellinCapacityLimit (toPareto f) z)) ∧
    Tendsto (fun i => mellinProjectionRemainder (toPareto (F i))
      (fun j : Fin (N i) => z j.val)) l (𝓝 (mellinUnobservedEnergy (toPareto f) z)) := by
  have hP : Tendsto (fun i => toPareto (F i)) l (𝓝 (toPareto f)) := by
    simpa only [Function.comp_def, toParetoCLM_apply] using
      (toParetoCLM.continuous.tendsto f).comp hF
  exact ⟨mellinPrefixCapacity_moving_tendsto _ _ hP z hz hinj N hN,
    mellinProjectionRemainder_moving_tendsto _ _ hP z hz hinj N hN⟩

end RiemannResearch.RH.QMellinTransfer

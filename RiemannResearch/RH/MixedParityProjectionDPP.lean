import RiemannResearch.Probability.DeterminantalProcess
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedCaptureZeroPair
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A coupled determinantal probe for the mixed-conductor parity projection

A single uniform threshold couples all one-site observations of the normalized
mixed capture of the centered parity packet. Expected vacancy is precisely the
remaining normalized squared distance. The actual relative projection gains
are the conditional probabilities of first entry at the next conductor. A
nonreal zero to the right of the line forces positive limiting vacancy.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains.MixedProbe
open CoefficientStabilization RiemannResearch.Probability.DPP

/-- The total energy available to the mixed projection of the centered parity packet. -/
def target : ℝ := Real.log 2 - (Real.log 2) ^ 2

/-- Finite inclusion probability of the distinguished normalized parity probe. -/
def occupancy (B : ℕ) : ℝ :=
  ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 / target

def fullOccupancy : ℝ := ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 / target

theorem target_pos : 0 < target := by
  have he := deficit_add_capture 0
  change 0 < Real.log 2 - (Real.log 2) ^ 2
  linarith [deficit_pos 0, sq_nonneg ‖(mixedSpace (Finset.Icc 2 0)).starProjection (ramanujanPacketHilbert 2)‖]

theorem one_sub_occupancy (B : ℕ) : 1 - occupancy B = deficit B / target := by
  have he := deficit_add_capture B
  change deficit B + _ = target at he
  unfold occupancy
  field_simp [target_pos.ne']
  linarith only [he]

theorem occupancy_bounds (B : ℕ) : 0 ≤ occupancy B ∧ occupancy B < 1 :=
  ⟨div_nonneg (sq_nonneg _) target_pos.le, by
    have h := one_sub_occupancy B
    linarith [div_pos (deficit_pos B) target_pos]⟩

theorem occupancy_monotone : Monotone occupancy := by
  intro A B hAB
  have hgain : 0 ≤ gain A B := sq_nonneg _
  have hle : deficit B ≤ deficit A := by linarith [deficit_step hAB]
  have hh := div_le_div_of_nonneg_right hle target_pos.le
  linarith only [one_sub_occupancy A, one_sub_occupancy B, hh]

theorem occupancy_tendsto : Tendsto occupancy atTop (𝓝 fullOccupancy) := by
  have hm : Monotone (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  have h := Submodule.starProjection_tendsto_closure_iSup
    (fun N => mixedSpace (Finset.Icc 2 N)) hm (ramanujanPacketHilbert 2)
  exact (h.norm.pow 2).div_const target

theorem fullOccupancy_bounds : 0 ≤ fullOccupancy ∧ fullOccupancy ≤ 1 :=
  ⟨div_nonneg (sq_nonneg _) target_pos.le,
    le_of_tendsto occupancy_tendsto (Eventually.of_forall (fun B => (occupancy_bounds B).2.le))⟩

/-- The shared random threshold for all mixed conductor cutoffs. -/
def thresholdLaw : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance thresholdLaw_probability : IsProbabilityMeasure thresholdLaw := by
  constructor
  simp [thresholdLaw, Real.volume_Ioc]

/-- Occupation of the single distinguished site for threshold probability p. -/
def probe (p u : ℝ) : Set Unit := {_i | u ∈ Ioc 0 p}

private theorem threshold_interval_mass {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    thresholdLaw.real (Ioc a b) = b - a := by
  have hs : Ioc a b ⊆ Ioc (0 : ℝ) 1 := fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans hb⟩
  rw [Measure.real, thresholdLaw, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hs, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- Each one-site observation is a DPP with the actual normalized capture as kernel. -/
theorem probe_isDPP {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    IsDPP thresholdLaw (probe p) (fun _ _ : Unit => p) := by
  constructor
  · intro i
    exact measurableSet_Ioc
  · intro m e
    have hm : m ≤ 1 := by simpa using Fintype.card_le_of_injective e e.injective
    interval_cases m
    · simp
    · simp only [probe, Set.mem_ofPred_eq, forall_const, Matrix.det_fin_one, Matrix.of_apply]
      rw [show {u : ℝ | u ∈ Ioc 0 p} = Ioc 0 p from Set.ext (fun _ => Iff.rfl)]
      simpa only [sub_zero] using threshold_interval_mass (a := 0) le_rfl hp hp'

theorem finite_probe_vacancy (B : ℕ) :
    thresholdLaw.real {u | () ∉ probe (occupancy B) u} = deficit B / target :=
  ((probe_isDPP (occupancy_bounds B).1 (occupancy_bounds B).2.le).vacancy ()).trans
    (one_sub_occupancy B)

/-- Given current absence, the conditional next-entry probability is precisely
the relative gain of the actual mixed-conductor projection. -/
theorem entry_ratio_eq_relativeGain (B : ℕ) :
    thresholdLaw.real {u | () ∈ probe (occupancy (B + 1)) u ∧ () ∉ probe (occupancy B) u} /
      thresholdLaw.real {u | () ∉ probe (occupancy B) u} = relativeGain B := by
  have he : {u | () ∈ probe (occupancy (B + 1)) u ∧ () ∉ probe (occupancy B) u} =
      Ioc (occupancy B) (occupancy (B + 1)) := by
    ext u
    change (0 < u ∧ u ≤ occupancy (B + 1)) ∧ ¬(0 < u ∧ u ≤ occupancy B) ↔ _
    constructor
    · rintro ⟨⟨hu, hu'⟩, hn⟩
      exact ⟨lt_of_not_ge (fun h => hn ⟨hu, h⟩), hu'⟩
    · rintro ⟨hu, hu'⟩
      exact ⟨⟨(occupancy_bounds B).1.trans_lt hu, hu'⟩, fun h => (not_le_of_gt hu) h.2⟩
  rw [he, threshold_interval_mass (occupancy_bounds B).1 (occupancy_monotone (Nat.le_succ B))
    (occupancy_bounds (B + 1)).2.le, finite_probe_vacancy]
  have hd := deficit_step (Nat.le_succ B)
  have h1 := one_sub_occupancy B
  have h2 := one_sub_occupancy (B + 1)
  field_simp [target_pos.ne'] at h1 h2
  unfold relativeGain
  field_simp [target_pos.ne', (deficit_pos B).ne']
  nlinarith only [h1, h2, hd]

/-- Limiting vacancy is an explicit function of the optimal legal Pareto error. -/
theorem full_probe_vacancy_eq_limitEnergy :
    thresholdLaw.real {u | () ∉ probe fullOccupancy u} =
      (Real.log 2) ^ 2 * limitEnergy / ((1 - limitEnergy) * target) := by
  rw [(probe_isDPP fullOccupancy_bounds.1 fullOccupancy_bounds.2).vacancy ()]
  change 1 - ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 / target = _
  rw [full_mixed_capture_eq_limitEnergy]
  have he : 1 - limitEnergy ≠ 0 := by linarith [limitEnergy_lt_period5040_bound]
  have hid (l d t : ℝ) (h : t = l - l ^ 2) (h₁ : 1 - d ≠ 0) (ht : t ≠ 0) :
      1 - (l - l ^ 2 / (1 - d)) / t = l ^ 2 * d / ((1 - d) * t) := by
    field_simp [h₁, ht]
    rw [h]
    ring
  exact hid (Real.log 2) limitEnergy target rfl he target_pos.ne'

/-- A right-of-line nonreal zero leaves strictly positive limiting vacancy. -/
theorem full_probe_vacancy_pos_of_zero (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hi : s.im ≠ 0) (hz : riemannZeta s = 0) :
    0 < thresholdLaw.real {u | () ∉ probe fullOccupancy u} := by
  rw [(probe_isDPP fullOccupancy_bounds.1 fullOccupancy_bounds.2).vacancy ()]
  apply sub_pos.mpr
  apply (div_lt_one target_pos).mpr
  have h := full_mixed_capture_upper_of_zeta_zero s hs hi hz
  exact h.1.trans_lt h.2

/-- The limiting parity probe is occupied almost surely precisely when the
finite relative gains have divergent total sum. -/
theorem full_probe_ae_iff_relativeGain_not_summable :
    (∀ᵐ u ∂thresholdLaw, () ∈ probe fullOccupancy u) ↔ ¬ Summable relativeGain := by
  rw [(probe_isDPP fullOccupancy_bounds.1 fullOccupancy_bounds.2).mem_ae_iff (),
    ← fixed_capture_saturation_iff_relativeGain_not_summable]
  have hm : Monotone (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  have h : Tendsto (fun N : ℕ => ‖(mixedSpace (Finset.Icc 2 N)).starProjection
      (ramanujanPacketHilbert 2)‖ ^ 2) atTop
      (𝓝 (‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2)) :=
    (Submodule.starProjection_tendsto_closure_iSup
      (fun N => mixedSpace (Finset.Icc 2 N)) hm (ramanujanPacketHilbert 2)).norm.pow 2
  constructor
  · intro he
    change ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 / target = 1 at he
    have hh := (div_eq_one_iff_eq target_pos.ne').mp he
    simpa only [hh, target] using h
  · intro ht
    have hh := tendsto_nhds_unique h ht
    change ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 / target = 1
    exact (div_eq_one_iff_eq target_pos.ne').mpr hh

theorem riemannHypothesis_of_full_probe_ae
    (h : ∀ᵐ u ∂thresholdLaw, () ∈ probe fullOccupancy u) : RiemannHypothesis :=
  riemannHypothesis_of_mixed_relativeGain_not_summable (full_probe_ae_iff_relativeGain_not_summable.mp h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains.MixedProbe

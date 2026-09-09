import RiemannResearch.Analysis.ConductorL2Inverse
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, §4.
The actual bounded L² conductor inverse does not preserve a finite left
support endpoint: a compact indicator has an inverse with nonzero values
on positive-measure sets below every real threshold.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RiemannResearch.Analysis.ConductorL2Inverse

/-- A compact interval indicator, represented in the actual Lebesgue L² space. -/
def box (a b : ℝ) : L2 :=
  indicatorConstLp (μ := volume) (s := Set.Ico a b) 2
    measurableSet_Ico (by simp) (1 : ℂ)

theorem box_coe_ae (a b : ℝ) :
    box a b =ᵐ[volume] (Set.Ico a b).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Restriction into the L² space of the restricted measure, as a continuous map. -/
def restrict (s : Set ℝ) : L2 →L[ℝ] Lp ℂ 2 (volume.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa using (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := s)))

theorem restrict_coe_ae (s : Set ℝ) (f : L2) :
    restrict s f =ᵐ[volume.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

def leftBlock (a : ℝ) (m : ℕ) : Set ℝ :=
  Set.Ico (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)

private theorem translate_box_membership {a : ℝ} (ha : 0 < a) (m j : ℕ)
    {x : ℝ} (hx : x ∈ leftBlock a m) :
    x - (-((j : ℝ) + 1) * a) ∈ Set.Ico 0 a ↔ j = m := by
  change -((m : ℝ) + 1) * a ≤ x ∧ x < -(m : ℝ) * a at hx
  rcases hx with ⟨hlo,hhi⟩
  constructor
  · intro hz
    rcases hz with ⟨hzlo,hzhi⟩
    rcases lt_trichotomy j m with hj | hj | hj
    · have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
      have hm := mul_le_mul_of_nonneg_right hj' ha.le
      nlinarith
    · exact hj
    · have hj' : (m : ℝ) + 1 ≤ j := by exact_mod_cast hj
      have hm := mul_le_mul_of_nonneg_right hj' ha.le
      nlinarith
  · rintro rfl
    constructor <;> nlinarith

private theorem restrict_translate_box {a : ℝ} (ha : 0 < a) (m j : ℕ) :
    restrict (leftBlock a m) (translate (-((j : ℝ) + 1) * a) (box 0 a)) =
      if j = m then restrict (leftBlock a m)
        (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)) else 0 := by
  apply Lp.ext
  have hb := (measurePreserving_sub_right volume (-((j : ℝ) + 1) * a)).quasiMeasurePreserving.ae
    (box_coe_ae 0 a)
  have hmem : ∀ᵐ x ∂volume.restrict (leftBlock a m), x ∈ leftBlock a m :=
    ae_restrict_mem (by exact measurableSet_Ico)
  by_cases hj : j = m
  · rw [if_pos hj]
    filter_upwards [restrict_coe_ae (leftBlock a m)
        (translate (-((j : ℝ) + 1) * a) (box 0 a)),
      restrict_coe_ae (leftBlock a m)
        (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)),
      ae_restrict_of_ae (translate_coe_ae (-((j : ℝ) + 1) * a) (box 0 a)),
      ae_restrict_of_ae hb,
      ae_restrict_of_ae (box_coe_ae (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)), hmem]
      with x hx hr ht hi hb hxmem
    rw [hx, hr, ht, hi, hb]
    rw [Set.indicator_of_mem ((translate_box_membership ha m j hxmem).mpr hj),
      Set.indicator_of_mem (show x ∈ Set.Ico (-((m : ℝ) + 1) * a)
        (-(m : ℝ) * a) from hxmem)]
  · rw [if_neg hj]
    filter_upwards [restrict_coe_ae (leftBlock a m)
        (translate (-((j : ℝ) + 1) * a) (box 0 a)),
      ae_restrict_of_ae (translate_coe_ae (-((j : ℝ) + 1) * a) (box 0 a)),
      ae_restrict_of_ae hb, hmem, Lp.coeFn_zero (ℂ) 2 (volume.restrict (leftBlock a m))]
      with x hx ht hi hxmem hz
    rw [hx, ht, hi, hz]
    exact Set.indicator_of_notMem (fun h => hj ((translate_box_membership ha m j hxmem).mp h)) _

/-- Exact inverse value on each left interval, as an identity in restricted L². -/
theorem inverse_box_restrict {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (m : ℕ) :
    restrict (leftBlock a m) (inverse q a (box 0 a)) =
      (-(q⁻¹) * q ^ m) • restrict (leftBlock a m)
        (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)) := by
  let F := (restrict (leftBlock a m)).comp (ContinuousLinearMap.apply ℝ L2 (box 0 a))
  have hs := (inverse_hasSum_translations hq0.le hq1 a).mapL F
  have hs' : HasSum (fun j : ℕ => if j = m then
      (-(q⁻¹) * q ^ m) • restrict (leftBlock a m)
        (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)) else 0)
      (restrict (leftBlock a m) (inverse q a (box 0 a))) := by
    convert hs using 1
    · funext j
      simp only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.smul_apply, map_smul, restrict_translate_box ha m j]
      split_ifs with hj
      · subst j; rfl
      · simp
    · simp [F]
  exact hs'.unique (hasSum_ite_eq m _)

/-- The inverse equals a nonzero constant almost everywhere on each full left block. -/
theorem inverse_box_value_ae {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (m : ℕ) : ∀ᵐ x ∂volume.restrict (leftBlock a m),
      inverse q a (box 0 a) x = ((-(q⁻¹) * q ^ m : ℝ) : ℂ) := by
  have heq := inverse_box_restrict hq0 hq1 ha m
  have hae := Lp.coeFn_smul (-(q⁻¹) * q ^ m)
    (restrict (leftBlock a m) (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)))
  rw [← heq] at hae
  filter_upwards [hae, restrict_coe_ae (leftBlock a m) (inverse q a (box 0 a)),
    restrict_coe_ae (leftBlock a m) (box (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)),
    ae_restrict_of_ae (box_coe_ae (-((m : ℝ) + 1) * a) (-(m : ℝ) * a)),
    ae_restrict_mem (show MeasurableSet (leftBlock a m) from measurableSet_Ico)]
    with x hs hi hr hb hm
  simp only [Pi.smul_apply] at hs
  rw [hi, hr, hb, Set.indicator_of_mem (show x ∈ Set.Ico (-((m : ℝ) + 1) * a)
    (-(m : ℝ) * a) from hm)] at hs
  simpa using hs

theorem leftBlock_volume (a : ℝ) (m : ℕ) :
    volume (leftBlock a m) = ENNReal.ofReal a := by
  simp only [leftBlock, Real.volume_Ico]
  congr 1
  ring

/-- Nonzero values occupy a set of full block measure, not just selected points. -/
theorem inverse_box_nonzero_block_measure {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 < a) (m : ℕ) :
    volume {x ∈ leftBlock a m | inverse q a (box 0 a) x ≠ 0} = ENNReal.ofReal a := by
  have hc : (((-(q⁻¹) * q ^ m : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (ne_of_gt hq0)))
      (pow_ne_zero m (ne_of_gt hq0))
  have hg : ∀ᵐ x ∂volume.restrict (leftBlock a m),
      inverse q a (box 0 a) x ≠ 0 :=
    (inverse_box_value_ae hq0 hq1 ha m).mono (fun x hx => hx ▸ hc)
  have hi : ∀ᵐ x ∂volume, x ∈ leftBlock a m → inverse q a (box 0 a) x ≠ 0 :=
    (ae_restrict_iff' (show MeasurableSet (leftBlock a m) from measurableSet_Ico)).mp hg
  calc
    volume {x ∈ leftBlock a m | inverse q a (box 0 a) x ≠ 0} =
        volume (leftBlock a m) := by
      apply measure_congr
      filter_upwards [hi] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
    _ = ENNReal.ofReal a := leftBlock_volume a m

/-- No finite left endpoint bounds the essential support of this inverse. -/
theorem inverse_box_not_bounded_below {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 < a) (r : ℝ) :
    0 < volume {x : ℝ | x < r ∧ inverse q a (box 0 a) x ≠ 0} := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-r / a)
  have hm' : -r < (m : ℝ) * a := (div_lt_iff₀ ha).mp hm
  have hsub : {x ∈ leftBlock a m | inverse q a (box 0 a) x ≠ 0} ⊆
      {x : ℝ | x < r ∧ inverse q a (box 0 a) x ≠ 0} := by
    intro x hx
    refine ⟨?_, hx.2⟩
    have hh : x < -(m : ℝ) * a := hx.1.2
    linarith
  have hpos : 0 < volume {x ∈ leftBlock a m | inverse q a (box 0 a) x ≠ 0} := by
    rw [inverse_box_nonzero_block_measure hq0 hq1 ha m]
    exact ENNReal.ofReal_pos.mpr ha
  exact hpos.trans_le (measure_mono hsub)

/-- The compact seed has zero values almost everywhere outside its closed interval. -/
theorem box_zero_outside_ae (a b : ℝ) :
    ∀ᵐ x ∂volume, x ∉ Set.Icc a b → box a b x = 0 := by
  filter_upwards [box_coe_ae a b] with x hx
  intro hn
  rw [hx]
  exact Set.indicator_of_notMem (fun h => hn ⟨h.1, h.2.le⟩) _

/-- For every natural conductor greater than one, its actual L² inverse sends
this compact indicator to a function with essential support arbitrarily far left. -/
theorem natInverse_box_not_bounded_below {n : ℕ} (hn : 1 < n) (r : ℝ) :
    0 < volume {x : ℝ | x < r ∧ natInverse n (box 0 (Real.log n)) x ≠ 0} := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hs : 1 < Real.sqrt n := by
    have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    have hnon := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hp : 0 < Real.sqrt n := zero_lt_one.trans hs
  have hi : 0 < (Real.sqrt n)⁻¹ := inv_pos.mpr hp
  have hi1 : (Real.sqrt n)⁻¹ < 1 := by
    have heq : (Real.sqrt n)⁻¹ * Real.sqrt n = 1 := inv_mul_cancel₀ (ne_of_gt hp)
    nlinarith
  exact inverse_box_not_bounded_below hi hi1 (Real.log_pos hn') r

end RiemannResearch.Analysis.ConductorL2Inverse

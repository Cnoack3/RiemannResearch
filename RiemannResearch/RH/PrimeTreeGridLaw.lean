/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeHaarRows
import RiemannResearch.RH.QConductorLimits
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The Haar grid and the physical prime average

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, §2.4.
The signed CRT lift at each prime permutes a finite grid. This module uses
arbitrary grid permutations, proves the grid quadrature limit, and records
the opposite physical-Q limit for the unpermuted residue averages.
-/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
namespace RiemannResearch.RH.PrimeTreeHaarRows

def gridMean (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, f ((k : ℝ)/n)) / n

/-- Left endpoints of the equal grid, including the endpoint at zero. -/
theorem gridMean_tendsto (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (gridMean f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff_le.mp huc (ε/2) (half_pos hε)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ] with n hn hmesh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a := fun j : ℕ => (j : ℝ)/(n : ℝ)
  have hm (k : ℕ) : a k ≤ a (k+1) := by
    apply (div_le_div_iff_of_pos_right hnR).mpr
    exact_mod_cast Nat.le_succ k
  have hl (k : ℕ) : 0 ≤ a k := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hr (k : ℕ) (hk : k ≤ n) : a k ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hk)
  have hi (k : ℕ) (hk : k < n) : IntervalIntegrable f volume (a k) (a (k+1)) :=
    ContinuousOn.intervalIntegrable_of_Icc (hm k) (hf.mono (fun x hx => ⟨(hl k).trans hx.1,
      hx.2.trans (hr (k+1) hk)⟩))
  have hstep (k : ℕ) : a (k+1) - a k = 1/(n : ℝ) := by
    simp only [a, Nat.cast_add, Nat.cast_one]; ring
  have hpart := intervalIntegral.sum_integral_adjacent_intervals hi
  have hzero : a 0 = 0 := by simp [a]
  have hone : a n = 1 := by simp [a, hnR.ne']
  rw [hzero, hone] at hpart
  let e := fun k => f (a k)/(n : ℝ) - ∫ x in a k..a (k+1), f x
  have he (k : ℕ) (hk : k < n) : |e k| ≤ (ε/2) / n := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k+1))
      (C := ε/2) (f := fun x => f (a k)-f x) (by
        intro x hx
        rw [Set.uIoc_of_le (hm k)] at hx
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨(hl k).trans hx.1.le, hx.2.trans (hr _ hk)⟩
        have hd : dist (a k) x ≤ δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
          have hgap := hstep k
          linarith [hx.2]
        simpa only [Real.dist_eq, Real.norm_eq_abs] using hu _ ⟨hl k, hr k hk.le⟩ _ hx' hd)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi k hk), intervalIntegral.integral_const,
      smul_eq_mul, hstep, abs_of_nonneg (by positivity : 0 ≤ 1/(n : ℝ)), Real.norm_eq_abs] at hh
    simpa only [e, div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hh
  rw [Real.dist_eq, ← hpart]
  change |(∑ k ∈ Finset.range n, f (a k))/(n : ℝ) - _| < ε
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _)
  calc
    _ ≤ ∑ k ∈ Finset.range n, (ε/2)/(n : ℝ) :=
      Finset.sum_le_sum fun k hk => he k (Finset.mem_range.mp hk)
    _ = ε/2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hnR.ne']
    _ < ε := half_lt_self hε

/-- Uniform probability on one finite residue grid. -/
def gridLaw (n : ℕ) : Measure (Fin n) := ((n : ℝ≥0∞)⁻¹) • Measure.count

instance gridLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (gridLaw n) := by
  constructor
  simp [gridLaw, NeZero.ne n]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (by simp)

/-- Permuting grid labels leaves the expectation exactly invariant. -/
theorem gridLaw_integral (f : ℝ → ℝ) (n : ℕ) [NeZero n] (e : Equiv.Perm (Fin n)) :
    (∫ x, f (((e x).val : ℝ) / n) ∂gridLaw n) = gridMean f n := by
  rw [integral_fintype .of_finite]
  have hw (x : Fin n) : (gridLaw n).real {x} = (n : ℝ)⁻¹ := by
    simp [gridLaw, measureReal_def]
  simp only [hw, smul_eq_mul, ← Finset.mul_sum]
  rw [Equiv.sum_comp e (fun y : Fin n => f ((y.val : ℝ)/n)), gridMean, Finset.sum_range]
  ring

/-- The prime-coordinate law with arbitrary row-dependent grid permutations,
for each continuous test. Distinct positive conductors escaping to infinity
are enough. -/
theorem permuted_grid_average_ae (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (e : ∀ n j : ℕ, Equiv.Perm (Fin (p j)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun j => gridLaw (p j)), Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n, f (((e n j (ω j)).val : ℝ)/(p j)))/(n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  let μ := fun j => gridLaw (p j)
  let X := fun (n j : ℕ) (x : Fin (p j)) => f (((e n j x).val : ℝ)/(p j))
  have hm (n j : ℕ) : Measurable (X n j) := measurable_of_countable _
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hb (n j : ℕ) (x : Fin (p j)) : X n j x ∈ Set.Icc (-(C+1)) (C+1) := by
    have hpR : 0 < (p j : ℝ) := by exact_mod_cast NeZero.pos (p j)
    have hx : (((e n j x).val : ℝ)/(p j)) ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hpR.le, (div_le_one hpR).mpr (by exact_mod_cast (e n j x).isLt.le)⟩
    have hbound := abs_le.mp (show |X n j x| ≤ C from hC _ hx)
    exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
  have hz := product_row_average_ae μ X hm (-(C+1)) (C+1) (by linarith) hb
  have hmean (n j : ℕ) : (∫ ω, X n j (ω j) ∂Measure.infinitePi μ) = gridMean f (p j) := by
    have hh := integral_map (μ := Measure.infinitePi μ) (φ := Function.eval j) (f := X n j)
      (measurable_pi_apply j).aemeasurable (hm n j).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval μ j] at hh
    exact hh.symm.trans (gridLaw_integral f (p j) (e n j))
  have hc := ((gridMean_tendsto f hf).comp hp).cesaro_smul
  filter_upwards [hz] with ω hω
  have hsum := hω.add hc
  simp only [hmean, Finset.sum_sub_distrib, Function.comp_apply, smul_eq_mul, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change ((_ - _)/(n : ℝ) + (n : ℝ)⁻¹ * _) = _
  ring

/-- The same unpermuted prime averages at physical integers tend to zero
in the complete inverse-square Hilbert norm. -/
theorem physical_prime_average_zero (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, (2 : ℝ) • ZetaTwoHilbert.qResidue (p j))
      atTop (𝓝 0) := by
  have h : Tendsto (fun j => (2 : ℝ) • ZetaTwoHilbert.qResidue (p j)) atTop (𝓝 0) := by
    simpa using (ZetaTwoHilbert.qResidue_tendsto_zero p hp).const_smul (2 : ℝ)
  exact h.cesaro_smul

end RiemannResearch.RH.PrimeTreeHaarRows

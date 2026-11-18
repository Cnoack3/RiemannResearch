/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCollisionCertificate
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.Analysis.GaussianCellGeometry
import RiemannResearch.Analysis.MarkedFourierTail
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryPoisson
import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.MontgomeryExtendedFourierShoulder
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import RiemannResearch.Analysis.OrdinateCollisionRemainder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A uniform tail bound connecting the physical gaps and Fourier Fejér tests

A fixed physical triangle controls the squared occupancies in unfolded
half-unit cells. Applying the symmetric inverse-square envelope to these
cells gives a bound for the Fejér contribution away from zero. This is
independent of any minimum gap or pointwise microscopic occupancy estimate.
The strictly positive-gap PCC is the formulation in GLSS, arXiv:2503.15449,
equation (1.5). That conjecture and the short-window estimate imply the
complementary Fourier upper criterion by this bound.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor

open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open MontgomeryPoisson MontgomeryLocalMass MontgomeryPositiveGap
open OrdinateCollisionCertificate GaussianCellGeometry MarkedFourierTail

private theorem cauchy_pair_sum_le_triangle {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ i, ∑ j, cauchyWeight (x i - x j)) ≤
      32 * ∑ i, ∑ j, max (2 - |x i - x j|) 0 := by
  classical
  let s : Finset ι := Finset.univ
  let cell : ι → ℤ := fun i => Int.floor (x i)
  let m := occupancy s cell
  let e : ℤ → ℤ → ℝ := fun a b => inverseSquareEnvelope (a - b)
  have hs : (∑ a ∈ s.image cell, m a ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, if cell i = cell j then (1 : ℝ) else 0 := by
    rw [pair_sum_by_cells s cell (fun a b => if a = b then (1 : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro a ha
    symm
    rw [Finset.sum_eq_single a]
    · simp [pow_two, m]
    · intro b _ hab
      simp [Ne.symm hab]
    · exact fun hn => (hn ha).elim
  have htri : (∑ a ∈ s.image cell, m a ^ 2) ≤
      ∑ i ∈ s, ∑ j ∈ s, max (2 - |x i - x j|) 0 := by
    rw [hs]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs with h
    · have hi := Int.floor_le (x i)
      have hu := Int.lt_floor_add_one (x i)
      have hj := Int.floor_le (x j)
      have hv := Int.lt_floor_add_one (x j)
      change Int.floor (x i) = Int.floor (x j) at h
      rw [h] at hi hu
      have habs : |x i - x j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact (show 1 ≤ 2 - |x i - x j| by linarith).trans (le_max_left _ _)
    · exact le_max_right _ _
  have he : (∑ i ∈ s, ∑ j ∈ s, e (cell i) (cell j)) ≤
      32 * ∑ a ∈ s.image cell, m a ^ 2 := by
    rw [pair_sum_by_cells]
    apply symmetric_kernel_quadratic_le_row_bound (s.image cell) m e 32
    · exact fun a _ b _ => inverseSquareEnvelope_nonneg (a - b)
    · intro a _ b _
      simp only [e, inverseSquareEnvelope, show b - a = -(a - b) by ring, Int.natAbs_neg]
    · exact fun a _ => inverseSquareEnvelope_row_le _ a
  have hpair : (∑ i ∈ s, ∑ j ∈ s, cauchyWeight (x i - x j)) ≤
      ∑ i ∈ s, ∑ j ∈ s, e (cell i) (cell j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      cauchyWeight_le_cell_envelope (x i) (x j)
  exact hpair.trans (he.trans (mul_le_mul_of_nonneg_left htri (by norm_num)))

private theorem cauchyWeight_le_one (d : ℝ) : cauchyWeight d ≤ 1 := by
  unfold cauchyWeight
  exact (div_le_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg d])

private theorem sincSquared_le_one (R v : ℝ) : sincSquared R v ≤ 1 := by
  unfold sincSquared
  have h := Real.abs_sinc_le_one (R * v / 2)
  have hh := (sq_le_sq₀ (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).2 h
  simpa [sq_abs] using hh

private theorem far_gap_kernel_le {R u x d : ℝ} (hR : 0 < R) (hu : 0 < u)
    (hx : 2 * u < |x|) :
    cauchyWeight d * sincSquared R (Real.pi * x) ≤
      ((1 + 1 / u ^ 2) / R ^ 2) * cauchyWeight x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; linarith
  have hs : sincSquared R (Real.pi * x) ≤ 1 / (R ^ 2 * x ^ 2) := by
    refine (sincSquared_le_inverse_square hR.ne' (mul_ne_zero Real.pi_ne_zero hx0)).trans ?_
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hp : 4 ≤ Real.pi ^ 2 := by
      have hn : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le).2 hn
      norm_num at hs
      exact hs
    have hi := mul_le_mul_of_nonneg_right hp (show 0 ≤ R ^ 2 * x ^ 2 by positivity)
    nlinarith only [hi]
  have hb : 1 / (R ^ 2 * x ^ 2) ≤ ((1 + 1 / u ^ 2) / R ^ 2) * cauchyWeight x := by
    have hxu := (sq_le_sq₀ (show 0 ≤ 2 * u by positivity) (abs_nonneg x)).2 hx.le
    rw [sq_abs] at hxu
    have hc : 1 / x ^ 2 ≤ (1 + 1 / u ^ 2) * cauchyWeight x := by
      unfold cauchyWeight
      apply (div_le_iff₀ (sq_pos_of_ne_zero hx0)).2
      have hiden : (1 + 1 / u ^ 2) * (4 / (4 + x ^ 2)) * x ^ 2 =
          (((u ^ 2 + 1) * 4 * x ^ 2) / u ^ 2) / (4 + x ^ 2) := by
        field_simp [hu.ne']
        <;> ring
      rw [hiden]
      apply (le_div_iff₀ (by positivity)).2
      rw [one_mul]
      apply (le_div_iff₀ (sq_pos_of_pos hu)).2
      nlinarith only [hxu, sq_nonneg (u * x)]
    calc
      _ = (1 / x ^ 2) / R ^ 2 := by rw [div_div, mul_comm (x ^ 2)]
      _ ≤ ((1 + 1 / u ^ 2) * cauchyWeight x) / R ^ 2 :=
        div_le_div_of_nonneg_right hc (sq_nonneg R)
      _ = _ := by ring
  exact (mul_le_of_le_one_left (sincSquared_nonneg _ _) (cauchyWeight_le_one d)).trans
    (hs.trans hb)

/-- A finite bound for the full normalized Fejér remainder. Every nonzero gap
in the unfolded interval of radius `u` is counted, and the far tail is
controlled by the physical short-window moment. -/
theorem fejerFormFactor_le_collision_add_gap_tail {T R B u : ℝ} (hT : 1 < T)
    (hR : 0 < R) (hB : 1 ≤ B) (hu : 0 < u) :
    fejerFormFactor T R ≤ (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) +
      2 * positiveGapMass T u +
      (64 * (1 + 1 / u ^ 2) / R ^ 2) *
        actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) := by
  classical
  let L := Real.log T / (2 * Real.pi)
  let D := T * Real.log T / (2 * Real.pi)
  let t := copyOrdinate T
  let x := fun i : Copies T => 2 * L * t i
  let I := fun i j : Copies T => if 0 < L * (t j - t i) ∧ L * (t j - t i) ≤ u
    then (1 : ℝ) else 0
  let k := (1 + 1 / u ^ 2) / R ^ 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 < D := div_pos (mul_pos (by linarith) (Real.log_pos hT)) (by positivity)
  have hDL : D = T * L := by dsimp [D, L]; ring
  have hphase (i j : Copies T) : Real.log T * (t i - t j) = Real.pi * (x i - x j) := by
    dsimp [x, L]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hpointwise (i j : Copies T) :
      (if t i = t j then 0 else
        cauchyWeight (t i - t j) * sincSquared R (Real.log T * (t i - t j))) ≤
      I i j + I j i + k * cauchyWeight (x i - x j) := by
    have hpos : 0 ≤ k * cauchyWeight (x i - x j) := mul_nonneg hk (cauchyWeight_nonneg _)
    have hI (a b : Copies T) : 0 ≤ I a b := by
      dsimp [I]
      split_ifs <;> norm_num
    have hone : cauchyWeight (t i - t j) * sincSquared R (Real.log T * (t i - t j)) ≤ 1 :=
      (mul_le_of_le_one_left (sincSquared_nonneg _ _) (cauchyWeight_le_one _)).trans
        (sincSquared_le_one _ _)
    by_cases hij : t i = t j
    · simp only [if_pos hij]
      exact add_nonneg (add_nonneg (hI i j) (hI j i)) hpos
    simp only [if_neg hij]
    by_cases hnear : |L * (t j - t i)| ≤ u
    · rcases lt_or_gt_of_ne hij with hlt | hlt
      · have hp := mul_pos hL (sub_pos.mpr hlt)
        have he : I i j = 1 := if_pos ⟨hp, (le_abs_self _).trans hnear⟩
        rw [he]
        exact hone.trans (by linarith only [hI j i, hpos])
      · have hp := mul_pos hL (sub_pos.mpr hlt)
        have he : I j i = 1 := by
          apply if_pos
          refine ⟨hp, ?_⟩
          have hn : L * (t i - t j) = -(L * (t j - t i)) := by ring
          calc
            _ ≤ |L * (t i - t j)| := le_abs_self _
            _ = |L * (t j - t i)| := by rw [hn, abs_neg]
            _ ≤ u := hnear
        rw [he]
        exact hone.trans (by linarith only [hI i j, hpos])
    · rw [hphase]
      have habs : |x i - x j| = 2 * |L * (t j - t i)| := by
        rw [show x i - x j = -(2 * (L * (t j - t i))) by dsimp [x]; ring,
          abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (far_gap_kernel_le hR hu (by rw [habs]; linarith only [lt_of_not_ge hnear])).trans
        (le_add_of_nonneg_left (add_nonneg (hI i j) (hI j i)))
  have htriangle :
      (∑ i : Copies T, ∑ j : Copies T, max (2 - |x i - x j|) 0) ≤
        2 * D * actualPhysicalTriangleEnergy T (B / L) := by
    unfold actualPhysicalTriangleEnergy
    rw [hDL]
    have hT0 : T ≠ 0 := ne_of_gt (by linarith)
    have hc (z : ℝ) : (2 * (T * L)) * (z / T) = (2 * L) * z := by
      field_simp [hT0]
      <;> ring
    rw [hc]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change max (2 - |x i - x j|) 0 ≤
      (2 * L) * max (B / L - |t i - t j|) 0
    have htwo : 0 ≤ 2 * L := by positivity
    rw [mul_max_of_nonneg _ _ htwo, mul_zero,
      show x i - x j = (2 * L) * (t i - t j) by dsimp [x]; ring,
      abs_mul, abs_of_nonneg htwo]
    apply max_le_max_right
    have hb : (2 * L) * (B / L) = 2 * B := by field_simp
    linarith only [hB, hb]
  have hIeq : (∑ i : Copies T, ∑ j : Copies T, I i j) = D * positiveGapMass T u := by
    change _ = D * (_ / D)
    rw [mul_div_cancel₀ _ hD.ne']
    rfl
  have hswap : (∑ i : Copies T, ∑ j : Copies T, I j i) =
      ∑ i : Copies T, ∑ j : Copies T, I i j := Finset.sum_comm
  have hsum : fejerNonzeroGapRemainder T R ≤
      2 * (D * positiveGapMass T u) +
        k * (32 * (2 * D * actualPhysicalTriangleEnergy T (B / L))) := by
    calc
      _ ≤ ∑ i : Copies T, ∑ j : Copies T, (I i j + I j i +
          k * cauchyWeight (x i - x j)) := by
        unfold fejerNonzeroGapRemainder
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpointwise i j
      _ = 2 * (D * positiveGapMass T u) +
            k * ∑ i : Copies T, ∑ j : Copies T, cauchyWeight (x i - x j) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hIeq, hswap, hIeq]
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((cauchy_pair_sum_le_triangle x).trans (mul_le_mul_of_nonneg_left htriangle (by norm_num))) hk)
  have hnorm := normalized_fejer_eq_collision_add_nonzeroGap hT hR
  change D * fejerFormFactor T R = _ at hnorm
  calc
    _ ≤ ((actualCollision T : ℝ) + 2 * (D * positiveGapMass T u) +
        k * (32 * (2 * D * actualPhysicalTriangleEnergy T (B / L)))) / D := by
      apply (le_div_iff₀ hD).2
      linarith only [hnorm, hsum]
    _ = _ := by
      change _ = (actualCollision T : ℝ) / D + 2 * positiveGapMass T u +
        (64 * (1 + 1 / u ^ 2) / R ^ 2) * actualPhysicalTriangleEnergy T (B / L)
      rw [add_div, add_div]
      have hc (A b c : ℝ) : (2 * (D * b)) / D + (A * (32 * (2 * D * c))) / D =
          2 * b + 64 * A * c := by
        field_simp [hD.ne']
        <;> ring
      rw [add_assoc, hc]
      dsimp [k]
      ring

/-- Close-gap control and one bounded short-window moment convert a collision
limit into a uniform large-radius Fourier upper test. -/
theorem eventually_fejer_upper_of_collision_and_near_gap
    (hcollision : Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1))
    (hnear : ∀ η : ℝ, 0 < η → ∃ u : ℝ, 0 < u ∧
      ∀ᶠ T : ℝ in atTop, positiveGapMass T u ≤ η)
    (hm : ∃ B M : ℝ, 1 ≤ B ∧ 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop,
      actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, R₀ ≤ R →
      fejerFormFactor T R ≤ 1 + ε := by
  obtain ⟨B, M, hB, hM, hmoment⟩ := hm
  obtain ⟨u, hu, hgap⟩ := hnear (ε / 8) (by positivity)
  let K := 64 * (1 + 1 / u ^ 2) * M
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let R₀ := max 1 (Real.sqrt (4 * K / ε))
  have hR₀ : 1 ≤ R₀ := le_max_left _ _
  refine ⟨R₀, hR₀, ?_⟩
  filter_upwards [hmoment, hgap, eventually_gt_atTop (1 : ℝ),
    hcollision.eventually_le_const (show 1 < 1 + ε / 4 by linarith)] with
    T hmoment hgap hT hcollision
  intro R hR
  have hR1 := hR₀.trans hR
  have hR0 := zero_lt_one.trans_le hR1
  have hbound : K / R ^ 2 ≤ ε / 4 := by
    have hsq : 4 * K / ε ≤ R ^ 2 := by
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hR0.le).2 ((le_max_right _ _).trans hR)
      rwa [Real.sq_sqrt (by positivity)] at hs
    have hl := (div_le_iff₀ hε).mp hsq
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    linarith only [hl, mul_comm (R ^ 2) ε]
  have hsum := fejerFormFactor_le_collision_add_gap_tail hT hR0 hB hu
  have hwindow :
      (64 * (1 + 1 / u ^ 2) / R ^ 2) *
        actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) ≤ K / R ^ 2 := by
    calc
      _ ≤ (64 * (1 + 1 / u ^ 2) / R ^ 2) * M :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = _ := by dsimp only [K]; ring
  linarith only [hsum, hwindow, hbound, hgap, hcollision, hε]

/-- A radius tending to infinity recovers the normalized collision limit
whenever the near-gap and moment estimates rule out unresolved mass. -/
theorem fejer_tendsto_one_of_collision_and_near_gap
    (hcollision : Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1))
    (hnear : ∀ η : ℝ, 0 < η → ∃ u : ℝ, 0 < u ∧
      ∀ᶠ T : ℝ in atTop, positiveGapMass T u ≤ η)
    (hm : ∃ B M : ℝ, 1 ≤ B ∧ 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop,
      actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) ≤ M)
    {R : ℝ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun T => fejerFormFactor T (R T)) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hcollision.eventually (lt_mem_nhds ha), eventually_gt_atTop (1 : ℝ),
      hR.eventually_gt_atTop 0] with T hcoll hT hR
    exact hcoll.trans_le (collision_div_main_le_fejerFormFactor hT hR)
  · intro b hb
    let ε := (b - 1) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    obtain ⟨R₀, _, hub⟩ := eventually_fejer_upper_of_collision_and_near_gap
      hcollision hnear hm ε hε
    filter_upwards [hub, hR.eventually_ge_atTop R₀] with T hu hT
    exact (hu (R T) hT).trans_lt (by dsimp only [ε]; linarith)

private theorem near_gap_upper_of_positiveGapPCC (hpcc : PositiveGapPCC)
    (η : ℝ) (hη : 0 < η) :
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ T : ℝ in atTop, positiveGapMass T u ≤ η := by
  let u := η / 2
  have hu : 0 < u := by dsimp only [u]; positivity
  have hi : Continuous (fun x : ℝ => 1 - Real.sinc (Real.pi * x) ^ 2) := by fun_prop
  have hmodel : sineGapMass u ≤ u := by
    have h := intervalIntegral.integral_mono_on hu.le (hi.intervalIntegrable 0 u)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 u)
      (fun x _ => sub_le_self _ (sq_nonneg _))
    simpa [sineGapMass] using h
  refine ⟨u, hu, ?_⟩
  filter_upwards [hpcc u u hu le_rfl u hu] with T hT
  have hp := (abs_le.mp (hT u ⟨le_rfl, le_rfl⟩)).2
  dsimp only [u] at hp hmodel
  linarith only [hp, hmodel]

private theorem bounded_window_of_shortWindowSecondMomentUpper
    (hm : ShortWindowSecondMomentUpper) :
    ∃ B M : ℝ, 1 ≤ B ∧ 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop,
      actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) ≤ M := by
  obtain ⟨B, hB, hmoment⟩ := hm 1 zero_lt_one
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨B, B ^ 2 + B, hB, by positivity, ?_⟩
  simpa only [one_mul] using hmoment

/-- Strict positive-gap PCC and the short-window moment give normalized
Fourier Fejér convergence at every radius tending to infinity. -/
theorem fejer_tendsto_one_of_positiveGapPCC (hpcc : PositiveGapPCC)
    (hm : ShortWindowSecondMomentUpper) {R : ℝ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun T => fejerFormFactor T (R T)) atTop (𝓝 1) :=
  fejer_tendsto_one_of_collision_and_near_gap (collision_limit_of_positiveGapPCC hpcc hm)
    (near_gap_upper_of_positiveGapPCC hpcc) (bounded_window_of_shortWindowSecondMomentUpper hm) hR

/-- The physical positive-gap PCC supplies the extended complementary Fourier
upper test at every sufficiently large radius, uniformly once height is large. -/
theorem eventually_outside_extended_upper_of_positiveGapPCC
    (hpcc : PositiveGapPCC) (hm : ShortWindowSecondMomentUpper) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, R₀ ≤ R →
      fejerOutsideExtended T R ≤ 1 - 1 / R + ε := by
  obtain ⟨R₀, hR₀, hupper⟩ := eventually_fejer_upper_of_collision_and_near_gap
    (collision_limit_of_positiveGapPCC hpcc hm) (near_gap_upper_of_positiveGapPCC hpcc)
    (bounded_window_of_shortWindowSecondMomentUpper hm) (ε / 2) (by positivity)
  let R₁ := max R₀ (2 / ε)
  refine ⟨R₁, hR₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [hupper, eventually_extendedShoulderRadius_band] with T hupper hb
  obtain ⟨hT, hzero, hbr, hb1, _, _⟩ := hb
  intro R hR
  have hR₀R : R₀ ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := hR₀.trans hR₀R
  have hRpos := zero_lt_one.trans_le hR1
  have hr0 : 0 ≤ extendedShoulderRadius T := hzero.trans hbr
  have hcore :
      0 ≤ (1 / R) * ∫ α in (-extendedShoulderRadius T)..extendedShoulderRadius T,
        (1 - |α| / R) * formFactor T α := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (by linarith only [hr0])
    intro α hα
    have hαR : |α| ≤ R := (abs_le.mpr hα).trans (hb1.trans hR1)
    exact mul_nonneg (sub_nonneg.mpr ((div_le_iff₀ hRpos).mpr (by simpa using hαR)))
      (formFactor_nonneg hT α)
  have hRlarge : 2 / ε ≤ R := (le_max_right _ _).trans hR
  have hinv : 1 / R ≤ ε / 2 := by
    apply (div_le_iff₀ hRpos).mpr
    have h := (div_le_iff₀ hε).mp hRlarge
    linarith only [h, mul_comm R ε]
  unfold fejerOutsideExtended
  linarith only [hcore, hinv, hupper R hR₀R]

end RiemannResearch.Analysis.MontgomeryFormFactor

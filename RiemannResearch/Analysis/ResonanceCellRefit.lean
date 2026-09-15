/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionSourceImprovement
import RiemannResearch.LinearAlgebra.TwoThreeResonanceCell

/-!
# Actual source gains for a five-column resonance cell

Source: Christian Noack,
`RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md`,
exact refitting and four-charge continuation.

These results connect the finite resonance quadratic form to actual Hilbert
vectors and refit all coefficients in the old subspace. Every covariance
estimate used below is an explicit hypothesis on the screened columns.
No lower bound on the arithmetic source correlations is asserted.
-/

namespace RiemannResearch.Analysis.ResonanceCellRefit

open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Five actual Hilbert columns, in the same order as `CellVector`. -/
structure CellColumns (H : Type*) where
  x0 : H
  x1 : H
  x2 : H
  y0 : H
  y1 : H

/-- The signed linear combination; no mixed term is discarded. -/
def synthesis (u : CellColumns H) (a : CellVector) : H :=
  a.x0 • u.x0 + a.x1 • u.x1 + a.x2 • u.x2 + a.y0 • u.y0 + a.y1 • u.y1

/-- The exact cycle, which can lie in the old subspace without vanishing. -/
def cycle (u : CellColumns H) : H := u.x0 + u.x1 + u.x2 - (u.y0 + u.y1)

variable (P : Submodule ℝ H) [P.HasOrthogonalProjection]

/-- Correlations against the actual residual, rather than a free source vector. -/
def source (b : H) (u : CellColumns H) : CellVector :=
  ⟨inner ℝ (residual P b) u.x0, inner ℝ (residual P b) u.x1,
    inner ℝ (residual P b) u.x2, inner ℝ (residual P b) u.y0,
    inner ℝ (residual P b) u.y1⟩

theorem inner_synthesis (b : H) (u : CellColumns H) (a : CellVector) :
    inner ℝ (residual P b) (synthesis u a) = dot (source P b u) a := by
  simp only [synthesis, inner_add_right, real_inner_smul_right, source, dot]
  ring

/-- Orthogonality to the old cycle is precisely source compatibility. -/
theorem source_compatible (b : H) (u : CellColumns H) (hu : cycle u ∈ P) :
    Compatible (source P b u) := by
  have hc := Submodule.starProjection_inner_eq_zero b (cycle u) hu
  simp only [cycle, inner_sub_right, inner_add_right] at hc
  unfold Compatible binarySum ternarySum source
    RiemannResearch.Analysis.ProjectionSourceImprovement.residual
  dsimp
  linarith

/-- Exact signed gain for every coefficient vector and every scalar. -/
theorem cell_refit_gain_exact (b : H) (u : CellColumns H) (a : CellVector) (t : ℝ) :
    ‖residual P b‖^2 -
      ‖b - (P.starProjection b + t • residual P (synthesis u a))‖^2 =
    2*t*dot (source P b u) a - t^2*‖residual P (synthesis u a)‖^2 := by
  rw [refit_gain_exact, inner_synthesis]

/-- A compatible-source trial produces a quantitative gain from a Gram upper bound. -/
theorem sourceSize_refit_lower (b : H) (u : CellColumns H)
    (hh : Compatible (source P b u)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis u a)‖^2 ≤ C * sizeSq a) :
    sizeSq (source P b u) / C ≤
      ‖residual P b‖^2 - ‖b - (P.starProjection b +
        (1/C) • residual P (synthesis u (source P b u)))‖^2 := by
  rw [cell_refit_gain_exact]
  have hid : dot (source P b u) (source P b u) = sizeSq (source P b u) := by
    simp only [dot, sizeSq, pow_two]
  rw [hid]
  have hn := hbound (source P b u) hh
  have hmul := mul_le_mul_of_nonneg_left hn (sq_nonneg (1/C))
  have he : 2*(1/C)*sizeSq (source P b u) -
      (1/C)^2*(C*sizeSq (source P b u)) = sizeSq (source P b u)/C := by
    field_simp [ne_of_gt hC]
    ring
  nlinarith

/-- The four-charge optimizer supplies its stronger bound from the leading energy. -/
theorem sourceEnergy_refit_lower (b : H) (u : CellColumns H)
    (hh : Compatible (source P b u)) {L : ℝ} (hL : 0 < L)
    (hbound : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis u a)‖^2 ≤ L * energy a) :
    sourceEnergy (source P b u) / L ≤
      ‖residual P b‖^2 - ‖b - (P.starProjection b +
        (1/L) • residual P (synthesis u (optimizer (source P b u))))‖^2 := by
  rw [cell_refit_gain_exact]
  have hn := hbound (optimizer (source P b u)) (optimizer_compatible _)
  have hmul := mul_le_mul_of_nonneg_left hn (sq_nonneg (1/L))
  have he : 2*(1/L)*dot (source P b u) (optimizer (source P b u)) -
      (1/L)^2*(L*energy (optimizer (source P b u))) =
      sourceEnergy (source P b u)/L := by
    rw [← optimizer_attains (source P b u) hh]
    field_simp [ne_of_gt hL]
  nlinarith

variable (W : Submodule ℝ H) [W.HasOrthogonalProjection]

/-- Exact membership conditions for the five columns of a legal enlarged space. -/
def ColumnsIn (u : CellColumns H) : Prop :=
  u.x0 ∈ W ∧ u.x1 ∈ W ∧ u.x2 ∈ W ∧ u.y0 ∈ W ∧ u.y1 ∈ W

omit [W.HasOrthogonalProjection] in
theorem synthesis_mem (u : CellColumns H) (hu : ColumnsIn W u) (a : CellVector) :
    synthesis u a ∈ W := by
  rcases hu with ⟨h0, h1, h2, h3, h4⟩
  exact W.add_mem (W.add_mem (W.add_mem (W.add_mem
    (W.smul_mem a.x0 h0) (W.smul_mem a.x1 h1))
      (W.smul_mem a.x2 h2)) (W.smul_mem a.y0 h3)) (W.smul_mem a.y1 h4)

private theorem projection_error_le (b y : H) (hy : y ∈ W) :
    ‖residual W b‖^2 ≤ ‖b-y‖^2 := by
  have he := refit_pythagoras W b y 0 hy
  have hz : residual W (0 : H) = 0 := by
    simp [RiemannResearch.Analysis.ProjectionSourceImprovement.residual]
  simp only [add_zero, hz, sub_zero, map_zero] at he
  nlinarith [sq_nonneg ‖W.starProjection b-y‖]

/-- A trial is dominated by the true improvement after complete old/new refitting. -/
theorem enlarged_gain_ge_trial (hPW : P ≤ W) (b : H) (u : CellColumns H)
    (hu : ColumnsIn W u) (a : CellVector) (t : ℝ) :
    ‖residual P b‖^2 -
      ‖b - (P.starProjection b + t • residual P (synthesis u a))‖^2 ≤
    ‖residual P b‖^2 - ‖residual W b‖^2 := by
  have hy := refit_mem P W hPW b (synthesis u a) (synthesis_mem W u hu a) t
  have he := projection_error_le W b _ hy
  linarith

/-- The five-column source bound applies to the exact enlarged projection gain. -/
theorem enlarged_gain_lower (hPW : P ≤ W) (b : H) (u : CellColumns H)
    (hu : ColumnsIn W u) (hh : Compatible (source P b u))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis u a)‖^2 ≤ C * sizeSq a) :
    sizeSq (source P b u)/C ≤ ‖residual P b‖^2 - ‖residual W b‖^2 :=
  (sourceSize_refit_lower P b u hh hC hbound).trans
    (enlarged_gain_ge_trial P W hPW b u hu (source P b u) (1/C))

/-- The four-charge bound also controls the exact enlarged projection gain. -/
theorem enlarged_gain_four_charges (hPW : P ≤ W) (b : H) (u : CellColumns H)
    (hu : ColumnsIn W u) (hh : Compatible (source P b u))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis u a)‖^2 ≤ L * energy a) :
    sourceEnergy (source P b u)/L ≤ ‖residual P b‖^2 - ‖residual W b‖^2 :=
  (sourceEnergy_refit_lower P b u hh hL hbound).trans
    (enlarged_gain_ge_trial P W hPW b u hu (optimizer (source P b u)) (1/L))

/-- A leading covariance form plus a bounded error gives the coefficient `7/3`. -/
theorem enlarged_gain_lower_of_leading_bound (hPW : P ≤ W) (b : H)
    (u : CellColumns H) (hu : ColumnsIn W u) (hh : Compatible (source P b u))
    {L K : ℝ} (hL : 0 ≤ L) (hC : 0 < (7:ℝ)/3*L+K)
    (hbound : ∀ a : CellVector, Compatible a →
      ‖residual P (synthesis u a)‖^2 ≤ L*energy a + K*sizeSq a) :
    sizeSq (source P b u) / ((7:ℝ)/3*L+K) ≤
      ‖residual P b‖^2 - ‖residual W b‖^2 := by
  apply enlarged_gain_lower P W hPW b u hu hh hC
  intro a ha
  calc
    ‖residual P (synthesis u a)‖^2 ≤ L*energy a+K*sizeSq a := hbound a ha
    _ ≤ L*((7:ℝ)/3*sizeSq a)+K*sizeSq a :=
      add_le_add (mul_le_mul_of_nonneg_left (energy_le a) hL) le_rfl
    _ = ((7:ℝ)/3*L+K)*sizeSq a := by ring

/-- The raw five-column trace, with every original column included. -/
def trace (u : CellColumns H) : ℝ :=
  ‖u.x0‖^2 + ‖u.x1‖^2 + ‖u.x2‖^2 + ‖u.y0‖^2 + ‖u.y1‖^2

omit [InnerProductSpace ℝ H] in
theorem trace_nonneg (u : CellColumns H) : 0 ≤ trace u := by
  unfold trace
  positivity

/-- Hilbert-space Lagrange identity: all ten mixed interactions are retained. -/
theorem trace_lagrange (u : CellColumns H) (a : CellVector) :
    trace u * sizeSq a - ‖synthesis u a‖^2 =
      ‖a.x0 • u.x1-a.x1 • u.x0‖^2 +
      ‖a.x0 • u.x2-a.x2 • u.x0‖^2 +
      ‖a.x0 • u.y0-a.y0 • u.x0‖^2 +
      ‖a.x0 • u.y1-a.y1 • u.x0‖^2 +
      ‖a.x1 • u.x2-a.x2 • u.x1‖^2 +
      ‖a.x1 • u.y0-a.y0 • u.x1‖^2 +
      ‖a.x1 • u.y1-a.y1 • u.x1‖^2 +
      ‖a.x2 • u.y0-a.y0 • u.x2‖^2 +
      ‖a.x2 • u.y1-a.y1 • u.x2‖^2 +
      ‖a.y0 • u.y1-a.y1 • u.y0‖^2 := by
  unfold trace sizeSq synthesis
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u.x1 u.x0, real_inner_comm u.x2 u.x0,
    real_inner_comm u.y0 u.x0, real_inner_comm u.y1 u.x0,
    real_inner_comm u.x2 u.x1, real_inner_comm u.y0 u.x1,
    real_inner_comm u.y1 u.x1, real_inner_comm u.y0 u.x2,
    real_inner_comm u.y1 u.x2, real_inner_comm u.y1 u.y0]
  ring

/-- Finite Cauchy--Schwarz for the actual Hilbert columns. -/
theorem synthesis_norm_sq_le_trace (u : CellColumns H) (a : CellVector) :
    ‖synthesis u a‖^2 ≤ trace u * sizeSq a := by
  have hp : 0 ≤ trace u * sizeSq a - ‖synthesis u a‖^2 := by
    rw [trace_lagrange]
    positivity
  linarith

/-- Screening against every old column can only improve the trace bound. -/
theorem screened_synthesis_norm_sq_le_trace (u : CellColumns H) (a : CellVector) :
    ‖residual P (synthesis u a)‖^2 ≤ trace u * sizeSq a := by
  have he := RiemannResearch.Analysis.ProjectionCompression.projection_pythagoras P
    (synthesis u a)
  change ‖synthesis u a‖^2 = ‖P.starProjection (synthesis u a)‖^2 +
    ‖residual P (synthesis u a)‖^2 at he
  have hc : ‖residual P (synthesis u a)‖^2 ≤ ‖synthesis u a‖^2 := by
    nlinarith [sq_nonneg ‖P.starProjection (synthesis u a)‖]
  exact hc.trans (synthesis_norm_sq_le_trace u a)

/-- Unconditional trace gain for any five actual columns, including zero trace.
This bound requires neither a covariance provider nor source compatibility. -/
theorem enlarged_gain_trace (hPW : P ≤ W) (b : H) (u : CellColumns H)
    (hu : ColumnsIn W u) :
    sizeSq (source P b u) / trace u ≤
      ‖residual P b‖^2 - ‖residual W b‖^2 := by
  by_cases ht : 0 < trace u
  · have hn := screened_synthesis_norm_sq_le_trace P u (source P b u)
    have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg (1/trace u))
    have hid : dot (source P b u) (source P b u) = sizeSq (source P b u) := by
      simp only [dot, sizeSq, pow_two]
    have he : 2*(1/trace u)*sizeSq (source P b u) -
        (1/trace u)^2*(trace u*sizeSq (source P b u)) =
        sizeSq (source P b u)/trace u := by
      field_simp [ne_of_gt ht]
      ring
    have htrial : sizeSq (source P b u)/trace u ≤
        ‖residual P b‖^2 - ‖b - (P.starProjection b +
          (1/trace u) • residual P (synthesis u (source P b u)))‖^2 := by
      rw [cell_refit_gain_exact, hid]
      nlinarith
    exact htrial.trans
      (enlarged_gain_ge_trial P W hPW b u hu (source P b u) (1/trace u))
  · have hz : trace u = 0 := le_antisymm (le_of_not_gt ht) (trace_nonneg u)
    rw [hz, div_zero]
    have he := enlarged_gain_ge_trial P W hPW b u hu (source P b u) 0
    simpa only [zero_smul, add_zero,
      RiemannResearch.Analysis.ProjectionSourceImprovement.residual, sub_self] using he

end
end RiemannResearch.Analysis.ResonanceCellRefit

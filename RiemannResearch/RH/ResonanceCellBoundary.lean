/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.TwoThreePacketRelations
import RiemannResearch.RH.AdjacentPacketNormBounds
import RiemannResearch.Analysis.ProjectionSourceImprovement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import RiemannResearch.LinearAlgebra.ResonanceCellPotentials

/-!
# Actual Pareto potentials and the short resonance boundary anchor

Source: user - provided global approximation / resonance - blind - pattern handoff,
16 September 2026, Sections 5 and 8. This specializes the finite reconstruction
to the actual residue - difference Hilbert vectors and projection residual.
The commuting relation is discharged by the proved arithmetic generator
cocycle; old anchoring is discharged by projection orthogonality.
No RH assumption, density assumption, or residual - source minorant is used.
-/

namespace RiemannResearch.RH.Pareto.ResonanceCellBoundary

noncomputable section

open RiemannResearch.LinearAlgebra

/-- The actual generator potential, extended by zero at conductor zero. -/
def potential (r : ThresholdHilbert) (p : ℕ) (hp : 0 < p) (m : ℕ) : ℝ :=
  if hm : 0 < m then inner ℝ r (AdjacentPacket.generator p m hp hm) else 0

theorem potential_packet (r : ThresholdHilbert) (p : ℕ) (hp : 0 < p)
    (m : ℕ) (hm : 0 < m) :
    ResonanceCellPotentials.packet (potential r p hp) m =
      inner ℝ r (AdjacentPacket.packet p m hp hm) := by
  have hm1 : 0 < m + 1 := by omega
  simp only [ResonanceCellPotentials.packet, potential, dif_pos hm, dif_pos hm1,
    AdjacentPacket.packet,
    inner_sub_right]

/-- The abstract five sources are exactly the genuine arithmetic packet correlations. -/
theorem potential_sources (r : ThresholdHilbert) (k : ℕ) (hk : 0 < k) :
    ResonanceCellPotentials.sources (potential r 2 (by omega)) (potential r 3 (by omega)) k =
      AdjacentPacket.cellSource r k hk := by
  simp only [ResonanceCellPotentials.sources, AdjacentPacket.cellSource,
    potential_packet r 2 (by omega) (3 * k) (by omega),
    potential_packet r 2 (by omega) (3 * k + 1) (by omega),
    potential_packet r 2 (by omega) (3 * k + 2) (by omega),
    potential_packet r 3 (by omega) (2 * k) (by omega),
    potential_packet r 3 (by omega) (2 * k + 1) (by omega)]

/-- Provider: the exact commuting - square potential law follows from actual generators. -/
theorem potential_commuting (r : ThresholdHilbert) :
    ResonanceCellPotentials.Commuting (potential r 2 (by omega)) (potential r 3 (by omega)) := by
  intro k
  by_cases hk : 0 < k
  · have hk2 : 0 < 2 * k := by omega
    have hk3 : 0 < 3 * k := by omega
    have h := congrArg (fun f : ThresholdHilbert => inner ℝ r f)
      (AdjacentPacket.generator_cocycle 2 3 k (by omega) (by omega) hk)
    simp only [inner_sub_right] at h
    simp only [potential, dif_pos hk, dif_pos hk2, dif_pos hk3]
    linarith
  · have hk0 : k = 0 := by omega
    subst k
    simp [potential]

/-- Exact old - budget membership, retaining both seeds at every positive dilation. -/
def OldColumnsIn (P : Submodule ℝ ThresholdHilbert) (M : ℕ) : Prop :=
  ∀ m, (hm : 0 < m) → m ≤ M →
    AdjacentPacket.generator 2 m (by omega) hm ∈ P ∧ AdjacentPacket.generator 3 m (by omega) hm ∈ P

/-- Provider: old potentials vanish for the actual constant - target projection residual. -/
theorem projection_old_anchored (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (M : ℕ) (hP : OldColumnsIn P M) :
    ResonanceCellPotentials.OldAnchored M
      (potential (hilbertOne - P.starProjection hilbertOne) 2 (by omega))
      (potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega)) := by
  intro m hmM
  by_cases hm : 0 < m
  · obtain ⟨h2, h3⟩ := hP m hm hmM
    simp only [potential, dif_pos hm]
    exact ⟨Submodule.starProjection_inner_eq_zero _ _ h2,
      Submodule.starProjection_inner_eq_zero _ _ h3⟩
  · simp [potential, hm]

/-- Actual - residual simultaneous nullspace theorem, with the old and arithmetic
providers discharged. The only input is membership of the old legal generators. -/
theorem projection_invisible_iff_constant (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (M : ℕ) (hP : OldColumnsIn P M) :
    let r := hilbertOne - P.starProjection hilbertOne
    let B := potential r 2 (by omega)
    let T := potential r 3 (by omega)
    (∀ k, ResonanceCellPotentials.Selected M k → ResonanceCellPotentials.Invisible B T k) ↔
    ((∀ j, j ≤ ResonanceCellPotentials.cellCount M →
      T (2 * (ResonanceCellPotentials.cellStart M + j)) =
        T (2 * ResonanceCellPotentials.cellStart M)) ∧
      ∀ i, i < ResonanceCellPotentials.cellCount M →
        B (3 * (ResonanceCellPotentials.cellStart M + i) + 1) =
          T (2 * ResonanceCellPotentials.cellStart M) ∧
        B (3 * (ResonanceCellPotentials.cellStart M + i) + 2) =
          T (2 * ResonanceCellPotentials.cellStart M) ∧
        T (2 * (ResonanceCellPotentials.cellStart M + i) + 1) =
          T (2 * ResonanceCellPotentials.cellStart M)) :=
  ResonanceCellPotentials.selected_invisible_iff_constant (projection_old_anchored P M hP)
    (potential_commuting _)

/-- One boundary packet detects the common potential at odd budgets. -/
theorem projection_boundary_odd (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (M : ℕ) (hm : 0 < M) (hodd : M % 2 = 1)
    (hP : AdjacentPacket.generator 3 M (by omega) hm ∈ P) :
    potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega)
      (2 * (M / 2 + 1)) =
    inner ℝ (hilbertOne - P.starProjection hilbertOne)
      (AdjacentPacket.packet 3 M (by omega) hm) := by
  have ha : potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega) M = 0 := by
    simp only [potential, dif_pos hm]
    exact Submodule.starProjection_inner_eq_zero _ _ hP
  rw [ResonanceCellPotentials.boundary_anchor_odd _ hodd ha, potential_packet]

/-- Two boundary packets detect the common potential at even budgets. -/
theorem projection_boundary_even (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (M : ℕ) (hm : 0 < M) (heven : M % 2 = 0)
    (hP : AdjacentPacket.generator 3 M (by omega) hm ∈ P) :
    potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega)
      (2 * (M / 2 + 1)) =
    inner ℝ (hilbertOne - P.starProjection hilbertOne) (AdjacentPacket.packet 3 M (by omega) hm) +
    inner ℝ (hilbertOne - P.starProjection hilbertOne)
      (AdjacentPacket.packet 3 (M + 1) (by omega) (by omega)) := by
  have ha : potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega) M = 0 := by
    simp only [potential, dif_pos hm]
    exact Submodule.starProjection_inner_eq_zero _ _ hP
  rw [ResonanceCellPotentials.boundary_anchor_even _ heven ha, potential_packet, potential_packet]


open AdjacentPacket AdjacentDigit
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ProjectionCompression

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem projection_error_le (W : Submodule ℝ H)
    [W.HasOrthogonalProjection] (b y : H) (hy : y ∈ W) :
    ‖residual W b‖ ^ 2 ≤ ‖b - y‖ ^ 2 := by
  have he := refit_pythagoras W b y 0 hy
  have hz : residual W (0 : H) = 0 := by
    simp [RiemannResearch.Analysis.ProjectionSourceImprovement.residual]
  simp only [add_zero, hz, sub_zero, map_zero] at he
  nlinarith [sq_nonneg ‖W.starProjection b - y‖]

/-- A raw legal correction with energy at most C gives its actual source gain. -/
private theorem source_sq_div_bound_le_gain
    (P W : Submodule ℝ H) [P.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (hPW : P ≤ W)
    (b z : H) (hz : z ∈ W) {C : ℝ} (hC : 0 < C)
    (hbound : ‖z‖ ^ 2 ≤ C) :
    (inner ℝ (residual P b) z) ^ 2 / C ≤
      ‖residual P b‖ ^ 2 - ‖residual W b‖ ^ 2 := by
  let c := inner ℝ (residual P b) z
  have hp := projection_pythagoras P z
  have hscreen : ‖residual P z‖ ^ 2 ≤ C := by
    change ‖z‖ ^ 2 = ‖P.starProjection z‖ ^ 2 + ‖residual P z‖ ^ 2 at hp
    nlinarith [sq_nonneg ‖P.starProjection z‖]
  have hmul := mul_le_mul_of_nonneg_left hscreen (sq_nonneg (c / C))
  have hgain := refit_gain_exact P b z (c / C)
  have hy := refit_mem P W hPW b z hz (c / C)
  have hminimum := projection_error_le W b _ hy
  have he : 2 * (c / C) * c - (c / C) ^ 2 * C = c ^ 2 / C := by
    field_simp [ne_of_gt hC]
    ring
  change c ^ 2 / C ≤ _
  change ‖residual P b‖ ^ 2 -
    ‖b - (P.starProjection b + (c / C) • residual P z)‖ ^ 2 =
      2 * (c / C) * c - (c / C) ^ 2*‖residual P z‖ ^ 2 at hgain
  nlinarith

omit [InnerProductSpace ℝ H] in
private theorem norm_add_sq_le_twice (x y : H) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2+‖y‖ ^ 2) := by
  have hn := norm_add_le x y
  nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y,
    sq_nonneg (‖x‖-‖y‖)]

end Abstract

/-- The first shared ternary vertex of the selected genuinely new cells. -/
def boundaryRoot (M : ℕ) : ℕ := 2 * (M / 2 + 1)

theorem boundaryRoot_cases (M : ℕ) :
    boundaryRoot M = M + 1 ∨ boundaryRoot M = M + 2 := by
  unfold boundaryRoot
  omega

theorem boundaryRoot_pos (M : ℕ) : 0 < boundaryRoot M := by
  unfold boundaryRoot
  omega

theorem boundaryRoot_le_double (M : ℕ) (hM : 0 < M) :
    boundaryRoot M ≤ 2 * M := by
  unfold boundaryRoot
  omega

/-- One old - boundary packet in the odd case, two in the even case. -/
theorem boundary_correction_cases (M : ℕ) (hM : 0 < M) :
    generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) -
      generator 3 M (by omega) hM = packet 3 M (by omega) hM ∨
    generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) -
      generator 3 M (by omega) hM =
        packet 3 M (by omega) hM + packet 3 (M + 1) (by omega) (by omega) := by
  rcases boundaryRoot_cases M with h | h
  · left
    simp only [h, packet]
  · right
    simp only [h, packet]
    abel

/-- Explicit logarithmic energy budget for anchoring the root generator. -/
def boundaryEnergyBudget (M : ℕ) : ℝ :=
  8 * Real.log ((M + 1:ℕ):ℝ) +
    8*‖digitHilbert 3 1 (by omega) (by omega)‖ ^ 2 + 996

theorem boundaryEnergyBudget_pos (M : ℕ) : 0 < boundaryEnergyBudget M := by
  have hl : 0 ≤ Real.log ((M + 1:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M))
  unfold boundaryEnergyBudget
  nlinarith [sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]

/-- Complete infinite packet norms imply a logarithmic bound for the anchor. -/
theorem boundary_correction_norm_sq_le (M : ℕ) (hM : 0 < M) :
    ‖generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) -
      generator 3 M (by omega) hM‖ ^ 2 ≤ boundaryEnergyBudget M := by
  have h0 := (abs_le.mp (ternary_packet_log_bound M hM)).2
  have h1 := (abs_le.mp (ternary_packet_log_bound (M + 1) (by omega))).2
  have hlog : Real.log (M:ℝ) ≤ Real.log ((M + 1:ℕ):ℝ) :=
    Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast Nat.le_succ M)
  have hl : 0 ≤ Real.log ((M + 1:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M))
  rcases boundary_correction_cases M hM with h | h
  · rw [h]
    unfold boundaryEnergyBudget
    nlinarith [sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]
  · rw [h]
    have hs := norm_add_sq_le_twice (packet 3 M (by omega) hM)
      (packet 3 (M + 1) (by omega) (by omega))
    unfold boundaryEnergyBudget
    nlinarith

/-- The boundary anchor controls an actual source after arbitrary old refitting.

In the intended application, P=V_M, W=V_(2M), and b=hilbertOne. No
conditional arithmetic source estimate is used.
-/
theorem actual_boundary_source_gain
    (P W : Submodule ℝ ThresholdHilbert) [P.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (hPW : P ≤ W)
    (b : ThresholdHilbert) (M : ℕ) (hM : 0 < M)
    (hold : generator 3 M (by omega) hM ∈ P)
    (hnew : generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) ∈ W) :
    (inner ℝ (residual P b)
      (generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M))) ^ 2 /
      boundaryEnergyBudget M ≤
        ‖residual P b‖ ^ 2 - ‖residual W b‖ ^ 2 := by
  have hz := W.sub_mem hnew (hPW hold)
  have hzero : inner ℝ (residual P b) (generator 3 M (by omega) hM) = 0 := by
    exact Submodule.starProjection_inner_eq_zero b _ hold
  have hc : inner ℝ (residual P b)
      (generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) -
        generator 3 M (by omega) hM) =
      inner ℝ (residual P b)
        (generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M)) := by
    rw [inner_sub_right, hzero, sub_zero]
  have hg := source_sq_div_bound_le_gain P W hPW b _ hz
    (boundaryEnergyBudget_pos M) (boundary_correction_norm_sq_le M hM)
  rwa [hc] at hg


/-- The common resonance potential has a logarithmic actual - gain budget.
This does not require the cell sources to vanish. -/
theorem projection_common_source_gain
    (P W : Submodule ℝ ThresholdHilbert) [P.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (hPW : P ≤ W)
    (M : ℕ) (hM : 0 < M)
    (hold : generator 3 M (by omega) hM ∈ P)
    (hnew : generator 3 (boundaryRoot M) (by omega) (boundaryRoot_pos M) ∈ W) :
    (potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega)
      (boundaryRoot M)) ^ 2 ≤ boundaryEnergyBudget M *
        (‖residual P hilbertOne‖ ^ 2 - ‖residual W hilbertOne‖ ^ 2) := by
  have h := actual_boundary_source_gain P W hPW hilbertOne M hM hold hnew
  have hm := (div_le_iff₀ (boundaryEnergyBudget_pos M)).mp h
  simpa only [potential, dif_pos (boundaryRoot_pos M),
    RiemannResearch.Analysis.ProjectionSourceImprovement.residual, mul_comm] using hm

/-- Ordinary old/new two-seed budgets supply every membership input to the
actual common-mode bound. Both seeds retain all positive integer dilations. -/
theorem projection_common_source_gain_of_budgets
    (P W : Submodule ℝ ThresholdHilbert) [P.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (hPW : P ≤ W)
    (M : ℕ) (hM : 0 < M)
    (hP : OldColumnsIn P M) (hW : OldColumnsIn W (2 * M)) :
    (potential (hilbertOne - P.starProjection hilbertOne) 3 (by omega)
      (boundaryRoot M)) ^ 2 ≤ boundaryEnergyBudget M *
        (‖residual P hilbertOne‖ ^ 2 - ‖residual W hilbertOne‖ ^ 2) :=
  projection_common_source_gain P W hPW M hM (hP M hM le_rfl).2
    (hW (boundaryRoot M) (boundaryRoot_pos M) (boundaryRoot_le_double M hM)).2

end
end RiemannResearch.RH.Pareto.ResonanceCellBoundary

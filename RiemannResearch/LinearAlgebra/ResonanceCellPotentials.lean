/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Resonance - cell potentials and their boundary anchor

Source: user - provided argument,
`RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026 - 09 - 16.md`,
Sections 5 and 8. The chain reconstruction and short boundary anchor are
developed from its exact commuting - square and old - space boundary identities.

`B` and `T` are binary and ternary correlation potentials. This module proves
finite arithmetic identities and a complete potential - level classification
on the covered component. It does not assert a residual - energy lower bound,
Hilbert - space density, or RH. Applying it to actual residuals requires the
old - space normal equations and the commuting - square identity.

-/

namespace RiemannResearch.LinearAlgebra.ResonanceCellPotentials

open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
open scoped BigOperators

/-- Exact adjacent source, with the boundary retained. -/
def packet (f : ℕ → ℝ) (m : ℕ) : ℝ := f (m + 1) - f m

/-- Five sources in the order used by the existing resonance - cell quadratic form. -/
def sources (B T : ℕ → ℝ) (k : ℕ) : CellVector :=
  ⟨packet B (3 * k), packet B (3 * k + 1), packet B (3 * k + 2),
    packet T (2 * k), packet T (2 * k + 1)⟩

/-- The selected genuinely new resonance cells. -/
def Selected (M k : ℕ) : Prop := M < 2 * k ∧ 3 * k + 3 ≤ 2 * M

def cellStart (M : ℕ) : ℕ := M / 2 + 1

def cellCount (M : ℕ) : ℕ := 2 * M / 3 - cellStart M

/-- Exact selected - cell interval, including empty small - budget cases. -/
theorem selected_iff_offset (M k : ℕ) :
    Selected M k ↔ ∃ i, i < cellCount M ∧ k = cellStart M + i := by
  unfold Selected cellCount cellStart
  constructor
  · intro hk
    exact ⟨k - (M / 2 + 1), by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega

/-- Potentials vanish on old columns, as the actual residual's normal equations require. -/
def OldAnchored (M : ℕ) (B T : ℕ → ℝ) : Prop :=
  ∀ m, m ≤ M → B m = 0 ∧ T m = 0

/-- Exact arithmetic relation; this is an explicit input, not an RH hypothesis. -/
def Commuting (B T : ℕ → ℝ) : Prop :=
  ∀ k, B (3 * k) = T (2 * k) + B k - T k

/-- The four canonical potential equalities in one cell. -/
def Flat (B T : ℕ → ℝ) (k : ℕ) : Prop :=
  B (3 * k + 1) = T (2 * k) ∧ B (3 * k + 2) = T (2 * k) ∧
    T (2 * k + 1) = T (2 * k) ∧ T (2 * k + 2) = T (2 * k)

/-- All five observed packet sources vanish. -/
def Invisible (B T : ℕ → ℝ) (k : ℕ) : Prop :=
  (sources B T k).x0 = 0 ∧ (sources B T k).x1 = 0 ∧
    (sources B T k).x2 = 0 ∧ (sources B T k).y0 = 0 ∧
    (sources B T k).y1 = 0

theorem selected_old_indices {M k : ℕ} (hk : Selected M k) :
    k ≤ M ∧ k + 1 ≤ M := by
  unfold Selected at hk
  omega

theorem selected_endpoints {M k : ℕ} {B T : ℕ → ℝ}
    (hk : Selected M k) (ha : OldAnchored M B T) (hc : Commuting B T) :
    B (3 * k) = T (2 * k) ∧ B (3 * k + 3) = T (2 * k + 2) := by
  obtain ⟨hk0, hk1⟩ := selected_old_indices hk
  have h0 := hc k
  have h1 := hc (k + 1)
  obtain ⟨hb0, ht0⟩ := ha k hk0
  obtain ⟨hb1, ht1⟩ := ha (k + 1) hk1
  rw [hb0, ht0] at h0
  rw [hb1, ht1] at h1
  have e3 : 3 * (k + 1) = 3 * k + 3 := by omega
  have e2 : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [e3, e2] at h1
  constructor <;> linarith

theorem source_compatible_of_endpoints {B T : ℕ → ℝ} {k : ℕ}
    (h0 : B (3 * k) = T (2 * k)) (h2 : B (3 * k + 3) = T (2 * k + 2)) :
    Compatible (sources B T k) := by
  unfold Compatible binarySum ternarySum sources packet
  dsimp
  have e1 : 3 * k + 1 + 1 = 3 * k + 2 := by omega
  have e2 : 3 * k + 2 + 1 = 3 * k + 3 := by omega
  have e3 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
  rw [e1, e2, e3]
  linarith

theorem selected_source_compatible {M k : ℕ} {B T : ℕ → ℝ}
    (hk : Selected M k) (ha : OldAnchored M B T) (hc : Commuting B T) :
    Compatible (sources B T k) := by
  obtain ⟨h0, h2⟩ := selected_endpoints hk ha hc
  exact source_compatible_of_endpoints h0 h2

theorem invisible_iff_flat_of_endpoints {B T : ℕ → ℝ} {k : ℕ}
    (h0 : B (3 * k) = T (2 * k)) (h2 : B (3 * k + 3) = T (2 * k + 2)) :
    Invisible B T k ↔ Flat B T k := by
  unfold Invisible sources packet Flat
  dsimp
  have e1 : 3 * k + 1 + 1 = 3 * k + 2 := by omega
  have e2 : 3 * k + 2 + 1 = 3 * k + 3 := by omega
  have e3 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
  rw [e1, e2, e3]
  constructor
  · rintro ⟨ha, hb, _, hd, he⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨ha, hb, hd, he⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem selected_invisible_iff_flat {M k : ℕ} {B T : ℕ → ℝ}
    (hk : Selected M k) (ha : OldAnchored M B T) (hc : Commuting B T) :
    Invisible B T k ↔ Flat B T k := by
  obtain ⟨h0, h2⟩ := selected_endpoints hk ha hc
  exact invisible_iff_flat_of_endpoints h0 h2

/-- Exact reconstruction along the chain; all signed ternary sources are retained. -/
theorem ternary_chain_reconstruction (T : ℕ → ℝ) (L j : ℕ) :
    T (2 * (L + j)) = T (2 * L) +
      ∑ i ∈ Finset.range j, (packet T (2 * (L + i)) + packet T (2 * (L + i) + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    unfold packet at *
    have e : 2 * (L + (j + 1)) = 2 * (L + j) + 1 + 1 := by omega
    rw [e]
    linarith

/-- Contiguous invisible cells have exactly one common potential on their covered vertices. -/
theorem flat_chain_even {B T : ℕ → ℝ} {L c : ℕ}
    (hf : ∀ i, i < c → Flat B T (L + i)) :
    ∀ j, j ≤ c → T (2 * (L + j)) = T (2 * L) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hf0 := (hf j (by omega)).2.2.2
    have hi := ih (by omega)
    have e : 2 * (L + j) + 2 = 2 * (L + (j + 1)) := by omega
    rw [e] at hf0
    exact hf0.trans hi

theorem flat_chain_vertices {B T : ℕ → ℝ} {L c : ℕ}
    (hf : ∀ i, i < c → Flat B T (L + i)) {i : ℕ} (hi : i < c) :
    B (3 * (L + i) + 1) = T (2 * L) ∧ B (3 * (L + i) + 2) = T (2 * L) ∧
      T (2 * (L + i) + 1) = T (2 * L) := by
  have he := flat_chain_even hf i (by omega)
  obtain ⟨h0, h1, h2, _⟩ := hf i hi
  exact ⟨h0.trans he, h1.trans he, h2.trans he⟩

/-- Necessary and sufficient classification, including the shared terminal vertex. -/
theorem flat_chain_iff_constant {B T : ℕ → ℝ} {L c : ℕ} :
    (∀ i, i < c → Flat B T (L + i)) ↔
    ((∀ j, j ≤ c → T (2 * (L + j)) = T (2 * L)) ∧
      ∀ i, i < c → B (3 * (L + i) + 1) = T (2 * L) ∧
        B (3 * (L + i) + 2) = T (2 * L) ∧ T (2 * (L + i) + 1) = T (2 * L)) := by
  constructor
  · intro hf
    exact ⟨flat_chain_even hf, fun i hi => flat_chain_vertices hf hi⟩
  · rintro ⟨he, hv⟩ i hi
    obtain ⟨h0, h1, h2⟩ := hv i hi
    have hbase := he i (by omega)
    have hend := he (i + 1) (by omega)
    have e : 2 * (L + (i + 1)) = 2 * (L + i) + 2 := by omega
    rw [e] at hend
    exact ⟨h0.trans hbase.symm, h1.trans hbase.symm,
      h2.trans hbase.symm, hend.trans hbase.symm⟩

/-- Adding the root anchor kills the entire covered invisible component. -/
theorem anchored_flat_chain_zero {B T : ℕ → ℝ} {L c : ℕ}
    (hf : ∀ i, i < c → Flat B T (L + i)) (ha : T (2 * L) = 0) :
    (∀ j, j ≤ c → T (2 * (L + j)) = 0) ∧
      ∀ i, i < c → B (3 * (L + i) + 1) = 0 ∧ B (3 * (L + i) + 2) = 0 ∧
        T (2 * (L + i) + 1) = 0 := by
  obtain ⟨he, hv⟩ := flat_chain_iff_constant.mp hf
  constructor
  · intro j hj; exact (he j hj).trans ha
  · intro i hi
    obtain ⟨h0, h1, h2⟩ := hv i hi
    exact ⟨h0.trans ha, h1.trans ha, h2.trans ha⟩

/-- Complete simultaneous nullspace on the canonical vertices covered by
the selected cells. Uncovered potential coordinates do not enter this theorem. -/
theorem selected_invisible_iff_constant {M : ℕ} {B T : ℕ → ℝ}
    (ha : OldAnchored M B T) (hc : Commuting B T) :
    (∀ k, Selected M k → Invisible B T k) ↔
    ((∀ j, j ≤ cellCount M →
      T (2 * (cellStart M + j)) = T (2 * cellStart M)) ∧
      ∀ i, i < cellCount M →
        B (3 * (cellStart M + i) + 1) = T (2 * cellStart M) ∧
        B (3 * (cellStart M + i) + 2) = T (2 * cellStart M) ∧
        T (2 * (cellStart M + i) + 1) = T (2 * cellStart M)) := by
  rw [← flat_chain_iff_constant]
  constructor
  · intro hi i hic
    have hk : Selected M (cellStart M + i) :=
      (selected_iff_offset M _).mpr ⟨i, hic, rfl⟩
    exact (selected_invisible_iff_flat hk ha hc).mp (hi _ hk)
  · intro hf k hk
    obtain ⟨i, hic, rfl⟩ := (selected_iff_offset M k).mp hk
    exact (selected_invisible_iff_flat hk ha hc).mpr (hf i hic)

/-- The first covered ternary conductor is only one or two sites past the old boundary. -/
theorem root_conductor_bounds (M : ℕ) :
    M + 1 ≤ 2 * (M / 2 + 1) ∧ 2 * (M / 2 + 1) ≤ M + 2 := by omega

theorem boundary_anchor_odd (T : ℕ → ℝ) {M : ℕ}
    (hM : M % 2 = 1) (ha : T M = 0) :
    T (2 * (M / 2 + 1)) = packet T M := by
  have e : 2 * (M / 2 + 1) = M + 1 := by omega
  rw [e, packet, ha, sub_zero]

theorem boundary_anchor_even (T : ℕ → ℝ) {M : ℕ}
    (hM : M % 2 = 0) (ha : T M = 0) :
    T (2 * (M / 2 + 1)) = packet T M + packet T (M + 1) := by
  have e : 2 * (M / 2 + 1) = M + 2 := by omega
  have e2 : M + 1 + 1 = M + 2 := by omega
  rw [e]
  unfold packet
  rw [e2, ha]
  ring

/-- Exact sharp certificate for the common displacement between ternary endpoints. -/
theorem compatible_displacement_certificate (h : CellVector) (hh : Compatible h) :
    6 * sizeSq h - 5 * (binarySum h) ^ 2 =
      2 * ((h.x0 - h.x1) ^ 2 + (h.x0 - h.x2) ^ 2 + (h.x1 - h.x2) ^ 2) +
        3 * (h.y0 - h.y1) ^ 2 := by
  have hs : h.x0 + h.x1 + h.x2 = h.y0 + h.y1 := hh
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  unfold sizeSq binarySum
  nlinarith only [hs2]

theorem compatible_displacement_bound (h : CellVector) (hh : Compatible h) :
    (binarySum h) ^ 2 ≤ (6 / 5:ℝ) * sizeSq h := by
  have he := compatible_displacement_certificate h hh
  have hp : 0 ≤ 2 * ((h.x0 - h.x1) ^ 2 + (h.x0 - h.x2) ^ 2 + (h.x1 - h.x2) ^ 2) +
      3 * (h.y0 - h.y1) ^ 2 := by positivity
  linarith

end RiemannResearch.LinearAlgebra.ResonanceCellPotentials

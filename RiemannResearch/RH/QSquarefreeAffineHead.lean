/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeConstrainedMinimum
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exhaustive squarefree exact-head affine minimization

Source: user-provided Squarefree_Lattice_Log_Exp_Theory_2026-10-16,
Sections 8, 9, and 11. This verifies the complete affine feasible set
and its complete-Q minimum, allowing all large composite conductors.
The uniform bound on the growing-head minima remains Open.
The final RH theorem is a conditional research reduction using the
existing checked bounded-exact-head consumer, not an RH proof.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeAffineHead
open ZetaTwoHilbert ArithmeticCumulative QSquarefreeLatticePackets QResidueHeadSpace

def conductors (L : ℕ) : Finset ℕ := L.divisors.filter fun d => 1 < d

theorem conductor_gt_one (L : ℕ) : ∀ d ∈ conductors L, 1 < d := by
  intro d hd
  exact (Finset.mem_filter.mp hd).2

theorem divisorStage_eq_dictionary (L : ℕ) (hL : 0 < L) :
    divisorStage L = dictionary (conductors L) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    by_cases hd1 : d = 1
    · rw [hd1, qResidue_one]
      exact (dictionary (conductors L)).zero_mem
    · have hd0 := Nat.pos_of_dvd_of_pos hd hL
      apply Submodule.subset_span
      refine ⟨⟨d, ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hd, ne_of_gt hL⟩, by omega⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨d, rfl⟩
    exact Submodule.subset_span
      ⟨d, (Nat.mem_divisors.mp (Finset.mem_filter.mp d.property).1).1, rfl⟩

/-- Every nonzero low Möbius coefficient is forced into the actual period. -/
theorem exact_head_forces_conductor (H L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1)
    (d : ℕ) (hd : 1 < d) (hdH : d ≤ H)
    (hmu : ArithmeticFunction.moebius d ≠ 0) : d ∣ L := by
  rw [divisorStage_eq_dictionary L hL] at hf
  obtain ⟨c, hc⟩ := (mem_dictionary_iff (conductors L) f).mp hf
  have hh' : ∀ n, 0 < n → n ≤ H →
      (∑ e ∈ conductors L, c e * residueFraction e n) = 1 := by
    intro n hn hnH
    rw [← synthesis_sequence, hc]
    exact hh n hn hnH
  have he := Pareto.residueFraction_exact_head_coefficients
    (conductors L) c H hh' d hd hdH
  have hmem : d ∈ conductors L := by
    by_contra hnot
    rw [if_neg hnot] at he
    have hz : (ArithmeticFunction.moebius d : ℝ) = 0 := by linarith
    apply hmu
    exact_mod_cast hz
  exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1

/-- The fixed low Möbius coefficients plus one exact normalization anchor. -/
def baseline (H r : ℕ) : QHilbert :=
  QSquarefreeConstrainedMinimum.mobiusSeed H +
    ((r : ℝ) * Pareto.mobiusReciprocalSum H) • qResidue r

theorem baseline_head (H r : ℕ) (hrH : H < r) (n : ℕ)
    (hn : 0 < n) (hnH : n ≤ H) : qSequence (baseline H r) n = 1 := by
  change qSequenceLinear (_ + _) n = 1
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (QSquarefreeConstrainedMinimum.mobiusSeed H) n +
    ((r : ℝ) * Pareto.mobiusReciprocalSum H) * qSequence (qResidue r) n = 1
  rw [QSquarefreeConstrainedMinimum.mobiusSeed_head H n hn hnH, qSequence_qResidue]
  simp only [residueFraction, Nat.mod_eq_of_lt (show n < r by omega)]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp
  ring

theorem baseline_mem_divisorStage (H L r : ℕ) (hr : r ∣ L)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    baseline H r ∈ divisorStage L := by
  classical
  apply (divisorStage L).add_mem
  · apply (divisorStage L).neg_mem
    apply (divisorStage L).sum_mem
    intro d hd
    by_cases hsf : Squarefree d
    · by_cases hd1 : d = 1
      · rw [hd1, qResidue_one, smul_zero]
        exact (divisorStage L).zero_mem
      · have hd2 : 1 < d := by have := (Finset.mem_Icc.mp hd).1; omega
        exact (divisorStage L).smul_mem _
          (Submodule.subset_span ⟨d, hsmall d hd2 (Finset.mem_Icc.mp hd).2 hsf, rfl⟩)
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp only [Int.cast_zero, zero_smul]
      exact (divisorStage L).zero_mem
  · exact (divisorStage L).smul_mem _ (Submodule.subset_span ⟨r, hr, rfl⟩)

/-- Equation (8.1): the entire feasible set in a divisor stage. -/
theorem exact_head_iff (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) (f : QHilbert) :
    (f ∈ divisorStage L ∧ ∀ n, 0 < n → n ≤ H → qSequence f n = 1) ↔
      f - baseline H r ∈ zeroHeadSpan (conductors L) H r := by
  rw [divisorStage_eq_dictionary L hL]
  apply exact_head_iff_sub_mem_zeroHeadSpan (conductors L) (conductor_gt_one L)
    H r hH hr hrH
  · rw [← divisorStage_eq_dictionary L hL]
    exact baseline_mem_divisorStage H L r
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1 hsmall
  · exact baseline_head H r hrH

def optimizer (H L r : ℕ) (hr : r ∈ conductors L) : QHilbert :=
  affineOptimizer (conductors L) (conductor_gt_one L) H r hr (baseline H r) qOne

def minimumError (H L r : ℕ) (hr : r ∈ conductors L) : ℝ :=
  ‖qOne - optimizer H L r hr‖ ^ 2

theorem optimizer_feasible (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    optimizer H L r hr ∈ divisorStage L ∧
      ∀ n, 0 < n → n ≤ H → qSequence (optimizer H L r hr) n = 1 := by
  have hB : baseline H r ∈ dictionary (conductors L) := by
    rw [← divisorStage_eq_dictionary L hL]
    exact baseline_mem_divisorStage H L r
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1 hsmall
  have he := affineOptimizer_feasible (conductors L) (conductor_gt_one L) H r
    hH hr hrH (baseline H r) qOne hB (baseline_head H r hrH)
  simpa only [optimizer, ← divisorStage_eq_dictionary L hL] using he

/-- Complete error equals the true finite minimum plus the full norm-square
distance to its unique optimizer. -/
theorem minimumError_completion (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L)
    (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖qOne - f‖ ^ 2 = minimumError H L r hr + ‖f - optimizer H L r hr‖ ^ 2 := by
  have hB : baseline H r ∈ dictionary (conductors L) := by
    rw [← divisorStage_eq_dictionary L hL]
    exact baseline_mem_divisorStage H L r
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hr).1).1 hsmall
  exact affineOptimizer_error_decomposition (conductors L) (conductor_gt_one L)
    H r hH hr hrH (baseline H r) qOne hB (baseline_head H r hrH) f
    (by simpa only [← divisorStage_eq_dictionary L hL] using hf) hh

theorem minimumError_le (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L)
    (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    minimumError H L r hr ≤ ‖qOne - f‖ ^ 2 := by
  rw [minimumError_completion H L r hH hL hr hrH hsmall f hf hh]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Exact period-enlargement gain, including the full physical remainder. -/
theorem minimumError_period_gain (H L K r : ℕ) (hH : 0 < H)
    (hL : 0 < L) (hK : 0 < K) (hLK : L ∣ K)
    (hrL : r ∈ conductors L) (hrK : r ∈ conductors K) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    minimumError H L r hrL = minimumError H K r hrK +
      ‖optimizer H L r hrL - optimizer H K r hrK‖ ^ 2 := by
  have hsmallK : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ K :=
    fun d hd hdH hsf => dvd_trans (hsmall d hd hdH hsf) hLK
  have hf := optimizer_feasible H L r hH hL hrL hrH hsmall
  exact minimumError_completion H K r hH hK hrK hrH hsmallK (optimizer H L r hrL)
    (divisorStage_mono hLK hf.1) hf.2

/-- Enlargement retains every old legal competitor, including old composite
cumulants and coefficient refitting. -/
theorem minimumError_mono_period (H L K r : ℕ) (hH : 0 < H)
    (hL : 0 < L) (hK : 0 < K) (hLK : L ∣ K)
    (hrL : r ∈ conductors L) (hrK : r ∈ conductors K) (hrH : H < r)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    minimumError H K r hrK ≤ minimumError H L r hrL := by
  rw [minimumError_period_gain H L K r hH hL hK hLK hrL hrK hrH hsmall]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Changing the normalization anchor changes coordinates but not the
actual minimum over the exhaustive feasible set. -/
theorem minimumError_anchor_independent (H L r a : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (ha : a ∈ conductors L)
    (hrH : H < r) (haH : H < a)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    minimumError H L r hr = minimumError H L a ha := by
  have hf := optimizer_feasible H L r hH hL hr hrH hsmall
  have hg := optimizer_feasible H L a hH hL ha haH hsmall
  exact le_antisymm
    (minimumError_le H L r hH hL hr hrH hsmall _ hg.1 hg.2)
    (minimumError_le H L a hH hL ha haH hsmall _ hf.1 hf.2)

theorem optimizer_anchor_independent (H L r a : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (ha : a ∈ conductors L)
    (hrH : H < r) (haH : H < a)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    optimizer H L r hr = optimizer H L a ha := by
  have hg := optimizer_feasible H L a hH hL ha haH hsmall
  have he := minimumError_completion H L r hH hL hr hrH hsmall
    (optimizer H L a ha) hg.1 hg.2
  change minimumError H L a ha =
    minimumError H L r hr + ‖optimizer H L a ha - optimizer H L r hr‖ ^ 2 at he
  rw [minimumError_anchor_independent H L r a hH hL hr ha hrH haH hsmall] at he
  have hz : ‖optimizer H L a ha - optimizer H L r hr‖ ^ 2 = 0 := by linarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm

/-- Conditional research reduction. The sole analytic provider is the
displayed uniform bound on the actual complete affine minima. -/
theorem riemannHypothesis_of_bounded_affine_minima
    (L r : ℕ → ℕ) (hL : ∀ N, 0 < L N) (hsf : ∀ N, Squarefree (L N))
    (hr : ∀ N, r N ∈ conductors (L N)) (hrH : ∀ N, N + 1 < r N)
    (hsmall : ∀ N d, 1 < d → d ≤ N + 1 → Squarefree d → d ∣ L N)
    (B : ℝ) (hbudget : ∀ N, minimumError (N + 1) (L N) (r N) (hr N) ≤ B) :
    RiemannHypothesis := by
  let F : ℕ → QHilbert := fun N => optimizer (N + 1) (L N) (r N) (hr N)
  have hf (N : ℕ) := optimizer_feasible (N + 1) (L N) (r N)
    (Nat.succ_pos N) (hL N) (hr N) (hrH N) (hsmall N)
  have hl : ∀ N, F N ∈ ZetaTwoProbability.qSquarefreeCRTSpan := by
    intro N
    exact divisorStage_le_squarefreeSpan (L N) (hL N) (hsf N) (hf N).1
  have hb : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B := hbudget
  have hh : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1 := by
    intro N n hn hnN
    exact (hf N).2 n hn (by omega)
  exact (QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F hl hb hh).2.2

end RiemannResearch.RH.QSquarefreeAffineHead

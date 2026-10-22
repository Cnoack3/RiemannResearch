/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.Radical.NatInt
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

/-! The following exact head/period accounting addresses Targets 2 and 3 in the
user-provided squarefree profinite lattice research agenda, 16 October 2026.
The identities retain both actual period gains and head-extension costs.
They do not supply a uniform bound on their cumulative difference. -/

theorem minimumError_head_cost (H J L r : ℕ) (hH : 0 < H) (hHJ : H ≤ J)
    (hL : 0 < L) (hr : r ∈ conductors L) (hrJ : J < r)
    (hsmall : ∀ d, 1 < d → d ≤ J → Squarefree d → d ∣ L) :
    minimumError J L r hr = minimumError H L r hr +
      ‖optimizer J L r hr - optimizer H L r hr‖ ^ 2 := by
  have hf := optimizer_feasible J L r (lt_of_lt_of_le hH hHJ) hL hr hrJ hsmall
  exact minimumError_completion H L r hH hL hr (lt_of_le_of_lt hHJ hrJ)
    (fun d hd hdH hsf => hsmall d hd (hdH.trans hHJ) hsf)
    (optimizer J L r hr) hf.1 (fun n hn hnH => hf.2 n hn (hnH.trans hHJ))

theorem minimumError_head_period_balance (H J L K r a : ℕ)
    (hH : 0 < H) (hHJ : H ≤ J) (hL : 0 < L) (hK : 0 < K) (hLK : L ∣ K)
    (hrL : r ∈ conductors L) (hrK : r ∈ conductors K) (haK : a ∈ conductors K)
    (hrH : H < r) (haJ : J < a)
    (hsmallL : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L)
    (hsmallK : ∀ d, 1 < d → d ≤ J → Squarefree d → d ∣ K) :
    minimumError J K a haK +
        ‖optimizer H L r hrL - optimizer H K r hrK‖ ^ 2 =
      minimumError H L r hrL +
        ‖optimizer J K a haK - optimizer H K a haK‖ ^ 2 := by
  have hp := minimumError_period_gain H L K r hH hL hK hLK hrL hrK hrH hsmallL
  have hh := minimumError_head_cost H J K a hH hHJ hK haK haJ hsmallK
  have he := minimumError_anchor_independent H K r a hH hK hrK haK hrH
    (lt_of_le_of_lt hHJ haJ)
    (fun d hd hdH hsf => hsmallK d hd (hdH.trans hHJ) hsf)
  rw [he] at hp
  linarith

/-- Telescope retains both actual period gains and exact-head costs. -/
theorem minimumError_head_period_telescope
    (H L r : ℕ → ℕ) (hH : ∀ i, 0 < H i) (hmono : ∀ i, H i ≤ H (i + 1))
    (hL : ∀ i, 0 < L i) (hLK : ∀ i, L i ∣ L (i + 1))
    (hr : ∀ i, r i ∈ conductors (L i))
    (hrNext : ∀ i, r i ∈ conductors (L (i + 1)))
    (hrH : ∀ i, H i < r i)
    (hsmall : ∀ i d, 1 < d → d ≤ H i → Squarefree d → d ∣ L i) (n : ℕ) :
    minimumError (H n) (L n) (r n) (hr n) +
        (∑ i ∈ Finset.range n,
          ‖optimizer (H i) (L i) (r i) (hr i) -
            optimizer (H i) (L (i + 1)) (r i) (hrNext i)‖ ^ 2) =
      minimumError (H 0) (L 0) (r 0) (hr 0) +
        (∑ i ∈ Finset.range n,
          ‖optimizer (H (i + 1)) (L (i + 1)) (r (i + 1)) (hr (i + 1)) -
            optimizer (H i) (L (i + 1)) (r (i + 1)) (hr (i + 1))‖ ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs := minimumError_head_period_balance (H n) (H (n + 1)) (L n)
        (L (n + 1)) (r n) (r (n + 1)) (hH n) (hmono n) (hL n) (hL (n + 1))
        (hLK n) (hr n) (hrNext n) (hr (n + 1)) (hrH n) (hrH (n + 1))
        (hsmall n) (hsmall (n + 1))
      linarith

open ZetaTwoProbability SquarefreeRadicalDifference UniqueFactorizationMonoid
open QSquarefreeLatticePackets

/-- A nonsquarefree boundary adds no new interpolation condition. -/
theorem exact_head_extend_nonsquarefree (n : ℕ) (hn : 2 ≤ n)
    (hns : ¬ Squarefree n) (f : QHilbert) (hf : f ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k < n → qSequence f k = 1) :
    qSequence f n = 1 := by
  have hrad2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn
  have hradle : radical n ≤ n := Nat.le_of_dvd (by omega) radical_dvd_self
  have hradsf : Squarefree (radical n) := squarefree_radical
  have hradlt : radical n < n := by
    by_contra h
    have he : radical n = n := by omega
    exact hns (he ▸ hradsf)
  have hspan : qSquarefreeCRTSpan ≤
      Submodule.span ℝ (qResidue '' {d : ℕ | 2 ≤ d ∧ Squarefree d}) := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    exact Submodule.subset_span ⟨d.val, d.property, rfl⟩
  have hdif := span_difference_radical {d : ℕ | 2 ≤ d ∧ Squarefree d}
    (fun d hd => ⟨hd.2, hd.1⟩) n hn f (hspan hf)
  unfold qDifference at hdif
  rw [hh (n - 1) (by omega) (by omega),
    hh (radical n) (by omega) hradlt,
    hh (radical n - 1) (by omega) (by omega)] at hdif
  linarith

/-- At a nonsquarefree next site, the optimizer and complete Q minimum agree. -/
theorem nonsquarefree_boundary_no_cost (n L r : ℕ) (hn : 2 ≤ n)
    (hns : ¬ Squarefree n) (hL : 0 < L) (hsf : Squarefree L)
    (hr : r ∈ conductors L) (hrn : n < r)
    (hsmall : ∀ d, 1 < d → d ≤ n - 1 → Squarefree d → d ∣ L) :
    optimizer n L r hr = optimizer (n - 1) L r hr ∧
      minimumError n L r hr = minimumError (n - 1) L r hr := by
  have hsmalln : ∀ d, 1 < d → d ≤ n → Squarefree d → d ∣ L := by
    intro d hd hdn hdsf
    have hne : d ≠ n := by intro he; subst d; exact hns hdsf
    exact hsmall d hd (by omega) hdsf
  have hold := optimizer_feasible (n - 1) L r (by omega) hL hr (by omega) hsmall
  have hnvalue : qSequence (optimizer (n - 1) L r hr) n = 1 := by
    apply exact_head_extend_nonsquarefree n hn hns _
      (divisorStage_le_squarefreeSpan L hL hsf hold.1)
    intro k hk hkn
    exact hold.2 k hk (by omega)
  have hheadn : ∀ k, 0 < k → k ≤ n →
      qSequence (optimizer (n - 1) L r hr) k = 1 := by
    intro k hk hkn
    by_cases he : k = n
    · simpa only [he] using hnvalue
    · exact hold.2 k hk (by omega)
  have hupper := minimumError_le n L r (by omega) hL hr hrn hsmalln
    (optimizer (n - 1) L r hr) hold.1 hheadn
  change minimumError n L r hr ≤ minimumError (n - 1) L r hr at hupper
  have hcost := minimumError_head_cost (n - 1) n L r (by omega) (by omega)
    hL hr hrn hsmalln
  have hz : ‖optimizer n L r hr - optimizer (n - 1) L r hr‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖optimizer n L r hr - optimizer (n - 1) L r hr‖]
  have he : optimizer n L r hr = optimizer (n - 1) L r hr :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  exact ⟨he, congrArg (fun f : QHilbert => ‖qOne - f‖ ^ 2) he⟩
end RiemannResearch.RH.QSquarefreeAffineHead

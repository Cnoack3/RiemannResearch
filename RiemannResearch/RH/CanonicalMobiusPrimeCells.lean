/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedVariance
import RiemannResearch.RH.CanonicalMobiusQuotientCells
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Common boundary cells and exact weighted Mertens variance bounds

Source: user-provided common-prime-cell argument, October 15, 2026.
The finite weighted variance bounds and two-cell offset completion were developed
from the exact identities in CanonicalMobiusQuotientCells.
Primality is not used by the arithmetic estimates: positive boundary conductors
suffice. Prime boundaries provide legal squarefree canonical candidates.

The exact full-energy and finite-envelope identities retain every complementary
term. Lower bounds do not supply the uniform upper certificate needed for RH.
The short-prime-interval selection discussed in the research record uses
Baker--Harman--Pintz, Theorem 1, externally; that theorem is not formalized here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

theorem mobiusQuotientVariance_pairwise (t : Finset ℕ) (q : ℕ)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    (∑ n ∈ t, ∑ m ∈ t, positiveWeight n * positiveWeight m *
      (mobiusQuotientProfile q n - mobiusQuotientProfile q m) ^ 2) =
        2 * (∑ n ∈ t, positiveWeight n) * mobiusQuotientVariance t q :=
  FiniteWeightedVariance.pairwise_identity t positiveWeight (mobiusQuotientProfile q) hW

/-- Enlarging a common cell cannot decrease its unnormalized variance. -/
theorem mobiusQuotientVariance_mono (s t : Finset ℕ) (q : ℕ) (hst : s ⊆ t)
    (hs : (∑ n ∈ s, positiveWeight n) ≠ 0) :
    mobiusQuotientVariance s q ≤ mobiusQuotientVariance t q :=
  FiniteWeightedVariance.variance_mono s t positiveWeight (mobiusQuotientProfile q) hst
    (fun n _ => positiveWeight_nonneg n) hs

theorem boundary_common_quotient (a b p q n : ℕ) (ha : 0 < a)
    (hap : a ≤ p) (hpb : p ≤ b) (hn : n ∈ Finset.Ico (q * b) ((q + 1) * a)) :
    n / p = q := by
  have hp : 0 < p := ha.trans_le hap
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  have hlow : q ≤ n / p := (Nat.le_div_iff_mul_le hp).2
    ((Nat.mul_le_mul_left q hpb).trans hlo)
  have hhigh : n / p < q + 1 := (Nat.div_lt_iff_lt_mul hp).2
    (by simpa [Nat.mul_comm] using hhi.trans_le (Nat.mul_le_mul_left (q + 1) hap))
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhigh) hlow

theorem common_boundary_cell_nonempty_iff (a b q : ℕ) (hab : a ≤ b) :
    q * b < (q + 1) * a ↔ q * (b - a) < a := by
  have he : q * b = q * a + q * (b - a) := by
    calc
      q * b = q * ((b - a) + a) := congrArg (fun x : ℕ => q * x) (Nat.sub_add_cancel hab).symm
      _ = _ := by ring
  have htop : (q + 1) * a = q * a + a := by ring
  omega

theorem mertens_profile_succ (n : ℕ) :
    mobiusQuotientProfile 1 (n + 1) = mobiusQuotientProfile 1 n +
      (ArithmeticFunction.moebius (n + 1) : ℝ) := by
  simp only [mobiusQuotientProfile_one]
  exact Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)
    (fun d => (ArithmeticFunction.moebius d : ℝ))

theorem mertens_profile_abs_sub_le_of_le {m n : ℕ} (hmn : m ≤ n) :
    |mobiusQuotientProfile 1 n - mobiusQuotientProfile 1 m| ≤ (n : ℝ) - (m : ℝ) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hmu : |(ArithmeticFunction.moebius (n + 1) : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or (n + 1) with h | h | h <;> simp [h]
    rw [mertens_profile_succ]
    calc
      _ = |(mobiusQuotientProfile 1 n - mobiusQuotientProfile 1 m) +
          (ArithmeticFunction.moebius (n + 1) : ℝ)| := by congr 1; ring
      _ ≤ |mobiusQuotientProfile 1 n - mobiusQuotientProfile 1 m| +
          |(ArithmeticFunction.moebius (n + 1) : ℝ)| := abs_add_le _ _
      _ ≤ (n : ℝ) - (m : ℝ) + 1 := add_le_add ih hmu
      _ = _ := by push_cast; ring

theorem mertens_profile_sub_sq_le (m n : ℕ) :
    (mobiusQuotientProfile 1 n - mobiusQuotientProfile 1 m) ^ 2 ≤
      ((n : ℝ) - (m : ℝ)) ^ 2 := by
  wlog hmn : m ≤ n generalizing m n
  · have hnm : n ≤ m := le_of_not_ge hmn
    simpa only [sub_sq_comm] using this n m hnm
  have h := mul_self_le_mul_self (abs_nonneg _)
    (mertens_profile_abs_sub_le_of_le hmn)
  simpa only [← pow_two, sq_abs] using h

/-- A bound that uses no cancellation hypothesis for the Mertens function. -/
theorem mertens_variance_le_coordinate_variance (t : Finset ℕ)
    (hW : 0 < ∑ n ∈ t, positiveWeight n) :
    mobiusQuotientVariance t 1 ≤
      FiniteWeightedVariance.variance t positiveWeight (fun n => (n : ℝ)) :=
  FiniteWeightedVariance.variance_le_of_pairwise t positiveWeight (mobiusQuotientProfile 1)
    (fun n => (n : ℝ)) (fun n _ => positiveWeight_nonneg n) hW
      (fun n _ m _ => mertens_profile_sub_sq_le m n)

private theorem interval_mass_pos (L U : ℕ) (hL : 0 < L) (hLU : L < U) :
    0 < ∑ n ∈ Finset.Ico L U, positiveWeight n := by
  apply Finset.sum_pos
  · intro n hn
    have hn0 : 0 < n := hL.trans_le (Finset.mem_Ico.mp hn).1
    unfold positiveWeight
    positivity
  · exact Finset.nonempty_Ico.mpr hLU

theorem mertens_variance_interval_le (L U : ℕ) (hL : 0 < L) (hLU : L < U) :
    mobiusQuotientVariance (Finset.Ico L U) 1 ≤
      (1 / (L : ℝ) - 1 / (U : ℝ)) * ((U : ℝ) - (L : ℝ) - 1) ^ 2 / 4 := by
  have hW := interval_mass_pos L U hL hLU
  have hv := FiniteWeightedVariance.variance_le_of_bounds (Finset.Ico L U) positiveWeight
    (fun n => (n : ℝ)) (fun n _ => positiveWeight_nonneg n) hW.ne'
    (L : ℝ) ((U : ℝ) - 1)
    (fun n hn => by exact_mod_cast (Finset.mem_Ico.mp hn).1)
    (fun n hn => by
      have h : n + 1 ≤ U := (Finset.mem_Ico.mp hn).2
      have hc : (n : ℝ) + 1 ≤ (U : ℝ) := by exact_mod_cast h
      linarith)
  have hm := mertens_variance_le_coordinate_variance (Finset.Ico L U) hW
  unfold FiniteWeightedVariance.mass at hv
  rw [positiveWeight_interval L U hL hLU.le] at hv
  calc
    _ ≤ (1 / (L : ℝ) - 1 / (U : ℝ)) *
        (((U : ℝ) - 1) - (L : ℝ)) ^ 2 / 4 := hm.trans hv
    _ = _ := by ring

/-- If ell=2a-b, this is ell*(ell-1)^2/(8ab), an explicit local upper bound. -/
theorem first_boundary_variance_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 2 * a) :
    mobiusQuotientVariance (Finset.Ico b (2 * a)) 1 ≤
      (2 * (a : ℝ) - (b : ℝ)) * (2 * (a : ℝ) - (b : ℝ) - 1) ^ 2 /
        (8 * (a : ℝ) * (b : ℝ)) := by
  have hb0 : 0 < b := ha.trans_le hab
  have h := mertens_variance_interval_le b (2 * a) hb0 hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0' : (b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
  convert h using 1
  push_cast
  field_simp [ha0, hb0']
  ring

/-- Exact first and second coordinate moments give a closed finite upper comparator. -/
theorem coordinate_variance_interval_moment (L U : ℕ) (hL : 0 < L) (hLU : L < U) :
    (1 / (L : ℝ) - 1 / (U : ℝ)) *
        FiniteWeightedVariance.variance (Finset.Ico L U) positiveWeight (fun n => (n : ℝ)) =
      (1 / (L : ℝ) - 1 / (U : ℝ)) *
        ((U : ℝ) - (L : ℝ) - ∑ n ∈ Finset.Ico L U, 1 / ((n : ℝ) + 1)) -
      (∑ n ∈ Finset.Ico L U, 1 / ((n : ℝ) + 1)) ^ 2 := by
  have hm := FiniteWeightedVariance.moment_identity (Finset.Ico L U) positiveWeight
    (fun n => (n : ℝ)) (interval_mass_pos L U hL hLU).ne'
  have hfirst : (∑ n ∈ Finset.Ico L U, positiveWeight n * (n : ℝ)) =
      ∑ n ∈ Finset.Ico L U, 1 / ((n : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (hL.trans_le (Finset.mem_Ico.mp hn).1).ne'
    unfold positiveWeight
    field_simp
  have hsecond : (∑ n ∈ Finset.Ico L U, positiveWeight n * (n : ℝ) ^ 2) =
      (U : ℝ) - (L : ℝ) - ∑ n ∈ Finset.Ico L U, 1 / ((n : ℝ) + 1) := by
    calc
      _ = ∑ n ∈ Finset.Ico L U, (1 - 1 / ((n : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast (hL.trans_le (Finset.mem_Ico.mp hn).1).ne'
        unfold positiveWeight
        field_simp
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
          Nat.cast_sub hLU.le]
  unfold FiniteWeightedVariance.mass at hm
  rw [positiveWeight_interval L U hL hLU.le, hfirst, hsecond] at hm
  exact hm

/-- Exact full split specialized to the concrete first common boundary cell. -/
theorem signedMobiusAverage_first_boundary_full_energy
    (s : Finset ℕ) (α : ℕ → ℝ) (a b : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 2 * a) (hsum : ∑ Y ∈ s, α Y = 1)
    (hboundary : ∀ Y ∈ s, a ≤ Y + 1 ∧ Y + 1 ≤ b) :
    ‖hilbertOne - signedMobiusAverage s α‖ ^ 2 =
      mobiusQuotientVariance (Finset.Ico b (2 * a)) 1 +
      (1 / (b : ℝ) - 1 / ((2 * a : ℕ) : ℝ)) *
        (mobiusQuotientMean (Finset.Ico b (2 * a)) 1 +
          ∑ Y ∈ s, α Y * mobiusCellOffset Y) ^ 2 +
      ∑' n : {n : ℕ // n ∉ Finset.Ico b (2 * a)}, positiveWeight n.val *
        (hilbertSequence (hilbertOne - signedMobiusAverage s α) n.val) ^ 2 := by
  have hbounds : ∀ Y ∈ s, 1 * (Y + 1) ≤ b ∧
      2 * a ≤ (1 + 1) * (Y + 1) := by
    intro Y hY
    obtain ⟨hl, hu⟩ := hboundary Y hY
    constructor
    · simpa using hu
    · exact Nat.mul_le_mul_left 2 hl
  simpa using signedMobiusAverage_quotient_interval_full_energy s α 1 b (2 * a)
    (ha.trans_le hab) hb hsum hbounds


private theorem physical_quotient_cell_energy (s t : Finset ℕ) (α : ℕ → ℝ)
    (q : ℕ) (hsum : ∑ Y ∈ s, α Y = 1) (ht : ∀ n ∈ t, 0 < n)
    (hcell : ∀ n ∈ t, ∀ Y ∈ s, n / (Y + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    (∑ n ∈ t, positiveWeight n *
      (hilbertSequence (hilbertOne - signedMobiusAverage s α) n) ^ 2) =
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q +
          (q : ℝ) * ∑ Y ∈ s, α Y * mobiusCellOffset Y) ^ 2 := by
  rw [← signedMobiusAverage_quotient_cell_energy s t α q hsum ht hcell hW]
  apply Finset.sum_congr rfl
  intro n hn
  have he : hilbertSequence (hilbertOne - signedMobiusAverage s α) n =
      1 - hilbertSequence (signedMobiusAverage s α) n := by
    change (hilbertSequenceLinear (hilbertOne - signedMobiusAverage s α)) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n - hilbertSequence (signedMobiusAverage s α) n = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt (ht n hn)]
  rw [he]

/-- Two disjoint cells retain a nonnegative incompatibility term and the full tail. -/
theorem signedMobiusAverage_two_cells_full_energy
    (s t u : Finset ℕ) (α : ℕ → ℝ) (q r : ℕ)
    (hsum : ∑ Y ∈ s, α Y = 1) (hdis : Disjoint t u)
    (ht : ∀ n ∈ t, 0 < n) (hu : ∀ n ∈ u, 0 < n)
    (htcell : ∀ n ∈ t, ∀ Y ∈ s, n / (Y + 1) = q)
    (hucell : ∀ n ∈ u, ∀ Y ∈ s, n / (Y + 1) = r)
    (hWt : (∑ n ∈ t, positiveWeight n) ≠ 0)
    (hWu : (∑ n ∈ u, positiveWeight n) ≠ 0)
    (hK : 0 < (∑ n ∈ t, positiveWeight n) * (q : ℝ) ^ 2 +
      (∑ n ∈ u, positiveWeight n) * (r : ℝ) ^ 2) :
    let W := ∑ n ∈ t, positiveWeight n
    let V := ∑ n ∈ u, positiveWeight n
    let x := mobiusQuotientMean t q
    let y := mobiusQuotientMean u r
    let K := W * (q : ℝ) ^ 2 + V * (r : ℝ) ^ 2
    let B := ∑ Y ∈ s, α Y * mobiusCellOffset Y
    ‖hilbertOne - signedMobiusAverage s α‖ ^ 2 =
      mobiusQuotientVariance t q + mobiusQuotientVariance u r +
      W * V * ((r : ℝ) * x - (q : ℝ) * y) ^ 2 / K +
      K * (B + (W * (q : ℝ) * x + V * (r : ℝ) * y) / K) ^ 2 +
      ∑' n : {n : ℕ // n ∉ t ∪ u}, positiveWeight n.val *
        (hilbertSequence (hilbertOne - signedMobiusAverage s α) n.val) ^ 2 := by
  classical
  dsimp only
  rw [hilbert_norm_weighted_sq,
    ← (hilbertSequence_square_summable
      (hilbertOne - signedMobiusAverage s α)).sum_add_tsum_subtype_compl (t ∪ u),
    Finset.sum_union hdis,
    physical_quotient_cell_energy s t α q hsum ht htcell hWt,
    physical_quotient_cell_energy s u α r hsum hu hucell hWu]
  have hc := FiniteWeightedVariance.two_offset_completion
    (∑ n ∈ t, positiveWeight n) (∑ n ∈ u, positiveWeight n)
    (q : ℝ) (r : ℝ) (mobiusQuotientMean t q) (mobiusQuotientMean u r)
    (∑ Y ∈ s, α Y * mobiusCellOffset Y) hK.ne'
  linarith only [hc]

end RiemannResearch.RH.Pareto

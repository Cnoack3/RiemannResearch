/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ParetoResidueUniformCovariance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.ArithmeticCumulativeBasic

/-!
# Opposite uniform and complete-Q limits for normalized residue averages

Source: user-provided Squarefree_Profinite_Lattice_Q_Geometry_and_Research_Agenda_
2026-10-16, Section 8 and Target 5. The uniform statements are literal finite
common-period sums. The two-measure theorem identifies the same physical
observables before computing their different squared-error limits.

The argument uses actual residue covariances, complete-Q conductor convergence,
and Cesaro convergence. It asserts no transfer of the uniform estimate to Q.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability

def qUniformNormalizedResidue (d : ℕ) : QHilbert :=
  (2 * (d : ℝ) / ((d : ℝ) - 1)) • qResidue d

def qUniformNormalizedAverage (d : ℕ → ℕ) (M : ℕ) : QHilbert :=
  (M : ℝ)⁻¹ • ∑ j ∈ Finset.range M, qUniformNormalizedResidue (d j)

theorem qUniformNormalizedResidue_tendsto_zero
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => qUniformNormalizedResidue (d j)) atTop (𝓝 0) := by
  have hs := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
    ((tendsto_sub_atTop_nat 1).comp hd)
  have hc : Tendsto (fun j => (2 : ℝ) + 2 / ((d j - 1 : ℕ) : ℝ))
      atTop (𝓝 2) := by simpa using tendsto_const_nhds.add hs
  have hc' : Tendsto (fun j => 2 * (d j : ℝ) / ((d j : ℝ) - 1))
      atTop (𝓝 2) := by
    apply hc.congr'
    filter_upwards [hd.eventually (eventually_ge_atTop 2)] with j hj
    rw [Nat.cast_sub (by omega : 1 ≤ d j), Nat.cast_one]
    have hjR : (2 : ℝ) ≤ d j := by exact_mod_cast hj
    have hne : (d j : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hne]
    ring
  simpa only [qUniformNormalizedResidue, smul_zero] using
    hc'.smul (qResidue_tendsto_zero d hd)

theorem qUniformNormalizedAverage_tendsto_zero
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (qUniformNormalizedAverage d) atTop (𝓝 0) :=
  (qUniformNormalizedResidue_tendsto_zero d hd).cesaro_smul

theorem qUniformNormalizedAverage_error_tendsto_one
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun M => ‖qOne - qUniformNormalizedAverage d M‖ ^ 2)
      atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne) := tendsto_const_nhds
  have h := (hc.sub (qUniformNormalizedAverage_tendsto_zero d hd)).norm.pow 2
  simpa only [sub_zero, qOne_norm_sq] using h

theorem qUniformNormalizedAverage_mem_squarefreeSpan
    (p : ℕ → ℕ) (hp : ∀ j, Nat.Prime (p j)) (M : ℕ) :
    qUniformNormalizedAverage p M ∈ qSquarefreeCRTSpan := by
  unfold qUniformNormalizedAverage
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  unfold qUniformNormalizedResidue
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨p j, (hp j).two_le, (hp j).squarefree⟩, rfl⟩)
end RiemannResearch.RH.ZetaTwoHilbert

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The literal covariance of uniform-mean-normalized residue functions on
every common period. This is computed from the actual arithmetic values. -/
theorem normalized_residue_uniform_covariance (p q L : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hL : 0 < L) (hpL : p ∣ L) (hqL : q ∣ L) :
    (∑ n ∈ Finset.range L,
      (2 * residue p n / ((p : ℝ) - 1) - 1) *
      (2 * residue q n / ((q : ℝ) - 1) - 1)) / (L : ℝ) =
      ((Nat.gcd p q : ℝ) ^ 2 - 1) /
        (3 * ((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (q : ℝ) - 1 ≠ 0 := by linarith
  have he (n : ℕ) :
      (2 * residue p n / ((p : ℝ) - 1) - 1) *
        (2 * residue q n / ((q : ℝ) - 1) - 1) =
      (4 / (((p : ℝ) - 1) * ((q : ℝ) - 1))) *
        ((residue p n - ((p : ℝ) - 1) / 2) *
          (residue q n - ((q : ℝ) - 1) / 2)) := by
    field_simp [hp0, hq0]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, mul_div_assoc,
    residue_uniform_covariance p q L (by omega) (by omega) hL hpL hqL]
  field_simp [hp0, hq0]
  ring

/-- A finite arithmetic average, evaluated at an actual residue n modulo L. -/
def uniformNormalizedAverage {M : ℕ} (d : Fin M → ℕ) (n : ℕ) : ℝ :=
  (1 / (M : ℝ)) * ∑ i : Fin M, 2 * residue (d i) n / ((d i : ℝ) - 1)

/-- Exact uniform mean-square error for pairwise coprime conductors on a
common period. Distinct primes satisfy these hypotheses. All sums are literal
finite sums of residue values; no abstract independence is assumed. -/
theorem uniformNormalizedAverage_error_exact {M : ℕ} (hM : 0 < M)
    (d : Fin M → ℕ) (hd : ∀ i, 2 ≤ d i)
    (hcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (L : ℕ) (hL : 0 < L) (hdL : ∀ i, d i ∣ L) :
    (∑ n ∈ Finset.range L, (1 - uniformNormalizedAverage d n) ^ 2) / (L : ℝ) =
      (1 / (M : ℝ) ^ 2) *
        ∑ i : Fin M, ((d i : ℝ) + 1) / (3 * ((d i : ℝ) - 1)) := by
  classical
  let e : Fin M → ℕ → ℝ := fun i n =>
    2 * residue (d i) n / ((d i : ℝ) - 1) - 1
  let v : Fin M → ℝ := fun i =>
    ((d i : ℝ) + 1) / (3 * ((d i : ℝ) - 1))
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have havg (n : ℕ) : (1 - uniformNormalizedAverage d n) ^ 2 =
      (1 / (M : ℝ) ^ 2) * (∑ i : Fin M, e i n) ^ 2 := by
    have he : (∑ i : Fin M, e i n) =
        (∑ i : Fin M, 2 * residue (d i) n / ((d i : ℝ) - 1)) - (M : ℝ) := by
      simp only [e, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [he]
    unfold uniformNormalizedAverage
    field_simp [hM0]
    ring
  have hgram :
      (∑ n ∈ Finset.range L, (∑ i : Fin M, e i n) ^ 2) =
        ∑ i : Fin M, ∑ j : Fin M, ∑ n ∈ Finset.range L, e i n * e j n := by
    simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  have hpair (i j : Fin M) :
      (∑ n ∈ Finset.range L, e i n * e j n) / (L : ℝ) =
        if i = j then v i else 0 := by
    dsimp only [e]
    rw [normalized_residue_uniform_covariance (d i) (d j) L
      (hd i) (hd j) hL (hdL i) (hdL j)]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Nat.gcd_self]
      have hiR : (2 : ℝ) ≤ d i := by exact_mod_cast hd i
      have hi0 : (d i : ℝ) - 1 ≠ 0 := by linarith
      dsimp only [v]
      field_simp [hi0]
      ring
    · rw [if_neg hij, (hcop i j hij).gcd_eq_one]
      norm_num
  calc
    _ = ((1 / (M : ℝ) ^ 2) *
        ∑ n ∈ Finset.range L, (∑ i : Fin M, e i n) ^ 2) / (L : ℝ) := by
      simp_rw [havg]
      rw [← Finset.mul_sum]
    _ = (1 / (M : ℝ) ^ 2) *
        ((∑ i : Fin M, ∑ j : Fin M,
          ∑ n ∈ Finset.range L, e i n * e j n) / (L : ℝ)) := by
      rw [hgram]
      ring
    _ = (1 / (M : ℝ) ^ 2) *
        (∑ i : Fin M, ∑ j : Fin M,
          (∑ n ∈ Finset.range L, e i n * e j n) / (L : ℝ)) := by
      simp_rw [Finset.sum_div]
    _ = (1 / (M : ℝ) ^ 2) * ∑ i : Fin M, v i := by
      simp_rw [hpair]
      simp
    _ = _ := rfl

/-- The concrete uniform mean-square error is at most 1/M. This is a finite
Haar/CRT statement, distinct from the inverse-square Q error. -/
theorem uniformNormalizedAverage_error_le {M : ℕ} (hM : 0 < M)
    (d : Fin M → ℕ) (hd : ∀ i, 2 ≤ d i)
    (hcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (L : ℕ) (hL : 0 < L) (hdL : ∀ i, d i ∣ L) :
    (∑ n ∈ Finset.range L, (1 - uniformNormalizedAverage d n) ^ 2) / (L : ℝ) ≤
      1 / (M : ℝ) := by
  rw [uniformNormalizedAverage_error_exact hM d hd hcop L hL hdL]
  have hvar (i : Fin M) :
      ((d i : ℝ) + 1) / (3 * ((d i : ℝ) - 1)) ≤ 1 := by
    have hiR : (2 : ℝ) ≤ d i := by exact_mod_cast hd i
    have hden : 0 < 3 * ((d i : ℝ) - 1) := by linarith
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsum :
      (∑ i : Fin M, ((d i : ℝ) + 1) / (3 * ((d i : ℝ) - 1))) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ i : Fin M, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hvar i)
      _ = _ := by simp
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  calc
    _ ≤ (1 / (M : ℝ) ^ 2) * (M : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / (M : ℝ) := by field_simp [hM0]

end RiemannResearch.RH.Pareto

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.ZetaTwoHilbert
open ArithmeticCumulative

/-- The Q vector and the uniform-residue observable have exactly the same
physical values. Only the measure used to compute their errors differs. -/
theorem qUniformNormalizedResidue_sequence (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    qSequence (qUniformNormalizedResidue d) n =
      2 * Pareto.residue d n / ((d : ℝ) - 1) := by
  change qSequenceLinear ((2 * (d : ℝ) / ((d : ℝ) - 1)) • qResidue d) n = _
  rw [map_smul]
  change (2 * (d : ℝ) / ((d : ℝ) - 1)) * qSequence (qResidue d) n = _
  rw [qSequence_qResidue]
  simp only [residueFraction, Pareto.residue]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hd0, hd1]

/-- Exact identification of both finite averages at every physical coordinate. -/
theorem qUniformNormalizedAverage_sequence (d : ℕ → ℕ)
    (hd : ∀ j, 2 ≤ d j) (M n : ℕ) :
    qSequence (qUniformNormalizedAverage d M) n =
      Pareto.uniformNormalizedAverage (fun i : Fin M => d i.val) n := by
  unfold qUniformNormalizedAverage
  change qSequenceLinear
    ((M : ℝ)⁻¹ • ∑ j ∈ Finset.range M, qUniformNormalizedResidue (d j)) n = _
  rw [map_smul, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  change (M : ℝ)⁻¹ *
    (∑ j ∈ Finset.range M, qSequence (qUniformNormalizedResidue (d j)) n) = _
  have hterm (j : ℕ) : qSequence (qUniformNormalizedResidue (d j)) n =
      2 * Pareto.residue (d j) n / ((d j : ℝ) - 1) :=
    qUniformNormalizedResidue_sequence (d j) (hd j) n
  simp_rw [hterm]
  unfold Pareto.uniformNormalizedAverage
  rw [Finset.sum_range]
  simp only [one_div]

/-- On any sequence of common periods, the uniform mean-square errors of the
same physical averages tend to zero. No growth rate of those periods is used. -/
theorem qUniformNormalizedAverage_uniform_error_tendsto_zero
    (d : ℕ → ℕ) (hd : ∀ j, 2 ≤ d j)
    (hcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (L : ℕ → ℕ) (hL : ∀ M, 0 < L M)
    (hdL : ∀ M i, i < M → d i ∣ L M) :
    Tendsto (fun M =>
      (∑ n ∈ Finset.range (L M),
        (1 - qSequence (qUniformNormalizedAverage d M) n) ^ 2) / (L M : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Eventually.of_forall fun M =>
      div_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _)
        (Nat.cast_nonneg (L M))
  · filter_upwards [eventually_ge_atTop 1] with M hM
    simp_rw [qUniformNormalizedAverage_sequence d hd M]
    exact Pareto.uniformNormalizedAverage_error_le (by omega)
      (fun i : Fin M => d i.val) (fun i => hd i.val)
      (fun i j hij => hcop i.val j.val (by
        intro he
        exact hij (Fin.ext he)))
      (L M) (hL M) (fun i => hdL M i.val i.isLt)

/-- Opposite squared-error limits for identical legal-observable formulas:
uniform common-period error tends to zero while complete Q error tends to one.
Primality is not needed: pairwise coprime escaping conductors suffice. -/
theorem qUniformNormalizedAverage_two_measure_limits
    (d : ℕ → ℕ) (hd : ∀ j, 2 ≤ d j)
    (hescape : Tendsto d atTop atTop)
    (hcop : ∀ i j, i ≠ j → (d i).Coprime (d j))
    (L : ℕ → ℕ) (hL : ∀ M, 0 < L M)
    (hdL : ∀ M i, i < M → d i ∣ L M) :
    Tendsto (fun M =>
      (∑ n ∈ Finset.range (L M),
        (1 - qSequence (qUniformNormalizedAverage d M) n) ^ 2) / (L M : ℝ))
      atTop (𝓝 0) ∧
    Tendsto (fun M => ‖qOne - qUniformNormalizedAverage d M‖ ^ 2)
      atTop (𝓝 1) :=
  ⟨qUniformNormalizedAverage_uniform_error_tendsto_zero d hd hcop L hL hdL,
    qUniformNormalizedAverage_error_tendsto_one d hescape⟩

end RiemannResearch.RH.ZetaTwoHilbert

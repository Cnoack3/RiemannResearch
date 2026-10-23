/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SummableMultiplesRigidity
import RiemannResearch.Analysis.FirstMomentTails
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rigidity of actual Q signed tails

Source: the harmonic-mass proof in the user's uniform-dual-bound continuation,
22 October 2026. The exact signed-tail difference holds for every complete-Q
vector. Absolute first-moment summability permits the scaled-residue limit,
the signed floor identity, and the exchange of tail sums over multiples.
Together with the factorial Mobius sieve these prove that a full-conductor
annihilator with finite absolute harmonic moment is zero. Summability remains
an explicit hypothesis; it is not asserted for the actual orthogonal residual.
The final actual-residual signed-tail consumer is a conditional RH reduction.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert

def signedCoefficient (u : QHilbert) (n : ℕ) : ℝ :=
  positiveQWeight n * qSequence u n

theorem signedCoefficient_summable (u : QHilbert) : Summable (signedCoefficient u) := by
  apply (qSequence_product_summable u qOne).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, signedCoefficient]
  · simp [signedCoefficient, qSequence_qOne, qOneSequence, hn]

theorem residue_moment_eq_zero (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (d : ℕ) (hd : 2 ≤ d) :
    (∑' n : ℕ, (n % d : ℕ) * signedCoefficient u n) = 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have he : (∑' n : ℕ, (n % d : ℕ) * signedCoefficient u n) =
      (d : ℝ) * inner ℝ u (qResidue d) := by
    rw [qInner_weighted, qSequence_qResidue, ← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold signedCoefficient ArithmeticCumulative.residueFraction
    field_simp
  rw [he, hu d hd, mul_zero]

/-- Absolute first-moment summability permits the limit of the scaled
residue identities. This is a genuine summability hypothesis. -/
theorem first_moment_eq_zero (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => (n : ℝ) * signedCoefficient u n)) :
    (∑' n : ℕ, (n : ℝ) * signedCoefficient u n) = 0 := by
  have ht := tendsto_tsum_of_dominated_convergence hs.norm
    (f := fun d n => (n % d : ℕ) * signedCoefficient u n)
    (g := fun n : ℕ => (n : ℝ) * signedCoefficient u n)
    (fun n : ℕ => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop n] with d hd
      rw [Nat.mod_eq_of_lt hd])
    (Eventually.of_forall (fun d n => by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
        Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.mod_le n d) (norm_nonneg _)))
  have hz : Tendsto (fun d => ∑' n : ℕ, (n % d : ℕ) * signedCoefficient u n)
      atTop (nhds (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with d hd
    exact (residue_moment_eq_zero u hu d hd).symm
  exact tendsto_nhds_unique ht hz

theorem floor_moment_eq_zero (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => (n : ℝ) * signedCoefficient u n))
    (d : ℕ) (hd : 0 < d) :
    (∑' n : ℕ, (n / d : ℕ) * signedCoefficient u n) = 0 := by
  by_cases hd1 : d = 1
  · simpa [hd1] using first_moment_eq_zero u hu hs
  have hd2 : 2 ≤ d := by omega
  have hf : Summable (fun n : ℕ => (n / d : ℕ) * signedCoefficient u n) := by
    apply Summable.of_norm_bounded hs.norm
    intro n
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.div_le_self n d) (norm_nonneg _)
  have hr : Summable (fun n : ℕ => (n % d : ℕ) * signedCoefficient u n) := by
    apply Summable.of_norm_bounded hs.norm
    intro n
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.mod_le n d) (norm_nonneg _)
  have he : (∑' n : ℕ, (n : ℝ) * signedCoefficient u n) =
      (d : ℝ) * (∑' n : ℕ, (n / d : ℕ) * signedCoefficient u n) +
      (∑' n : ℕ, (n % d : ℕ) * signedCoefficient u n) := by
    rw [← tsum_mul_left, ← (hf.mul_left (d : ℝ)).tsum_add hr]
    apply tsum_congr
    intro n
    have hn : (n : ℝ) = (d : ℝ) * (n / d : ℕ) + (n % d : ℕ) := by
      have hnn : n = d * (n / d) + n % d := by
        have hh := Nat.mod_add_div n d
        omega
      exact_mod_cast hnn
    rw [hn]
    ring
  rw [first_moment_eq_zero u hu hs, residue_moment_eq_zero u hu d hd2, add_zero] at he
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  exact (mul_eq_zero.mp he.symm).resolve_left hdR

def signedTail (u : QHilbert) (k : ℕ) : ℝ :=
  ∑' j, signedCoefficient u (j + k)

def anchoredTail (u : QHilbert) (k : ℕ) : ℝ :=
  if k = 0 then 0 else signedTail u k

theorem anchoredTail_summable_of_firstMoment (u : QHilbert)
    (hs : Summable (fun n : ℕ => (n : ℝ) * signedCoefficient u n)) :
    Summable (anchoredTail u) := by
  have hm : Summable (fun n : ℕ => (n : ℝ) * |signedCoefficient u n|) := by
    apply hs.norm.congr
    intro n
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have ht : Summable (signedTail u) :=
    Analysis.rawTail_summable_of_firstMoment (signedCoefficient u)
      (signedCoefficient_summable u) hm
  apply Summable.of_norm_bounded ht.norm
  intro k
  dsimp [anchoredTail]
  split_ifs <;> simp

theorem signedTail_eq_tsum_cut (u : QHilbert) (k : ℕ) :
    signedTail u k = ∑' n : ℕ, if k ≤ n then signedCoefficient u n else 0 := by
  have he (j : ℕ) : (if k ≤ j + k then signedCoefficient u (j + k) else 0) =
      signedCoefficient u (j + k) := if_pos (Nat.le_add_left k j)
  have hs : Summable (fun j : ℕ =>
      if k ≤ j + k then signedCoefficient u (j + k) else 0) := by
    simpa only [he] using (summable_nat_add_iff k).mpr (signedCoefficient_summable u)
  have hi := Summable.sum_add_tsum_nat_add'
    (f := fun n : ℕ => if k ≤ n then signedCoefficient u n else 0) (k := k) hs
  have hz : (∑ i ∈ Finset.range k, if k ≤ i then signedCoefficient u i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hil := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
  rw [hz, zero_add] at hi
  simpa only [he, signedTail] using hi

/-- An exact absolutely convergent exchange of the signed tail sum over
multiples with the weighted floor sum. -/
theorem tail_multiples_eq_floor_moment (u : QHilbert)
    (hs : Summable (fun n : ℕ => (n : ℝ) * signedCoefficient u n))
    (d : ℕ) (hd : 0 < d) :
    (∑' k, if d ∣ k then anchoredTail u k else 0) =
      ∑' n : ℕ, (n / d : ℕ) * signedCoefficient u n := by
  classical
  let g : ℕ × ℕ → ℝ := fun p =>
    if p.2 ∈ Finset.Icc 1 (p.1 / d) then signedCoefficient u p.1 else 0
  have hrow (n : ℕ) : Summable (fun j : ℕ => ‖g (n, j)‖) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc 1 (n / d))
    intro j hj
    simp only [g, if_neg hj, norm_zero]
  have hrowsum (n : ℕ) : (∑' j, g (n, j)) =
      (n / d : ℕ) * signedCoefficient u n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (n / d)) (fun j hj => by simp only [g, if_neg hj])]
    calc
      _ = ∑ _j ∈ Finset.Icc 1 (n / d), signedCoefficient u n := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [g, if_pos hj]
      _ = _ := by simp
  have hnormsum (n : ℕ) : (∑' j, ‖g (n, j)‖) =
      (n / d : ℕ) * ‖signedCoefficient u n‖ := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (n / d)) (fun j hj => by simp only [g, if_neg hj, norm_zero])]
    calc
      _ = ∑ _j ∈ Finset.Icc 1 (n / d), ‖signedCoefficient u n‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [g, if_pos hj]
      _ = _ := by simp
  have hnormrows : Summable (fun n : ℕ => ∑' j, ‖g (n, j)‖) := by
    apply Summable.of_norm_bounded hs.norm
    intro n
    rw [hnormsum, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), norm_norm,
      norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.div_le_self n d) (norm_nonneg _)
  have hgn : Summable (fun p : ℕ × ℕ => ‖g p‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg (g p))).2 ⟨hrow, hnormrows⟩
  have hg : Summable g := Summable.of_norm_bounded hgn (fun _ => le_rfl)
  have hcol (j : ℕ) : (∑' n : ℕ, g (n, j)) = anchoredTail u (d * j) := by
    by_cases hj : j = 0
    · subst j
      simp [g, anchoredTail]
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hdj : d * j ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hd) hj
    rw [anchoredTail, if_neg hdj, signedTail_eq_tsum_cut]
    apply tsum_congr
    intro n
    simp only [g, Finset.mem_Icc]
    have hiff : 1 ≤ j ∧ j ≤ n / d ↔ d * j ≤ n := by
      rw [and_iff_right (by omega : 1 ≤ j), Nat.le_div_iff_mul_le hd]
      simp [Nat.mul_comm]
    simp only [hiff]
  have hsum : (∑' j, anchoredTail u (d * j)) =
      ∑' n : ℕ, (n / d : ℕ) * signedCoefficient u n := by
    have hex : (∑' j, ∑' n : ℕ, g (n, j)) = (∑' n : ℕ, ∑' j, g (n, j)) :=
      Summable.tsum_comm (f := fun n j => g (n, j)) hg
    simpa only [hcol, hrowsum] using hex
  have hinj : Function.Injective (fun j : ℕ => d * j) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hd hij
  have hsupport : Function.support (fun k : ℕ =>
      if d ∣ k then anchoredTail u k else 0) ⊆ Set.range (fun j : ℕ => d * j) := by
    intro k hk
    by_cases hdk : d ∣ k
    · obtain ⟨j, rfl⟩ := hdk
      exact ⟨j, rfl⟩
    · simp [Function.mem_support, hdk] at hk
  have he := hinj.tsum_eq hsupport
  have he' : (∑' j, anchoredTail u (d * j)) =
      ∑' k, if d ∣ k then anchoredTail u k else 0 := by
    simpa using he
  exact he'.symm.trans hsum

theorem signedTail_eq_tsum_sub_sum (u : QHilbert) (k : ℕ) :
    signedTail u k = (∑' n : ℕ, signedCoefficient u n) -
      ∑ j ∈ Finset.range k, signedCoefficient u j := by
  have he := Summable.sum_add_tsum_nat_add k (signedCoefficient_summable u)
  change (∑ j ∈ Finset.range k, signedCoefficient u j) + signedTail u k =
    (∑' n : ℕ, signedCoefficient u n) at he
  linarith

theorem signedTail_difference (u : QHilbert) (k : ℕ) :
    signedTail u k - signedTail u (k + 1) = signedCoefficient u k := by
  rw [signedTail_eq_tsum_sub_sum, signedTail_eq_tsum_sub_sum, Finset.sum_range_succ]
  ring

theorem anchoredTail_difference (u : QHilbert) (k : ℕ) (hk : 0 < k) :
    anchoredTail u k - anchoredTail u (k + 1) = signedCoefficient u k := by
  simp only [anchoredTail, if_neg (Nat.ne_of_gt hk), if_neg (Nat.succ_ne_zero k)]
  exact signedTail_difference u k

theorem eq_zero_of_anchoredTail_eq_zero (u : QHilbert) (h : anchoredTail u = 0) :
    u = 0 := by
  apply qSequence_injective
  funext k
  by_cases hk : k = 0
  · simp [hk]
  have he := anchoredTail_difference u k (Nat.pos_of_ne_zero hk)
  rw [h] at he
  have hc : signedCoefficient u k = 0 := by simpa using he.symm
  have hw : 0 < positiveQWeight k := by
    unfold positiveQWeight
    have hZ := ZetaTwoProbability.zetaTwo_pos
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    positivity
  have hu : qSequence u k = 0 := (mul_eq_zero.mp hc).resolve_left (ne_of_gt hw)
  change qSequence u k = qSequenceLinear 0 k
  rw [map_zero]
  exact hu

/-- Conditional reduction at the signed-tail level. The hypotheses concern
the actual complete-Q tail, without discarding any signed term. -/
theorem eq_zero_of_summable_tail_and_zero_multiples (u : QHilbert)
    (hs : Summable (anchoredTail u))
    (hm : ∀ d : ℕ, 0 < d →
      (∑' n : ℕ, if d ∣ n then anchoredTail u n else 0) = 0) : u = 0 := by
  apply eq_zero_of_anchoredTail_eq_zero
  exact Analysis.SummableMultiplesRigidity.eq_zero_of_multiples_tsum_eq_zero
    (anchoredTail u) hs (by simp [anchoredTail]) hm

/-- Absolute first harmonic moment rigidity, including zero-mean
annihilators. No RH assumption or target-mean hypothesis is used. -/
theorem eq_zero_of_first_moment_summable (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => (n : ℝ) * signedCoefficient u n)) : u = 0 := by
  apply eq_zero_of_summable_tail_and_zero_multiples u
    (anchoredTail_summable_of_firstMoment u hs)
  intro d hd
  rw [tail_multiples_eq_floor_moment u hs d hd]
  exact floor_moment_eq_zero u hu hs d hd

theorem eq_zero_of_harmonic_summable (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => qSequence u n / (n : ℝ))) : u = 0 := by
  apply eq_zero_of_first_moment_summable u hu
  apply (hs.div_const ZetaTwoProbability.zetaTwo).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, signedCoefficient]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold signedCoefficient positiveQWeight
  field_simp

/-- Conditional RH consumer. Both signed-tail hypotheses remain explicit;
this declaration does not assert them for the actual residual. -/
theorem riemannHypothesis_of_actualResidual_signed_tail
    (hs : Summable (anchoredTail QAnnihilatorTailEscape.actualResidual))
    (hm : ∀ d : ℕ, 0 < d →
      (∑' n : ℕ, if d ∣ n then anchoredTail QAnnihilatorTailEscape.actualResidual n else 0) = 0) :
    RiemannHypothesis := by
  have hr := eq_zero_of_summable_tail_and_zero_multiples
    QAnnihilatorTailEscape.actualResidual hs hm
  have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
    sub_eq_zero.mp hr
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  rw [he]
  exact QFullResidueProjection.closure.starProjection_apply_mem qOne

end RiemannResearch.RH.QSignedTailRigidity

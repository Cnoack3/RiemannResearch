/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSignedTailRigidity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# One-sided harmonic rigidity of complete-Q annihilators

Source: the user-provided continuation agenda, Section H1, 22 October 2026.
A finite first moment for just one sign forces a finite first moment for
both signs, by the exact residue equations. The signed-tail rigidity theorem
then forces the annihilator to vanish. No sign hypothesis on the actual
orthogonal residual is supplied by this module.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.ResidueMomentRigidity

theorem signed_parts (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- Residue annihilation upgrades one-sided first-moment summability to
full signed summability, with every cancellation retained exactly. -/
theorem firstMoment_summable_of_negative (w : ℕ → ℝ) (hw : Summable w)
    (hz : ∀ d : ℕ, 2 ≤ d → (∑' n : ℕ, (n % d : ℕ) * w n) = 0)
    (hm : Summable (fun n : ℕ => (n : ℝ) * max (-w n) 0)) :
    Summable (fun n : ℕ => (n : ℝ) * w n) := by
  have hpart (d : ℕ) (hd : 0 < d) (v : ℕ → ℝ)
      (hv : ∀ n, 0 ≤ v n) (hb : ∀ n, v n ≤ |w n|) :
      Summable (fun n : ℕ => (n % d : ℕ) * v n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (hv n)) _ (hw.abs.mul_left (d : ℝ))
    intro n
    apply mul_le_mul
    · exact_mod_cast (Nat.mod_lt n hd).le
    · exact hb n
    · exact hv n
    · exact Nat.cast_nonneg d
  have hp (d : ℕ) (hd : 0 < d) :
      Summable (fun n : ℕ => (n % d : ℕ) * max (w n) 0) :=
    hpart d hd _ (fun n => le_max_right _ _)
      (fun n => max_le (le_abs_self _) (abs_nonneg _))
  have hn (d : ℕ) (hd : 0 < d) :
      Summable (fun n : ℕ => (n % d : ℕ) * max (-w n) 0) :=
    hpart d hd _ (fun n => le_max_right _ _)
      (fun n => max_le (neg_le_abs _) (abs_nonneg _))
  have heq (d : ℕ) (hd : 2 ≤ d) :
      (∑' n : ℕ, (n % d : ℕ) * max (w n) 0) =
      ∑' n : ℕ, (n % d : ℕ) * max (-w n) 0 := by
    have hdpos : 0 < d := by omega
    have he : (∑' n : ℕ, (n % d : ℕ) * max (w n) 0) -
        (∑' n : ℕ, (n % d : ℕ) * max (-w n) 0) = 0 := by
      rw [← (hp d hdpos).tsum_sub (hn d hdpos)]
      calc
        _ = ∑' n : ℕ, (n % d : ℕ) * w n := by
          apply tsum_congr
          intro n
          rw [← mul_sub, signed_parts]
        _ = 0 := hz d hd
    exact sub_eq_zero.mp he
  have hpos : Summable (fun n : ℕ => (n : ℝ) * max (w n) 0) := by
    apply summable_of_sum_le (fun n => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
      (c := ∑' n : ℕ, (n : ℝ) * max (-w n) 0)
    intro s
    let d : ℕ := s.sup id + 2
    have hd : 2 ≤ d := by dsimp [d]; omega
    have hmod (n : ℕ) (hn : n ∈ s) : n % d = n := by
      have hnle : n ≤ s.sup id := by
        simpa only [id_eq] using (Finset.le_sup (f := id) hn)
      exact Nat.mod_eq_of_lt (by dsimp [d]; omega)
    calc
      _ = ∑ n ∈ s, (n % d : ℕ) * max (w n) 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hmod n hn]
      _ ≤ ∑' n : ℕ, (n % d : ℕ) * max (w n) 0 :=
        (hp d (by omega)).sum_le_tsum s
          (fun n _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
      _ = ∑' n : ℕ, (n % d : ℕ) * max (-w n) 0 := heq d hd
      _ ≤ ∑' n : ℕ, (n : ℝ) * max (-w n) 0 :=
        (hn d (by omega)).tsum_le_tsum (fun n =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mod_le n d)
            (le_max_right _ _)) hm
  apply (hpos.sub hm).congr
  intro n
  rw [← mul_sub, signed_parts]

end RiemannResearch.Analysis.ResidueMomentRigidity

namespace RiemannResearch.RH.QOneSidedHarmonicRigidity
open ZetaTwoHilbert QSignedTailRigidity

theorem eq_zero_of_negative_harmonic_summable (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => max (-qSequence u n) 0 / (n : ℝ))) : u = 0 := by
  apply eq_zero_of_first_moment_summable u hu
  apply Analysis.ResidueMomentRigidity.firstMoment_summable_of_negative
    (signedCoefficient u) (signedCoefficient_summable u) (residue_moment_eq_zero u hu)
  apply (hs.div_const ZetaTwoProbability.zetaTwo).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, signedCoefficient]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hw : 0 ≤ positiveQWeight n := positiveQWeight_nonneg n
  by_cases hu0 : 0 ≤ qSequence u n
  · have hc : 0 ≤ signedCoefficient u n := mul_nonneg hw hu0
    rw [max_eq_right (neg_nonpos.mpr hu0), max_eq_right (neg_nonpos.mpr hc)]
    simp
  · have hup : 0 ≤ -qSequence u n := by linarith
    have hc : 0 ≤ -signedCoefficient u n := by
      dsimp [signedCoefficient]
      nlinarith
    rw [max_eq_left hup, max_eq_left hc]
    unfold signedCoefficient positiveQWeight
    field_simp <;> ring

theorem eq_zero_of_positive_harmonic_summable (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : Summable (fun n : ℕ => max (qSequence u n) 0 / (n : ℝ))) : u = 0 := by
  have hneg : -u = 0 := by
    apply eq_zero_of_negative_harmonic_summable (-u)
    · intro d hd
      rw [inner_neg_left, hu d hd, neg_zero]
    · have hseq : qSequence (-u) = -qSequence u := qSequenceLinear.map_neg u
      simpa only [hseq, Pi.neg_apply, neg_neg] using hs
  exact neg_eq_zero.mp hneg

/-- Both nonnegative harmonic series diverge for every nonzero actual
full-span annihilator. No nonzero-mean assumption is required. -/
theorem both_signs_not_summable (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0) (hne : u ≠ 0) :
    ¬ Summable (fun n : ℕ => max (qSequence u n) 0 / (n : ℝ)) ∧
    ¬ Summable (fun n : ℕ => max (-qSequence u n) 0 / (n : ℝ)) :=
  ⟨fun hs => hne (eq_zero_of_positive_harmonic_summable u hu hs),
    fun hs => hne (eq_zero_of_negative_harmonic_summable u hu hs)⟩

theorem actualResidual_orthogonal_residue (d : ℕ) (hd : 2 ≤ d) :
    inner ℝ QAnnihilatorTailEscape.actualResidual (qResidue d) = 0 := by
  have hm : qResidue d ∈ QFullResidueProjection.closure := by
    apply QFullResidueProjection.legalSpan.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨d - 2, ?_⟩
    change qResidue (d - 2 + 2) = qResidue d
    rw [show d - 2 + 2 = d by omega]
  exact (Submodule.mem_orthogonal' _ _).mp
    QAnnihilatorTailEscape.actualResidual_mem_orthogonal (qResidue d) hm

/-- Conditional RH consumer. Neither one-sided harmonic summability
hypothesis is asserted for the actual residual. -/
theorem riemannHypothesis_of_one_sided_harmonic_summability
    (hs : Summable (fun n : ℕ => max (qSequence QAnnihilatorTailEscape.actualResidual n) 0 /
        (n : ℝ)) ∨
      Summable (fun n : ℕ => max (-qSequence QAnnihilatorTailEscape.actualResidual n) 0 /
        (n : ℝ))) : RiemannHypothesis := by
  have hr : QAnnihilatorTailEscape.actualResidual = 0 := by
    rcases hs with hp | hn
    · exact eq_zero_of_positive_harmonic_summable _ actualResidual_orthogonal_residue hp
    · exact eq_zero_of_negative_harmonic_summable _ actualResidual_orthogonal_residue hn
  have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
    sub_eq_zero.mp hr
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  rw [he]
  exact QFullResidueProjection.closure.starProjection_apply_mem qOne


theorem eq_zero_of_eventually_nonnegative (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : ∀ᶠ n : ℕ in atTop, 0 ≤ qSequence u n) : u = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hs
  apply eq_zero_of_negative_harmonic_summable u hu
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N ≤ n := by
    simp only [Finset.mem_range] at hn
    omega
  simp only [max_eq_right (neg_nonpos.mpr (hN n hnN)), zero_div]

theorem eq_zero_of_eventually_nonpositive (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hs : ∀ᶠ n : ℕ in atTop, qSequence u n ≤ 0) : u = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hs
  apply eq_zero_of_positive_harmonic_summable u hu
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N ≤ n := by
    simp only [Finset.mem_range] at hn
    omega
  simp only [max_eq_right (hN n hnN), zero_div]

/-- Every nonzero full-span annihilator has strictly positive and strictly
negative physical coordinates beyond every fixed index. -/
theorem arbitrarily_late_both_signs (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0)
    (hne : u ≠ 0) (N : ℕ) :
    (∃ n : ℕ, N < n ∧ 0 < qSequence u n) ∧
      (∃ n : ℕ, N < n ∧ qSequence u n < 0) := by
  constructor
  · by_contra h
    apply hne
    apply eq_zero_of_eventually_nonpositive u hu
    filter_upwards [eventually_gt_atTop N] with n hn
    exact le_of_not_gt (fun hp => h ⟨n, hn, hp⟩)
  · by_contra h
    apply hne
    apply eq_zero_of_eventually_nonnegative u hu
    filter_upwards [eventually_gt_atTop N] with n hn
    exact le_of_not_gt (fun hp => h ⟨n, hn, hp⟩)

/-- Conditional RH consumer: eventual one-sidedness is not supplied for
the actual residual. -/
theorem riemannHypothesis_of_eventual_residual_sign
    (hs : (∀ᶠ n : ℕ in atTop, 0 ≤ qSequence QAnnihilatorTailEscape.actualResidual n) ∨
      (∀ᶠ n : ℕ in atTop, qSequence QAnnihilatorTailEscape.actualResidual n ≤ 0)) :
    RiemannHypothesis := by
  have hr : QAnnihilatorTailEscape.actualResidual = 0 := by
    rcases hs with hp | hn
    · exact eq_zero_of_eventually_nonnegative _ actualResidual_orthogonal_residue hp
    · exact eq_zero_of_eventually_nonpositive _ actualResidual_orthogonal_residue hn
  have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
    sub_eq_zero.mp hr
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  rw [he]
  exact QFullResidueProjection.closure.starProjection_apply_mem qOne

theorem both_harmonic_partial_sums_tendsto_atTop (u : QHilbert)
    (hu : ∀ d : ℕ, 2 ≤ d → inner ℝ u (qResidue d) = 0) (hne : u ≠ 0) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      max (qSequence u n) 0 / (n : ℝ)) atTop atTop ∧
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      max (-qSequence u n) 0 / (n : ℝ)) atTop atTop := by
  have h := both_signs_not_summable u hu hne
  exact ⟨(not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := fun n : ℕ => max (qSequence u n) 0 / (n : ℝ))
    (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))).mp h.1,
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := fun n : ℕ => max (-qSequence u n) 0 / (n : ℝ))
    (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))).mp h.2⟩


end RiemannResearch.RH.QOneSidedHarmonicRigidity

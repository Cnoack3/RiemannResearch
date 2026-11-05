/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.RH.ZetaTwoRadicalRowCriterion

/-! # Squarefree physical coordinate tests for the eighth-moment criterion

The arithmetic input is the explicit approximation of QFiniteEighthMoment.
The projected test vectors are the individual Riesz representers of physical
coordinates. The constants and the cofinal sets may depend on the site.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoOptimizerStage ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.ExhaustiveWalk

/-- A single projected coordinate representer with a cofinally bounded
aligned eighth moment forces the limiting residual to vanish at that site. -/
theorem residual_site_zero_of_projected_eighth (ha : HasSubcriticalApproximation)
    (k : ℕ) (hk : 0 < k) (C : ℝ)
    (hb : ∃ᶠ N : ℕ in atTop, eighthHead ((stage N).starProjection (qSiteRiesz k)) N ≤ C) :
    qSequence limitingResidual k = 0 := by
  let s := qSiteRiesz k
  let p := closure.starProjection s
  have ht : Tendsto (fun N => (stage N).starProjection s) atTop (𝓝 p) :=
    walkProjection_tendsto squarefreeAtom id Function.surjective_id s
  have hp := summable_eighth_of_frequent_diagonal ht C hb
  have hsub (j : ℕ) : qSequence (s - p) j = qSequence s j - qSequence p j := by
    simpa only [qEvalCLM_apply] using (qEvalCLM j).map_sub s p
  have hw : Summable (fun j => positiveQWeight j * |qSequence (s - p) j| ^ 8) := by
    apply (summable_nat_add_iff (k + 1)).mp
    apply ((summable_nat_add_iff (k + 1)).mpr hp).congr
    intro j
    rw [hsub, show qSequence s (j + (k + 1)) = 0 by
      rw [show s = qSiteRiesz k from rfl, qSequence_qSiteRiesz k hk, if_neg (by omega)]]
    simp
  have ho : s - p ∈ closureᗮ := Submodule.sub_starProjection_mem_orthogonal (K := closure) s
  have hm := annihilator_mean_zero_of_eighth ha (s - p) ho hw
  have hor := Submodule.inner_right_of_mem_orthogonal (closure.starProjection_apply_mem s)
    QSquarefreeResidualTail.limitingResidual_mem_squarefree_orthogonal
  have hop := Submodule.inner_right_of_mem_orthogonal (closure.starProjection_apply_mem qOne) ho
  calc
    qSequence limitingResidual k = inner ℝ s limitingResidual :=
      (qSiteRiesz_inner k hk limitingResidual).symm
    _ = inner ℝ (s - p) limitingResidual := by
      rw [inner_sub_left, show inner ℝ p limitingResidual = 0 from hor, sub_zero]
    _ = inner ℝ limitingResidual (s - p) := real_inner_comm _ _
    _ = inner ℝ qOne (s - p) := by rw [limitingResidual, inner_sub_left, hop, sub_zero]
    _ = 0 := hm

/-- Only squarefree output sites, including 1, need column tests. -/
theorem riemannHypothesis_of_squarefree_projected_eighth
    (ha : HasSubcriticalApproximation)
    (hb : ∀ k : ℕ, 0 < k → Squarefree k → ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      eighthHead ((stage N).starProjection (qSiteRiesz k)) N ≤ C) :
    RiemannHypothesis := by
  have hzero (k : ℕ) : qSequence limitingResidual k = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k = 0
      · simp [hk]
      by_cases hs : Squarefree k
      · obtain ⟨C,hC⟩ := hb k (Nat.pos_of_ne_zero hk) hs
        exact residual_site_zero_of_projected_eighth ha k (Nat.pos_of_ne_zero hk) C hC
      · have hk1 : k ≠ 1 := by
          intro h
          exact hs (by simp [h])
        have hr : UniqueFactorizationMonoid.radical k < k := by
          apply lt_of_le_of_ne (Nat.radical_le_self_iff.mpr hk)
          intro he
          exact hs (he ▸ (UniqueFactorizationMonoid.squarefree_radical :
            Squarefree (UniqueFactorizationMonoid.radical k)))
        have hdiff := ZetaTwoRadicalRowCriterion.limitingResidual_difference_radical k (by omega)
        unfold SquarefreeRadicalDifference.qDifference at hdiff
        rw [ih (k - 1) (by omega), ih _ hr,
          ih (UniqueFactorizationMonoid.radical k - 1) (by omega)] at hdiff
        simpa using hdiff
  have hr : limitingResidual = 0 := by
    apply qSequence_injective
    funext k
    change qSequence limitingResidual k = qSequenceLinear 0 k
    rw [map_zero]
    exact hzero k
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
      (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm))

end RiemannResearch.RH.QSquarefreeFiniteDisplacement

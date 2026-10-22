/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusPolynomialHeadCriterion
import RiemannResearch.RH.BurnolFixedDampingObstruction
import RiemannResearch.RH.DampedMobiusExactSignedHeadLimits

/-!
# Sparse signed-head energy and its divergent alternative

The finite-head transfer uses the existing actual arithmetic coordinate
limits and the summable positive-damping Gram diagonal. A signed bound
at arbitrarily large physical heads suffices at any cofinal residue
cutoff, with no factor-two loss in the resulting energy bound.

The zero-propagation and accumulating-zero strategy follows J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and a
theorem of Baez-Duarte", arXiv:math/0202166, Section 4, Corollary 4.1 and
Theorem 4.2, https://arxiv.org/abs/math/0202166. The positive accumulation
parameter and sparse-head applications are elementary consequences of
that strategy and the verified finite-head infrastructure. No novelty
claim is made.

The bounds on the actual signed off-diagonal remain explicit arithmetic
hypotheses. No new unconditional subhalf membership or RH proof occurs.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Sparse signed bounds suffice at any residue cutoff tending to infinity.
The conclusion uses the actual diagonal total, without a comparison loss. -/
theorem centered_damped_energy_of_frequently_bounded_moving_heads
    {ε : ℝ} (hε : 0 < ε) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (B : ℝ)
    (hB : ∃ᶠ H : ℕ in atTop, dampedMobiusHeadOffDiagonal ε H (M H) ≤ B) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ∧
    (∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ≤
      dampedMobiusExactDiagonal ε + B := by
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ≤
      dampedMobiusExactDiagonal ε + B := by
    have ht := (dampedMobius_partial_head_tendsto hε N).comp hM
    have hf : ∃ᶠ H : ℕ in atTop,
        paretoHeadPairing N
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H))
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)) ≤
          dampedMobiusExactDiagonal ε + B := by
      apply (hB.and_eventually (eventually_ge_atTop N)).mono
      rintro H ⟨hHB, hNH⟩
      have hhead : paretoHeadPairing N
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H))
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)) ≤
          paretoHeadPairing H
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H))
          (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)) := by
        unfold paretoHeadPairing
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNH)
        intro n hn hnN
        simpa only [mul_assoc, ← pow_two] using
          mul_nonneg (positiveWeight_nonneg n) (sq_nonneg
            (hilbertSequence
              (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M H)) n))
      rw [dampedMobius_partial_head_eq_signed ε H (M H)] at hhead
      exact hhead.trans (add_le_add (dampedMobiusHeadDiagonal_le_exact hε H (M H)) hHB)
    by_contra hn
    have hlt := lt_of_not_ge hn
    obtain ⟨H, hle, hgt⟩ := (hf.and_eventually (ht.eventually (lt_mem_nhds hlt))).exists
    exact (not_lt_of_ge hle) hgt
  have hn (n : ℕ) : 0 ≤ positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2 :=
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- Failure of actual energy forces divergence, not merely unboundedness,
of the signed moving-head off-diagonal at every cofinal residue cutoff. -/
theorem dampedMobius_moving_offDiagonal_tendsto_atTop_of_not_summable
    {ε : ℝ} (hε : 0 < ε) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (henergy : ¬ Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2)) :
    Tendsto (fun H => dampedMobiusHeadOffDiagonal ε H (M H)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hn : ¬ ∃ᶠ H : ℕ in atTop, dampedMobiusHeadOffDiagonal ε H (M H) ≤ B := by
    intro hB
    exact henergy
      (centered_damped_energy_of_frequently_bounded_moving_heads hε M hM B hB).1
  filter_upwards [not_frequently.mp hn] with H hH
  exact (lt_of_not_ge hH).le

/-- Exact fixed-damping criterion with arbitrarily sparse physical heads. -/
theorem centered_damped_energy_iff_frequently_bounded_polynomial_heads
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hscale : 1 ≤ 2 * (k : ℝ) * ε) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) ↔
    ∃ B : ℝ, ∃ᶠ H : ℕ in atTop,
      dampedMobiusHeadOffDiagonal ε H ((H + 1) ^ k) ≤ B := by
  constructor
  · intro hs
    obtain ⟨B, hB⟩ :=
      (centered_damped_energy_iff_polynomial_signed_head_bound hε k hscale).mp hs
    exact ⟨B, (Eventually.of_forall hB).frequently⟩
  · rintro ⟨B, hB⟩
    have hk : 1 ≤ k := by
      by_contra hn
      have hz : k = 0 := by omega
      norm_num [hz] at hscale
    have ht : Tendsto (fun H : ℕ => (H + 1) ^ k) atTop atTop :=
      tendsto_atTop_mono
        (fun H => RiemannResearch.Analysis.le_succ_pow H k hk) tendsto_id
    exact (centered_damped_energy_of_frequently_bounded_moving_heads hε _ ht B hB).1

/-- An off-line zero excludes sparse bounded signed heads at every small
positive damping, uniformly over all residue-cutoff schedules tending to infinity. -/
theorem right_half_zero_small_damping_moving_offDiagonal_diverges
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ M : ℕ → ℕ, Tendsto M atTop atTop →
        Tendsto (fun H => dampedMobiusHeadOffDiagonal ε H (M H)) atTop atTop := by
  obtain ⟨δ, hδ, hbad⟩ :=
    right_half_zero_eventually_not_centered_damped_square_summable ρ hhalf hone hz
  refine ⟨δ, hδ, ?_⟩
  intro ε hε he M hM
  exact dampedMobius_moving_offDiagonal_tendsto_atTop_of_not_summable hε M hM
    (hbad ε hε he _)

/-- Failure of RH forces all sufficiently small dampings to diverge along
every cofinal residue-cutoff schedule. This is an implication, not a proof
that the divergent alternative is impossible. -/
theorem not_RH_small_damping_moving_offDiagonal_diverges
    (hRH : ¬ RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ M : ℕ → ℕ, Tendsto M atTop atTop →
        Tendsto (fun H => dampedMobiusHeadOffDiagonal ε H (M H)) atTop atTop := by
  have hn : ¬ (∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
      riemannZeta ρ ≠ 0) := by
    intro h
    exact hRH (RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr h)
  push Not at hn
  obtain ⟨ρ, hhalf, hone, hz⟩ := hn
  exact right_half_zero_small_damping_moving_offDiagonal_diverges ρ hhalf hone hz

/-- Finite signed bounds at dampings accumulating from above at a >= 0
exclude zeros to the right of 1/2+a. Bounds may exist only at arbitrarily
large damping indices and at arbitrarily large physical heads. -/
theorem zero_free_of_accumulating_frequently_bounded_signed_heads
    (a : ℝ) (ha : 0 ≤ a)
    (ε : ℕ → ℝ) (hε : ∀ j, a < ε j)
    (hlim : Tendsto ε atTop (𝓝 a))
    (M : ℕ → ℕ → ℕ) (hM : ∀ j, Tendsto (M j) atTop atTop)
    (hbound : ∃ᶠ j : ℕ in atTop, ∃ B : ℝ, ∃ᶠ H : ℕ in atTop,
      dampedMobiusHeadOffDiagonal (ε j) H (M j H) ≤ B) :
    ∀ ρ : ℂ, (1 / 2 : ℝ) + a < ρ.re → ρ.re < 1 → riemannZeta ρ ≠ 0 := by
  intro ρ hhalf hone hz
  have hr : ρ - (a : ℂ) ≠ 1 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at he'
    linarith
  obtain ⟨δ, hδ, hlocal⟩ := Burnol.zeta_small_left_shift_ne_zero (ρ - (a : ℂ)) hr
  have hgap : 0 < ρ.re - 1 / 2 - a := by linarith
  have hmargin : a < a + min δ (ρ.re - 1 / 2 - a) :=
    lt_add_of_pos_right a (lt_min hδ hgap)
  obtain ⟨j, hj, hsmall⟩ :=
    (hbound.and_eventually (hlim.eventually (gt_mem_nhds hmargin))).exists
  obtain ⟨B, hB⟩ := hj
  have hpos : 0 < ε j := lt_of_le_of_lt ha (hε j)
  have henergy := (centered_damped_energy_of_frequently_bounded_moving_heads
    hpos (M j) (hM j) B hB).1
  have hdiff : ε j - a < δ := by
    have hm := min_le_left δ (ρ.re - 1 / 2 - a)
    linarith
  have heligible : (1 / 2 : ℝ) + ε j < ρ.re := by
    have hm := min_le_right δ (ρ.re - 1 / 2 - a)
    linarith
  have hne := hlocal (ε j - a) (sub_pos.mpr (hε j)) hdiff
  have heq : (ρ - (a : ℂ)) - ((ε j - a : ℝ) : ℂ) = ρ - (ε j : ℂ) := by
    push_cast
    ring
  rw [heq] at hne
  exact hne (centered_damped_square_summable_zero_propagation hpos.le
    (1 / riemannZeta (1 + (ε j : ℂ))).re henergy ρ heligible hone hz)

/-- Conditional RH reduction: both the damping indices and the physical
heads may be arbitrarily sparse. No common bound across damping stages. -/
theorem riemannHypothesis_of_doubly_frequent_signed_heads
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (M : ℕ → ℕ → ℕ) (hM : ∀ j, Tendsto (M j) atTop atTop)
    (hbound : ∃ᶠ j : ℕ in atTop, ∃ B : ℝ, ∃ᶠ H : ℕ in atTop,
      dampedMobiusHeadOffDiagonal (ε j) H (M j H) ≤ B) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  simpa only [add_zero] using
    zero_free_of_accumulating_frequently_bounded_signed_heads
      0 le_rfl ε hpos hlim M hM hbound

/-- Completely explicit arithmetic-only sparse-head hypothesis sufficient
for RH. The signed bound remains Open. -/
theorem riemannHypothesis_of_sparse_reciprocal_polynomial_signed_heads
    (hbound : ∃ᶠ j : ℕ in atTop, ∃ B : ℝ, ∃ᶠ H : ℕ in atTop,
      dampedMobiusHeadOffDiagonal (1 / ((j + 3 : ℕ) : ℝ)) H ((H + 1) ^ (j + 3)) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_doubly_frequent_signed_heads
    (fun j => 1 / ((j + 3 : ℕ) : ℝ)) (fun j => by positivity) _
    (fun j H => (H + 1) ^ (j + 3)) _ hbound
  · have ht : Tendsto (fun j : ℕ => ((j + 3 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ht
  · intro j
    exact tendsto_atTop_mono
      (fun H => RiemannResearch.Analysis.le_succ_pow H (j + 3) (by omega)) tendsto_id

end RiemannResearch.RH.Pareto

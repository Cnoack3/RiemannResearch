/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QProjectionMoments
import Mathlib.Tactic.Push
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The actual squarefree projection residual and its complete Q tail

Source: the user's projection-limit and residual-tail discussion, 25 October
2026. The existing exact-head/PNT provider and Bertrand's theorem give legal
squarefree exact heads at comparable cutoffs. This transfers the tail argument
to the actual squarefree residual without identifying it with the full-conductor
residual. No normalized-tail upper bound, target membership, or RH is assumed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeResidualTail
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QFiniteSupportDualCriterion
open QAnnihilatorTailEscape

theorem squarefree_exactHead_mem_closure (M : ℕ) (hs : Squarefree (M + 1)) :
    QMobiusExactHead.exactHead M ∈ ZetaTwoOptimizerStage.closure := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeCRTSpan.le_topologicalClosure
    (QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan M hs)

theorem defect_inner_shorter_head (N M : ℕ) (hNM : N ≤ M) (u : QHilbert) :
    inner ℝ (defect M) (finiteHead N u) = 0 := by
  have he : inner ℝ (QMobiusExactHead.exactHead M) (finiteHead N u) =
      inner ℝ qOne (finiteHead N u) := by
    apply inner_finiteHead_eq_of_matching_head
    intro k hk hkN
    rw [QMobiusExactHead.exactHead_exact M k hk (hkN.trans hNM)]
    simp [qOneSequence, Nat.ne_of_gt hk]
  rw [defect, inner_sub_left, he, sub_self]

/-- Exact signed identity for a genuinely squarefree exact head. -/
theorem squarefree_defect_tail_identity (N M : ℕ) (hNM : N ≤ M)
    (hs : Squarefree (M + 1)) (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) :
    inner ℝ (defect M) (tail N u) = inner ℝ qOne u := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (squarefree_exactHead_mem_closure M hs) hu
  rw [tail, inner_sub_right, defect_inner_shorter_head N M hNM u,
    sub_zero, defect, inner_sub_left, hz, sub_zero]

theorem squarefree_defect_tail_sq_bound (N M : ℕ) (hNM : N ≤ M)
    (hs : Squarefree (M + 1)) (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) :
    (inner ℝ qOne u) ^ 2 ≤ ‖defect M‖ ^ 2 * ‖tail N u‖ ^ 2 := by
  have h := abs_real_inner_le_norm (defect M) (tail N u)
  rw [squarefree_defect_tail_identity N M hNM hs u hu] at h
  have hh := mul_self_le_mul_self (abs_nonneg (inner ℝ qOne u)) h
  nlinarith [sq_abs (inner ℝ qOne u)]

/-- Positive mean forces scaled complete-Q tail escape in the squarefree space.
The old full-conductor annihilator hypothesis is not used. -/
theorem squarefree_annihilator_scaled_tail_tendsto
    (u : QHilbert) (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖tail N u‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hc : 0 < (inner ℝ qOne u) ^ 2 := sq_pos_of_ne_zero hm
  have heps : 0 < (inner ℝ qOne u) ^ 2 / (2 * b) :=
    div_pos hc (by positivity)
  have ht := (tendsto_order.1 defect_sq_sublinear).2 _ heps
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ht
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  have hNpos : 0 < N := by omega
  obtain ⟨p, hp, hNp, hp2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  let M : ℕ := p - 1
  have hNM : N ≤ M := by dsimp [M]; omega
  have hMp : M + 1 = p := by dsimp [M]; omega
  have hsf : Squarefree (M + 1) := by rw [hMp]; exact hp.squarefree
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM2N : (M : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show M ≤ 2 * N by dsimp [M]; omega)
  have hs := hN0 M (by omega)
  have hcross : ‖defect M‖ ^ 2 * (2 * b) <
      (inner ℝ qOne u) ^ 2 * (M : ℝ) :=
    (div_lt_div_iff₀ hMpos (by positivity : 0 < 2 * b)).mp hs
  have hscale := mul_le_mul_of_nonneg_left hM2N hc.le
  have hsmall : ‖defect M‖ ^ 2 * b <
      (inner ℝ qOne u) ^ 2 * (N : ℝ) := by nlinarith
  have hpair := squarefree_defect_tail_sq_bound N M hNM hsf u hu
  have hpairN := mul_le_mul_of_nonneg_right hpair (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  by_contra hbad
  have htail : (N : ℝ) * ‖tail N u‖ ^ 2 ≤ b :=
    (le_of_not_ge hbad).trans hBb.le
  have hprod := mul_le_mul_of_nonneg_left htail (sq_nonneg ‖defect M‖)
  nlinarith

theorem limitingResidual_mem_squarefree_orthogonal :
    limitingResidual ∈ ZetaTwoOptimizerStage.closureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal
    (K := ZetaTwoOptimizerStage.closure) qOne

def residualTailEnergy (N : ℕ) : ℝ := ‖tail N limitingResidual‖ ^ 2

/-- The ordinary, unscaled tail always tends to zero. -/
theorem residualTailEnergy_tendsto_zero :
    Tendsto residualTailEnergy atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => ‖tail N limitingResidual‖ ^ 2) atTop (𝓝 0)
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
    (tail_tendsto_zero limitingResidual).norm.pow 2

/-- Strict projection has finite residual norm but divergent normalized tails. -/
theorem scaled_residual_tail_tendsto_of_ne_zero (hr : limitingResidual ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop := by
  apply squarefree_annihilator_scaled_tail_tendsto limitingResidual
    limitingResidual_mem_squarefree_orthogonal
  have hm : inner ℝ qOne limitingResidual = ‖limitingResidual‖ ^ 2 := by
    rw [real_inner_comm]
    exact qResidual_inner_qOne ZetaTwoOptimizerStage.closure
  rw [hm]
  exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hr))

theorem actual_squarefree_tail_dichotomy :
    (limitingResidual = 0 ∧ ∀ N : ℕ, residualTailEnergy N = 0) ∨
    (limitingResidual ≠ 0 ∧
      Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop) := by
  by_cases hr : limitingResidual = 0
  · exact Or.inl ⟨hr, by intro N; simp [residualTailEnergy, tail, finiteHead, hr]⟩
  · exact Or.inr ⟨hr, scaled_residual_tail_tendsto_of_ne_zero hr⟩

/-- Conditional research reduction: the frequent normalized-tail bound is Open. -/
theorem residual_zero_iff_frequently_bounded_scaled_tail :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    simp [residualTailEnergy, tail, finiteHead, hr]
  · rintro ⟨C, hC⟩
    by_contra hr
    have ht := scaled_residual_tail_tendsto_of_ne_zero hr
    have hg := ht.eventually (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

/-- For the actual squarefree residual, physical boundedness is equivalent to zero. -/
theorem limitingResidual_eq_zero_iff_physically_bounded :
    limitingResidual = 0 ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |qSequence limitingResidual k| ≤ C := by
  constructor
  · intro hr
    refine ⟨0, le_rfl, ?_⟩
    intro k
    cases k <;> simp [hr, qSequence]
  · rintro ⟨C, hC, hu⟩
    apply residual_zero_iff_frequently_bounded_scaled_tail.mpr
    refine ⟨2 * C ^ 2 / zetaTwo, (Eventually.of_forall ?_).frequently⟩
    intro N
    exact scaled_tail_energy_le_of_bounded limitingResidual N C hC hu

theorem limitingProjection_eq_one_iff_physically_bounded :
    ZetaTwoOptimizerStage.closure.starProjection qOne = qOne ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
        |qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) k| ≤ C := by
  have hone (k : ℕ) : |qSequence qOne k| ≤ 1 := by
    rw [qSequence_qOne]
    by_cases hk : k = 0 <;> simp [qOneSequence, hk]
  constructor
  · intro h
    exact ⟨1, by norm_num, by simpa only [h] using hone⟩
  · rintro ⟨C, hC, hF⟩
    have hr : limitingResidual = 0 := by
      apply limitingResidual_eq_zero_iff_physically_bounded.mpr
      refine ⟨1 + C, by positivity, ?_⟩
      intro k
      have he : qSequence limitingResidual k = qSequence qOne k -
          qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) k := by
        change qSequenceLinear
          (qOne - ZetaTwoOptimizerStage.closure.starProjection qOne) k = _
        rw [map_sub]
        rfl
      rw [he]
      calc
        _ ≤ |qSequence qOne k| +
            |qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) k| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (qSequence qOne k)
              (-qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) k)
        _ ≤ 1 + C := add_le_add (hone k) (hF k)
    exact (sub_eq_zero.mp hr).symm

/-- A strict limiting projection is an unbounded physical function. -/
theorem strict_limitingProjection_physically_unbounded
    (hF : ZetaTwoOptimizerStage.closure.starProjection qOne ≠ qOne) (C : ℝ) :
    ∃ k : ℕ, C < |qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) k| := by
  by_contra h
  push Not at h
  have hC : 0 ≤ C :=
    (abs_nonneg (qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) 0)).trans (h 0)
  exact hF (limitingProjection_eq_one_iff_physically_bounded.mpr ⟨C, hC, h⟩)


/-- Every bounded squarefree annihilator has mean zero. It need not itself vanish. -/
theorem bounded_annihilator_mean_eq_zero (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, |qSequence u k| ≤ C) :
    inner ℝ qOne u = 0 := by
  by_contra hm
  have ht := squarefree_annihilator_scaled_tail_tendsto u hu hm
  have hg := ht.eventually (eventually_gt_atTop (2 * C ^ 2 / zetaTwo))
  obtain ⟨N, hN⟩ := hg.exists
  exact (not_lt_of_ge (scaled_tail_energy_le_of_bounded u N C hC hb)) hN

/-- A bounded faithful test of the actual residual cannot remain orthogonal
unless the residual is zero. The arithmetic work is establishing orthogonality
for the specific test supplied by a change of measure. -/
theorem limitingResidual_eq_zero_of_bounded_faithful_test
    (T : QHilbert → QHilbert)
    (hfaithful : ∀ u : QHilbert, inner ℝ u (T u) = 0 → u = 0)
    (ho : T limitingResidual ∈ ZetaTwoOptimizerStage.closureᗮ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, |qSequence (T limitingResidual) k| ≤ C) :
    limitingResidual = 0 := by
  apply hfaithful limitingResidual
  have hm := bounded_annihilator_mean_eq_zero (T limitingResidual) ho C hC hb
  have hp := Submodule.inner_right_of_mem_orthogonal
    (ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne) ho
  change inner ℝ (qOne - ZetaTwoOptimizerStage.closure.starProjection qOne)
    (T limitingResidual) = 0
  rw [inner_sub_left, hm, hp, sub_self]

end RiemannResearch.RH.QSquarefreeResidualTail

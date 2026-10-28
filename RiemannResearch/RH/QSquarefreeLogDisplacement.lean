/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QScaledTailPerturbation
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Bertrand
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic tail rigidity for the Q/Pareto projection displacement

Source: the user's two-residual argument and Squarefree_RH_Advance_20261026.md.
The existing complete exact-head logarithmic energy provider is transferred
to squarefree annihilators by choosing a prime p with N < p <= 2*N and
the legal exact head at p-1. No full-conductor orthogonality is assumed.

For d = f_Q-f_P, a nonzero residual forces every logarithmically normalized
complete Q tail of d to diverge. A frequently bounded such tail therefore
forces target membership and Mathlib's RiemannHypothesis.
The displayed tail bound remains an OPEN arithmetic premise.

The exact signed tail identity is retained in QScaledTailPerturbation.
The physical polylogarithmic corollary is formalized below, including
arbitrary fixed real exponents. Its physical envelope remains OPEN.
The stronger complete stretched-tail displacement extension is formalized in
QSquarefreeStretchedDisplacement; its physical envelope remains OPEN.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeLogDisplacement
open ZetaTwoHilbert QFiniteSupportDualCriterion ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QSquarefreeResidualTail
open QSquarefreeDisplacementRigidity

theorem squarefree_annihilator_log_tail
    (u : QHilbert) (hu : u ∈ closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) *
      ‖tail N u‖ ^ 2) atTop atTop := by
  let w : ℕ → ℝ := fun N => (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k
  change Tendsto (fun N => w N * ‖tail N u‖ ^ 2) atTop atTop
  apply tendsto_atTop.2
  intro A
  let b : ℝ := max A 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hAb : A < b := by dsimp [b]; linarith [le_max_left A 0]
  have hc : 0 < (inner ℝ qOne u) ^ 2 := sq_pos_of_ne_zero hm
  have heps : 0 < (inner ℝ qOne u) ^ 2 / (2 * b) := div_pos hc (by positivity)
  have ht := (tendsto_order.1 (defect_sq_log_weight_tendsto_zero k)).2 _ heps
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ht
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  have hNpos : 0 < N := by omega
  obtain ⟨p, hp, hNp, hp2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  let M : ℕ := p - 1
  have hNM : N ≤ M := by dsimp [M]; omega
  have hMp : M + 1 = p := by dsimp [M]; omega
  have hsf : Squarefree (M + 1) := by rw [hMp]; exact hp.squarefree
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM2N : (M : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show M ≤ 2 * N by dsimp [M]; omega)
  have hLN : 0 < 6 + Real.log (N : ℝ) := by linarith [Real.log_nonneg hN1]
  have hlog := Real.log_le_log hNR hNMreal
  have hLM : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hpow : (6 + Real.log (N : ℝ)) ^ k ≤
      (6 + Real.log (M : ℝ)) ^ k :=
    pow_le_pow_left₀ hLN.le (by linarith) k
  have hwN : 0 < w N := div_pos hNR (pow_pos hLN k)
  have hwM : 0 < w M := div_pos hMR (pow_pos hLM k)
  have hcomp : w M ≤ 2 * w N := by
    dsimp [w]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (pow_pos hLM k) (pow_pos hLN k)).mpr
    have h1 := mul_le_mul_of_nonneg_right hM2N (pow_nonneg hLN.le k)
    have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * (N : ℝ))
    nlinarith
  have hs := hN0 M (by omega)
  have hcross : ‖defect M‖ ^ 2 * (2 * b) <
      (inner ℝ qOne u) ^ 2 * w M :=
    (div_lt_div_iff₀ hwM (by positivity : 0 < 2 * b)).mp hs
  have hscale := mul_le_mul_of_nonneg_left hcomp hc.le
  have hsmall : ‖defect M‖ ^ 2 * b <
      (inner ℝ qOne u) ^ 2 * w N := by nlinarith
  have hpair := squarefree_defect_tail_sq_bound N M hNM hsf u hu
  have hpairN := mul_le_mul_of_nonneg_right hpair hwN.le
  by_contra hbad
  have htail : w N * ‖tail N u‖ ^ 2 ≤ b :=
    (le_of_not_ge hbad).trans hAb.le
  have hprod := mul_le_mul_of_nonneg_left htail (sq_nonneg ‖defect M‖)
  nlinarith

theorem residual_zero_of_frequent_log_witness_tail (k : ℕ) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop,
      ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) * ‖tail N witness‖ ^ 2 ≤ C) :
    limitingResidual = 0 := by
  apply residual_eq_zero_of_witness_mean_zero
  by_contra hm
  have ht := squarefree_annihilator_log_tail witness witness_mem_orthogonal hm k
  obtain ⟨N, hN, hgt⟩ := (h.and_eventually
    (ht.eventually (eventually_gt_atTop C))).exists
  exact (not_lt_of_ge hN) hgt


open ZetaTwoProbability QShiftedReciprocal

theorem displacement_log_scaled_tail_tendsto (hr : limitingResidual ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) *
      ‖tail N displacement‖ ^ 2) atTop atTop := by
  let w : ℕ → ℝ := fun N => (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k
  have hw : ∀ᶠ N in atTop, 0 ≤ w N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog := Real.log_nonneg hN1
    dsimp [w]
    positivity
  have hle : ∀ᶠ N in atTop, w N ≤ (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hL : 1 ≤ 6 + Real.log (N : ℝ) := by linarith [Real.log_nonneg hN1]
    have hpow : 1 ≤ (6 + Real.log (N : ℝ)) ^ k := one_le_pow₀ hL
    dsimp [w]
    exact div_le_self (Nat.cast_nonneg N) hpow
  apply weighted_tail_transfer_sub (B pResidual) displacement w hw
    (2 * (Real.sqrt zetaTwo * ‖pResidual‖) ^ 2 / zetaTwo)
  · filter_upwards [hle] with N hN
    exact (mul_le_mul_of_nonneg_right hN (sq_nonneg _)).trans
      (scaled_tail_energy_le_of_bounded (B pResidual) N
        (Real.sqrt zetaTwo * ‖pResidual‖) (by positivity)
        (B_physical_bound pResidual))
  · exact squarefree_annihilator_log_tail witness witness_mem_orthogonal
      (fun hm => hr (residual_eq_zero_of_witness_mean_zero hm)) k

theorem residual_zero_iff_frequent_log_displacement_tail (k : ℕ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) * ‖tail N displacement‖ ^ 2 ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    simp [tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (displacement_log_scaled_tail_tendsto hr k).eventually
      (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

theorem riemannHypothesis_of_frequent_log_displacement_tail (k : ℕ)
    (h : ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) *
        ‖tail N displacement‖ ^ 2 ≤ C) : RiemannHypothesis := by
  have hr := (residual_zero_iff_frequent_log_displacement_tail k).mpr h
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)


theorem residual_zero_iff_eventually_polylog_displacement (m : ℕ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |qSequence displacement n| ≤ C * (6 + Real.log (n : ℝ)) ^ m := by
  constructor
  · intro hr
    refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
    intro n
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    cases n <;> simp [qSequence]
  · rintro ⟨C, hC, hb⟩
    exact (residual_zero_iff_frequent_log_displacement_tail (2 * m)).mpr
      ⟨_, (eventually_polylog_scaled_tail_le displacement C hC m hb).frequently⟩

theorem riemannHypothesis_of_eventually_polylog_displacement
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n : ℕ in atTop,
      |qSequence displacement n| ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_frequent_log_displacement_tail (2 * m)
    ⟨_, (eventually_polylog_scaled_tail_le displacement C hC m hb).frequently⟩

theorem riemannHypothesis_of_eventually_real_polylog_displacement
    (β C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ n : ℕ in atTop,
      |qSequence displacement n| ≤ C * (6 + Real.log (n : ℝ)) ^ β) :
    RiemannHypothesis := by
  obtain ⟨m, hm⟩ := exists_nat_ge β
  apply riemannHypothesis_of_eventually_polylog_displacement m C hC
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hL : 1 ≤ 6 + Real.log (n : ℝ) := by linarith [Real.log_nonneg hn1r]
  have hp : (6 + Real.log (n : ℝ)) ^ β ≤ (6 + Real.log (n : ℝ)) ^ m := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL hm
  exact hn.trans (mul_le_mul_of_nonneg_left hp hC)

end RiemannResearch.RH.QSquarefreeLogDisplacement

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QLcmShellMoment
import RiemannResearch.RH.QSubcriticalDisplacementMoment
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QHilbertConvergence

/-! # The actual displacement on LCM blocks

Source: user-proposed block criterion. The physical approximation at the conjugate
exponent is an explicit arithmetic hypothesis. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QLcmShellMoment
open ZetaTwoProbability ZetaTwoHilbert QSquarefreeFiniteDisplacement
open QSquarefreeDisplacementRigidity

/-- A single constant for the limiting displacement on each LCM block suffices. -/
theorem riemannHypothesis_of_lcm_displacement_blocks {p q : ℝ}
    (hpq : p.HolderConjugate q) (hq : q < 8) (ha : HasPhysicalApproximationAt p)
    (M : ℕ → ℕ) (hM : Monotone M) (hL : StrictMono (fun j => (M j).lcmUpto))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j, (∑ n ∈ Finset.Ico (M j).lcmUpto (M (j + 1)).lcmUpto,
      |qSequence displacement n| ^ 8 / (n : ℝ) ^ 2) ≤ C) : RiemannHypothesis := by
  have hs := summable_rpow_of_lcm_eighth_blocks M hM hL (qSequence displacement)
    hC h hpq.symm.pos hq
  apply riemannHypothesis_of_displacement_conjugate_moment hpq ha
  apply (hs.mul_left (1 / zetaTwo)).congr
  intro n
  simp [positiveQWeight, div_eq_mul_inv, mul_comm, mul_assoc]

/-- Each fixed block may use its own cofinal sequence of later projection stages. -/
theorem riemannHypothesis_of_frequent_fixed_lcm_blocks {p q : ℝ}
    (hpq : p.HolderConjugate q) (hq : q < 8) (ha : HasPhysicalApproximationAt p)
    (M : ℕ → ℕ) (hM : Monotone M) (hL : StrictMono (fun j => (M j).lcmUpto))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j, ∃ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ico (M j).lcmUpto (M (j + 1)).lcmUpto,
        |qSequence (finiteDisplacement N) n| ^ 8 / (n : ℝ) ^ 2) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_lcm_displacement_blocks hpq hq ha M hM hL hC
  intro j
  by_contra! hbad
  have ht : Tendsto (fun N => ∑ n ∈ Finset.Ico (M j).lcmUpto (M (j + 1)).lcmUpto,
      |qSequence (finiteDisplacement N) n| ^ 8 / (n : ℝ) ^ 2) atTop
      (𝓝 (∑ n ∈ Finset.Ico (M j).lcmUpto (M (j + 1)).lcmUpto,
        |qSequence displacement n| ^ 8 / (n : ℝ) ^ 2)) := by
    apply tendsto_finsetSum
    intro n _
    exact ((qSequence_tendsto_of_tendsto finiteDisplacement_tendsto n).abs.pow 8).div_const _
  obtain ⟨N, hN, hgt⟩ := ((h j).and_eventually (ht.eventually (Ioi_mem_nhds hbad))).exists
  exact (not_lt_of_ge hN) hgt
end RiemannResearch.RH.QLcmShellMoment

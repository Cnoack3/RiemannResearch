import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.RH.NymanConductorContinuation
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QMellinTransfer
import Mathlib.NumberTheory.LSeries.Basic

/-! # An entire charge polynomial with nonzero fixed-subtree mass

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, §§3,7,8.
A single legal prime atom has the strongest possible coefficient support
(finite) and an entire polynomial vanishing at one. Its own subtree carries a
nonzero constant mass at every sufficiently large horizon. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.PrimeTreeAtomObstruction
open ZetaTwoHilbert QPrimeSubtreeBudget ArithmeticConductorCommonZeros
open ZetaConductorRegularization QMellinTransfer

/-- The ordinary coefficient series of one atom is an actual two-term
Dirichlet polynomial on the entire plane. -/
theorem atom_charge_dirichlet (p : ℕ) (hp : 1 < p) (z : ℂ) :
    LSeries (fun n => (charge (qResidue p) n : ℂ)) z = conductorSymbol p z := by
  classical
  have hp0 : 0 < p := by omega
  have h1p : (1 : ℕ) ≠ p := by omega
  have hone : charge (qResidue p) 1 = 1 / (p : ℝ) := by
    simp [charge, qSequence_qResidue, Pareto.mobiusDifference,
      ArithmeticCumulative.residueFraction, Nat.mod_eq_of_lt hp]
  have hpp : charge (qResidue p) p = -1 := by
    simp [charge, qSequence_qResidue, Pareto.mobiusDifference_residueFraction _ _ hp]
  have hoff (n : ℕ) (hn : n ∉ ({1, p} : Finset ℕ)) :
      LSeries.term (fun m => (charge (qResidue p) m : ℂ)) z n = 0 := by
    by_cases h0 : n = 0
    · simp [h0]
    have hn1 : n ≠ 1 := fun e => hn (by simp [e])
    have hnp : n ≠ p := fun e => hn (by simp [e])
    simp [LSeries.term_def, h0, charge, qSequence_qResidue,
      Pareto.mobiusDifference_residueFraction n p (by omega), hnp]
  rw [LSeries, tsum_eq_sum hoff, conductorSymbol_eq_cpow p hp0]
  simp [Finset.sum_insert, h1p, LSeries.term_def, hp0.ne', hone, hpp, Complex.cpow_neg]
  ring

theorem atom_subtree (p H : ℕ) (hp : 1 < p) (hH : p ≤ H) :
    subtree (charge (qResidue p)) H p = -1 / (p : ℝ) := by
  classical
  have hpS : p ∈ prefixes p := by
    rw [prefixes, dif_pos hp]
    exact Finset.mem_insert_self ..
  unfold subtree
  rw [Finset.sum_eq_single p]
  · rw [if_pos hpS, charge, qSequence_qResidue, Pareto.mobiusDifference_residueFraction p p hp,
      if_pos rfl]
  · intro m _ hmp
    by_cases hm : p ∈ prefixes m
    · have hm1 : 1 < m := lt_of_lt_of_le hp (prefix_bounds hm).2
      simp only [if_pos hm, charge, qSequence_qResidue, Pareto.mobiusDifference_residueFraction
        m p hm1, if_neg hmp, zero_div]
    · simp [hm]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨by omega, hH⟩)).elim

/-- This counterexample lies in the exact legal closed space. Its full
Dirichlet polynomial is the conductor symbol and its fixed branch fails
to tend to zero. The atom Mellin identity identifies the same polynomial. -/
theorem prime_atom_obstruction (p : ℕ) (hp : Nat.Prime p) :
    qResidue p ∈ ZetaTwoOptimizerStage.closure ∧
    (∀ z : ℂ, AnalyticAt ℂ (conductorSymbol p) z) ∧
    conductorSymbol p 1 = 0 ∧
    (∀ z : ℂ, 0 < z.re → z ≠ 1 →
      qMellin (qResidue p) z = riemannZeta z / z * conductorSymbol p z) ∧
    (∀ H : ℕ, p ≤ H → subtree (charge (qResidue p)) H p = -1 / (p : ℝ)) ∧
      -1 / (p : ℝ) ≠ 0 := by
  refine ⟨?_, analyticAt_conductorSymbol p, conductorSymbol_one p hp.pos, ?_,
    fun H hH => atom_subtree p H hp.one_lt hH,
    div_ne_zero (by norm_num) (by exact_mod_cast hp.ne_zero)⟩
  · have hindex : p - 2 + 2 = p := Nat.sub_add_cancel hp.two_le
    have hm : ZetaTwoOptimizerStage.squarefreeAtom (p - 2) = qResidue p := by
      simp [ZetaTwoOptimizerStage.squarefreeAtom, hindex, hp.squarefree]
    change qResidue p ∈
      (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
    exact (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).le_topologicalClosure
      (Submodule.subset_span ⟨p - 2, hm⟩)
  · intro z hz hz1
    rw [qMellin_residue_zeta p hp.pos z hz hz1, conductorSymbol_eq_cpow p hp.pos]

end RiemannResearch.RH.PrimeTreeAtomObstruction

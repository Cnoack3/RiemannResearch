/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.Linarith
import RiemannResearch.NumberTheory.PrimeMultiplierRigidity

/-!
# Prime-product rigidity of the actual squarefree closure

Source: user-provided paper proof, final section 2, 4 November 2026.
Every four-site square relation holds on the closed legal span. Combining
these relations for three prime atoms forces the physical multiplier to be
constant. No boundedness or RH assumption occurs in the theorem.
-/

noncomputable section

namespace RiemannResearch.RH.QSquarefreeMultiplierRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage SquarefreeRadicalDifference
open ArithmeticCumulative

/-- The paper's entire family of continuous four-site annihilators. -/
theorem closure_difference_square {f : QHilbert} (hf : f ∈ closure)
    (n : ℕ) (hn : 2 ≤ n) : qDifference f (n^2) = qDifference f n := by
  have hn2 : 2 ≤ n^2 := by nlinarith
  have hspan : (Submodule.span ℝ (Set.range squarefreeAtom) : Set QHilbert) ⊆
      {x | qDifference x (n^2) = qDifference x n} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        by_cases hk : Squarefree (k+2)
        · simp only [squarefreeAtom, if_pos hk, Set.mem_ofPred_eq,
            qDifference, qSequence_qResidue]
          exact residueFraction_difference_eq_of_dvd_iff (k+2) (n^2) n
            (by omega) (by omega) (by omega)
            (hk.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0))
        · simp only [squarefreeAtom, if_neg hk, Set.mem_ofPred_eq, qDifference_zero]
    | zero => simp only [Set.mem_ofPred_eq, qDifference_zero]
    | add x y hx hy ihx ihy =>
        simp only [Set.mem_ofPred_eq] at *
        rw [qDifference_add, qDifference_add, ihx, ihy]
    | smul c x hx ih =>
        simp only [Set.mem_ofPred_eq] at *
        rw [qDifference_smul, qDifference_smul, ih]
  have hclosed : IsClosed {x : QHilbert | qDifference x (n^2) = qDifference x n} :=
    isClosed_eq (continuous_qDifference (n^2)) (continuous_qDifference n)
  exact (closure_minimal hspan hclosed) hf

/-- Prime products alone force constancy; there is no boundedness premise. -/
theorem constant_of_prime_products_mem (h : ℕ → ℝ)
    (hlegal : ∀ p : ℕ, p.Prime → ∃ f : QHilbert,
      f ∈ closure ∧ ∀ n, qSequence f n = h n * residueFraction p n) :
    ∀ n, 1 ≤ n → h n = h 1 := by
  apply RiemannResearch.NumberTheory.PrimeMultiplierRigidity.constant_of_prime_tests
  intro p hp n hn
  obtain ⟨f, hf, hphys⟩ := hlegal p hp
  have he := closure_difference_square hf n hn
  simp only [qDifference, hphys, residueFraction] at he
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0] at he
  linear_combination he

end RiemannResearch.RH.QSquarefreeMultiplierRigidity

namespace RiemannResearch.RH.QSquarefreeMultiplierRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage ArithmeticCumulative

theorem prime_atom_mem (p : ℕ) (hp : p.Prime) : qResidue p ∈ closure := by
  apply (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
  have he : p-2+2 = p := Nat.sub_add_cancel hp.two_le
  have ha : squarefreeAtom (p-2) = qResidue p := by
    simp only [squarefreeAtom, he, if_pos hp.squarefree]
  rw [← ha]
  exact Submodule.subset_span ⟨p-2, rfl⟩

/-- An everywhere-defined physical multiplier preserves legality iff constant.
Even linearity and boundedness of M need not be assumed separately. -/
theorem preserves_closure_iff_constant (h : ℕ → ℝ) (M : QHilbert → QHilbert)
    (hM : ∀ f n, qSequence (M f) n = h n * qSequence f n) :
    (∀ f, f ∈ closure → M f ∈ closure) ↔
      ∀ n, 1 ≤ n → h n = h 1 := by
  constructor
  · intro hpres
    apply constant_of_prime_products_mem h
    intro p hp
    refine ⟨M (qResidue p), hpres _ (prime_atom_mem p hp), ?_⟩
    intro n
    rw [hM, qSequence_qResidue]
  · intro hc f hf
    have he : M f = (h 1) • f := by
      apply qSequence_injective
      funext n
      rw [hM]
      have hs := congrFun (qSequenceLinear.map_smul (h 1) f) n
      change qSequence ((h 1) • f) n = h 1 * qSequence f n at hs
      rw [hs]
      cases n with
      | zero => simp only [qSequence_zero, mul_zero]
      | succ n => rw [hc (n+1) (by omega)]
    rw [he]
    exact closure.smul_mem _ hf

/-- Every nonconstant multiplier has a prime atom witnessing leakage. -/
theorem exists_prime_leakage (h : ℕ → ℝ) (M : QHilbert → QHilbert)
    (hM : ∀ f n, qSequence (M f) n = h n * qSequence f n)
    (hnon : ¬ ∀ n, 1 ≤ n → h n = h 1) :
    ∃ p : ℕ, p.Prime ∧ M (qResidue p) ∉ closure := by
  by_contra hn
  apply hnon
  apply constant_of_prime_products_mem h
  intro p hp
  have hmem : M (qResidue p) ∈ closure := by
    by_contra hm
    exact hn ⟨p, hp, hm⟩
  refine ⟨M (qResidue p), hmem, ?_⟩
  intro n
  rw [hM, qSequence_qResidue]
end RiemannResearch.RH.QSquarefreeMultiplierRigidity

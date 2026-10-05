/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexQuadraticZeroDetector
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FunProp

/-!
# Finite Mobius mollifier and actual zeta-zero detector orders

The finite exponential sum is the integral-cutoff form of M_X in
Chourasiya--Simonic, arXiv:2507.15184v2, equation (29); the detector is the
one used before equation (32): https://arxiv.org/html/2507.15184v2.
Analyticity and nontriviality of each fixed finite mollifier are proved here.
At each actual zeta cutoff point its detector order equals the original
analytic zeta multiplicity plus the mollifier order. No simplicity or
density hypothesis occurs.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier
def mollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ)*
    Complex.exp (-s*(Real.log (n : ℝ) : ℂ))
theorem mollifier_analyticAt (X : ℕ) (s : ℂ) :
    AnalyticAt ℂ (mollifier X) s := by
  unfold mollifier
  fun_prop
theorem mollifier_tendsto_one (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun t : ℝ => mollifier X (t : ℂ)) atTop (nhds 1) := by
  have hi : ∀ n ∈ Finset.Icc 1 X,
      Tendsto (fun t : ℝ => (ArithmeticFunction.moebius n : ℂ)*
        Complex.exp (-(t : ℂ)*(Real.log (n : ℝ) : ℂ))) atTop
        (nhds (if n=1 then (1 : ℂ) else 0)) := by
    intro n hn
    by_cases h1 : n=1
    · subst n
      simp
    · have hn1 : 1 < n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
      have hs : Tendsto (fun t : ℝ => t*Real.log (n : ℝ)) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hlog tendsto_id
      have he : Tendsto (fun t : ℝ => Real.exp (-t*Real.log (n : ℝ)))
          atTop (nhds 0) := by
        simpa only [Function.comp_def, pow_zero, one_mul, neg_mul] using
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hs
      have hc : Tendsto (fun t : ℝ =>
          ((Real.exp (-t*Real.log (n : ℝ)) : ℝ) : ℂ)) atTop (nhds 0) := by
        simpa only [Function.comp_def, Complex.ofReal_zero] using
          (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp he
      have hcast (t : ℝ) :
          Complex.exp (-(t : ℂ)*(Real.log (n : ℝ) : ℂ)) =
            ((Real.exp (-t*Real.log (n : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_neg, ← Complex.ofReal_mul]
        simp
      simpa only [hcast, if_neg h1, mul_zero] using
        hc.const_mul (ArithmeticFunction.moebius n : ℂ)
  have hs := tendsto_finsetSum (Finset.Icc 1 X) hi
  have he : (∑ n ∈ Finset.Icc 1 X, if n=1 then (1 : ℂ) else 0)=1 := by simp [hX]
  rw [he] at hs
  exact hs

theorem mollifier_order_ne_top (X : ℕ) (hX : 1 ≤ X) (s : ℂ) :
    analyticOrderAt (mollifier X) s ≠ ⊤ := by
  intro htop
  have hM : AnalyticOnNhd ℂ (mollifier X) Set.univ := by
    intro z hz
    exact mollifier_analyticAt X z
  have he := hM.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ)
    isPreconnected_univ (Set.mem_univ s) (analyticOrderAt_eq_top.mp htop)
  have h0 : Tendsto (fun t : ℝ => mollifier X (t : ℂ)) atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0)).congr'
      (Eventually.of_forall fun t => (he (Set.mem_univ (t : ℂ))).symm)
  exact one_ne_zero (tendsto_nhds_unique (mollifier_tendsto_one X hX) h0)

def zetaDetector (X : ℕ) : ℂ → ℂ := Complex.quadraticZeroDetector riemannZeta (mollifier X)

theorem zetaDetector_orderNat (X : ℕ) (hX : 1 ≤ X) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ ActualZeroOrdinate.cutoff T) :
    (analyticOrderAt (zetaDetector X) ρ).toNat =
      Zeta23.zeroMult ρ+(analyticOrderAt (mollifier X) ρ).toNat := by
  have hzero : riemannZeta ρ=0 := (ActualZeroOrdinate.mem_cutoff.mp hρ).1.1
  have hne : ρ ≠ 1 := by
    intro heq
    have hp := (ActualZeroOrdinate.mem_cutoff.mp hρ).2.1
    simp [heq] at hp
  have hzfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro heq
    have hp := ActualZeroOrdinate.multiplicity_pos hρ
    simp [Zeta23.zeroMult, heq] at hp
  have hmfin := mollifier_order_ne_top X hX ρ
  have he := Complex.quadraticZeroDetector_order (analyticAt_riemannZeta hne) (mollifier_analyticAt X ρ) hzero
  change (analyticOrderAt (Complex.quadraticZeroDetector riemannZeta (mollifier X)) ρ).toNat = _
  rw [he, ENat.toNat_add hzfin hmfin]
  rfl
end RiemannResearch.Analysis.InghamMollifier

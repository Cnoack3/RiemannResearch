import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Convert

/-!
# The common zeros of the continuous Nyman Mellin symbols

Source: J.-F. Burnol, A note on Nyman's equivalent formulation of the
Riemann Hypothesis, equation (2.3) and the common-zero argument following it,
https://arxiv.org/pdf/math/9910055.

This module proves that the continuous family has no common scalar zero
other than s = 1. Away from 0 and 1 its common Mellin-symbol zeros are
exactly the zeta zeros. This is the zero-set component of the invariant
subspace argument; it does not assert the Mellin integral representation,
Paley--Wiener, Beurling--Lax, or the absence of singular inner factors.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.RH.Burnol

/-- Exponential parametrization of the scalar numerator with alpha = exp(-t). -/
def nymanExpNumerator (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(t : ℂ)) - Complex.exp (-(t : ℂ) * s)

/-- No complex number except one is a common zero of every scalar numerator. -/
theorem all_nymanExpNumerator_zero_iff (s : ℂ) :
    (∀ t : ℝ, 0 < t → nymanExpNumerator t s = 0) ↔ s = 1 := by
  constructor
  · intro h
    have he (t : ℝ) (ht : 0 < t) :
        Complex.exp (-(t : ℂ)) = Complex.exp (-(t : ℂ) * s) :=
      sub_eq_zero.mp (h t ht)
    have hev : (fun t : ℝ => Complex.exp (-(t : ℂ))) =ᶠ[𝓝 1]
        (fun t : ℝ => Complex.exp (-(t : ℂ) * s)) := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact he t ht
    have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 1 := by
      convert! (Complex.ofRealCLM.hasDerivAt (x := (1 : ℝ))) using 1
    have hleft := hreal.neg.cexp
    have hright := (hreal.neg.mul_const s).cexp
    have hd := hleft.unique (hright.congr_of_eventuallyEq hev)
    have hval := he 1 (by norm_num)
    simp only [Pi.neg_apply, Complex.ofReal_one, neg_mul, one_mul] at hd hval
    rw [← hval] at hd
    have hz : Complex.exp (-1) ≠ 0 := Complex.exp_ne_zero _
    have hm : Complex.exp (-1) * (s - 1) = 0 := by linear_combination hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hz)
  · rintro rfl t ht
    simp [nymanExpNumerator]

def nymanNumerator (α : ℝ) (s : ℂ) : ℂ := (α : ℂ) - (α : ℂ) ^ s

theorem nymanNumerator_exp (t : ℝ) (s : ℂ) :
    nymanNumerator (Real.exp (-t)) s = nymanExpNumerator t s := by
  rw [nymanNumerator, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_nonneg _), Real.log_exp]
  simp [nymanExpNumerator, Complex.ofReal_exp]

theorem all_nymanNumerator_zero_iff (s : ℂ) :
    (∀ α : ℝ, 0 < α → α < 1 → nymanNumerator α s = 0) ↔ s = 1 := by
  constructor
  · intro h
    apply (all_nymanExpNumerator_zero_iff s).mp
    intro t ht
    rw [← nymanNumerator_exp]
    exact h _ (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  · rintro rfl α hα hα1
    simp [nymanNumerator]

/-- An explicit numerator which does not vanish exists at every s other than one. -/
theorem exists_nymanNumerator_ne_zero {s : ℂ} (hs : s ≠ 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ nymanNumerator α s ≠ 0 := by
  by_contra! h
  exact hs ((all_nymanNumerator_zero_iff s).mp h)

/-- The right side of Burnol's Mellin formula (2.3), with its complete zeta factor. -/
def nymanMellinSymbol (α : ℝ) (s : ℂ) : ℂ :=
  nymanNumerator α s / s * riemannZeta s

/-- Away from the two removable/singular exceptional parameters, the common
zeros are exactly those of zeta. This theorem concerns the explicit symbols. -/
theorem all_nymanMellinSymbol_zero_iff {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (∀ α : ℝ, 0 < α → α < 1 → nymanMellinSymbol α s = 0) ↔
      riemannZeta s = 0 := by
  constructor
  · intro h
    obtain ⟨α, hα, hα1, hn⟩ := exists_nymanNumerator_ne_zero hs1
    exact (mul_eq_zero.mp (h α hα hα1)).resolve_left (div_ne_zero hn hs0)
  · intro hz α hα hα1
    simp [nymanMellinSymbol, hz]

end RiemannResearch.RH.Burnol

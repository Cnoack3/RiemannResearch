/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeSignedMellin
import RiemannResearch.RH.QTreeDigitMellin
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Analytic orders of physical digits and signed CRT lifts
The multiplier in (18) is a local unit in the open strip. In (19) the multiplier
can vanish. The exact order formula retains the multiplicity of every such extra zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.PrimeTreeSignedMellin
open ArithmeticCumulative ArithmeticConductorCommonZeros CRTCarryArithmetic

private theorem local_order (f B : ℂ → ℂ) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hB : AnalyticAt ℂ B s) (he : ∀ᶠ z in 𝓝 s, f z = riemannZeta z / z * B z) :
    analyticOrderAt f s = analyticOrderAt riemannZeta s + analyticOrderAt B s := by
  have hz : AnalyticAt ℂ riemannZeta s := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) _
      (isOpen_compl_singleton.mem_nhds hs1)
    exact fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  let u : ℂ → ℂ := fun z => z⁻¹
  have hu : AnalyticAt ℂ u s := analyticAt_id.inv hs0
  have he' : f =ᶠ[𝓝 s] riemannZeta * (u * B) := by
    filter_upwards [he] with z hz
    simp only [hz, Pi.mul_apply, u, div_eq_mul_inv, mul_assoc]
  rw [analyticOrderAt_congr he', analyticOrderAt_mul hz (hu.mul hB),
    analyticOrderAt_mul hu hB, analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hs0)), zero_add]

private theorem pow_diff (d : ℕ) (hd : 0 < d) : Differentiable ℂ (fun z : ℂ => (d : ℂ) ^ (-z)) := by
  intro z
  have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  exact differentiableAt_id.neg.const_cpow (Or.inl hc)

private theorem strip_nhds' (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re ∧ z.re < 1 :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hs, hlt⟩

theorem digit_order (D p : ℕ) (hD : 0 < D) (hp : 1 < p) (s : ℂ)
    (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (fun z => ∫ x in Ioi (1 : ℝ),
      (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-z - 1)) s =
        analyticOrderAt riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hlt
  have hpp : 0 < p := by omega
  let B (z : ℂ) := (D : ℂ) ^ (-z) * (1 / (p : ℂ) - (p : ℂ) ^ (-z))
  have hconst : AnalyticAt ℂ (fun _ : ℂ => 1 / (p : ℂ)) s := analyticAt_const
  have hB : AnalyticAt ℂ B s := ((pow_diff D hD).analyticAt s).mul
    (hconst.sub ((pow_diff p hpp).analyticAt s))
  have hN : B s ≠ 0 := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hD.ne')))
    (by rw [← conductorSymbol_eq_cpow p hpp s]; exact conductorSymbol_ne_zero_of_re_ne_one p hp s hlt.ne)
  rw [← add_zero (analyticOrderAt riemannZeta s), ← analyticOrderAt_eq_zero.mpr (Or.inr hN)]
  apply local_order _ B s hs0 hs1 hB
  filter_upwards [strip_nhds' s hs hlt] with z hz
  have hz1 : z ≠ 1 := by rintro rfl; simpa using hz.2
  rw [QTreeDigitMellin.digit_integral D p hD hpp z hz.1 hz1, conductorSymbol_eq_cpow p hpp z]
  simp only [B, mul_assoc]

def physicalMultiplier {ι : Type*} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) (D : ℕ) (z : ℂ) : ℂ :=
  (liftOffset a c D : ℂ) + (D : ℂ) ^ (-z) - ∑ j, (c j : ℂ) * (a j : ℂ) ^ (-z)

theorem signed_order {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : ∀ j, 0 < a j)
    (c : ι → ℝ) (D : ℕ) (hD : 0 < D) (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (fun z => ∫ x in Ioi (1 : ℝ),
      (signedValue a c D ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-z - 1)) s =
      analyticOrderAt riemannZeta s + analyticOrderAt (physicalMultiplier a c D) s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hlt
  have hTerms (j : ι) : Differentiable ℂ (fun z : ℂ => (c j : ℂ) * (a j : ℂ) ^ (-z)) :=
    (pow_diff (a j) (ha j)).const_mul _
  have hconst : Differentiable ℂ (fun _ : ℂ => (liftOffset a c D : ℂ)) := by fun_prop
  have hsum : Differentiable ℂ (fun z : ℂ => ∑ j, (c j : ℂ) * (a j : ℂ) ^ (-z)) :=
    Differentiable.fun_sum (u := Finset.univ) (fun j _ => hTerms j)
  have hB : Differentiable ℂ (physicalMultiplier a c D) :=
    (hconst.add (pow_diff D hD)).sub hsum
  apply local_order _ _ s hs0 hs1 (hB.analyticAt s)
  filter_upwards [strip_nhds' s hs hlt] with z hz
  have hz1 : z ≠ 1 := by rintro rfl; simpa using hz.2
  exact signed_integral a ha c D hD z hz.1 hz1

end RiemannResearch.RH.PrimeTreeSignedMellin

import RiemannResearch.Analysis.LogarithmicPrimePairTriangle
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Vaughan's Cesàro estimate at real logarithmic widths

R. C. Vaughan, Proc. London Math. Soc. 82 (2001), 533–553,
https://doi.org/10.1112/plms/82.3.533. The exact normalization and the
unconditional remainder are reproduced in Goldston and Suriajaya, Acta
Arith. 200 (2021), equations (1.3)–(1.4), https://arxiv.org/abs/2007.16099.
The published analytic bound is a named, local input. The finite transfer
to actual von Mangoldt pairs retains the signed arithmetic discrepancy.
-/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open RiemannResearch.RH.AnnularPrimePair

def singularCesaro (s : ℝ) : ℝ :=
  ∑ h ∈ Ioc 0 ⌊s⌋₊, (s-h)*singularSeries h

def vaughanConstant : ℝ := 1-Real.eulerMascheroniConstant-Real.log (2*Real.pi)

def vaughanMain (s : ℝ) : ℝ := (s^2-s*Real.log s+vaughanConstant*s)/2

def vaughanDecay (c s : ℝ) : ℝ :=
  Real.sqrt s * Real.exp (-c*(Real.log (2*s))^((3:ℝ)/5) /
    (Real.log (Real.log (3*s)))^((1:ℝ)/5))

/-- The unconditional estimate at sufficiently large real widths. -/
def VaughanCesaroBound : Prop := ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ᶠ s : ℝ in atTop,
  |singularCesaro s - vaughanMain s| ≤ C*vaughanDecay c s

/-- The second term of the normalized model, including its sign. -/
def correctedTriangle (u L : ℝ) : ℝ :=
  u^2/2 + u*(vaughanConstant-Real.log u-Real.log L)/(2*L)

def triangleArithmeticError (A B u X : ℝ) : ℝ :=
  (∑ h ∈ Ioc 0 (shiftWidth u X), (u*Real.log X-h)*
    (pairBlock A B X h-(B-A)*X*singularSeries h)) / (X*(Real.log X)^2)

theorem triangle_model_exact (A B u : ℝ) {X : ℝ} (hX : 1 < X) :
    trianglePairAverage A B u X - triangleArithmeticError A B u X =
    (B-A)*singularCesaro (u*Real.log X)/(Real.log X)^2 := by
  have hx : X ≠ 0 := by linarith
  have hl := (Real.log_pos hX).ne'
  unfold trianglePairAverage triangleArithmeticError singularCesaro shiftWidth
  field_simp [hx,hl]
  simp only [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro h _
  field_simp [hl]
  ring

theorem correctedTriangle_eq {u L : ℝ} (hu : 0 < u) (hL : 0 < L) :
    vaughanMain (u*L)/L^2 = correctedTriangle u L := by
  unfold vaughanMain correctedTriangle
  rw [Real.log_mul hu.ne' hL.ne']
  field_simp [hL.ne']
  ring

/-- Quantitative transfer. Only the singular-series part uses Vaughan's paper. -/
theorem vaughan_logarithmic_triangle (published : VaughanCesaroBound)
    {A B u : ℝ} (hAB : A < B) (hu : 0 < u) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ᶠ X : ℝ in atTop,
      |trianglePairAverage A B u X - triangleArithmeticError A B u X -
        (B-A)*correctedTriangle u (Real.log X)| ≤
        (B-A)*C*vaughanDecay c (u*Real.log X)/(Real.log X)^2 := by
  obtain ⟨c,hc,C,hC,h⟩ := published
  refine ⟨c,hc,C,hC, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.const_mul_atTop hu).eventually h,
    eventually_gt_atTop (1:ℝ)] with X hb hX
  have hl := Real.log_pos hX
  rw [triangle_model_exact A B u hX, ← correctedTriangle_eq hu hl]
  have he : (B-A)*singularCesaro (u*Real.log X)/(Real.log X)^2 -
      (B-A)*(vaughanMain (u*Real.log X)/(Real.log X)^2) =
      (B-A)*(singularCesaro (u*Real.log X)-vaughanMain (u*Real.log X))/(Real.log X)^2 := by ring
  rw [he, abs_div, abs_mul, abs_of_pos (sub_pos.mpr hAB), abs_of_nonneg (sq_nonneg (Real.log X))]
  exact div_le_div_of_nonneg_right (by simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hAB.le))) (sq_nonneg _)

end RiemannResearch.Analysis.LogarithmicPrimePairs

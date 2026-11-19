import RiemannResearch.Analysis.MontgomeryReflectedGramKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Sharpness witness for the reflected pair Gram estimate

At the two maximal admissible displacements, zero frequency and equal
ordinates, the mixed difference is exactly 1/30. Thus any uniform constant
in this normalization is at least 8/15. -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryCentralDifference
open MontgomeryPoisson

/-- Uniform constant in the reflected pair kernel estimate with its original Cauchy weight. -/
def ReflectedPairQuarticEnvelope (K : ℝ) : Prop :=
  ∀ u a b d : ℝ, |a| ≤ 1/2 → |b| ≤ 1/2 →
    ‖reflectedPairKernel u a b d‖ ≤
      K*(1+|u|)^4*Real.exp (|u| * (|a| + |b|))*a^2*b^2*cauchyWeight d

theorem reflectedPairKernel_zero_half_half :
    reflectedPairKernel 0 (1/2) (1/2) 0 = (1/30:ℂ) := by
  norm_num [reflectedPairKernel,central,phaseKernel,Complex.ofReal_div]

theorem reflectedPairQuarticEnvelope_lower_bound {K : ℝ} (hK : ReflectedPairQuarticEnvelope K) :
    (8/15:ℝ) ≤ K := by
  have h := hK 0 (1/2) (1/2) 0 (by norm_num) (by norm_num)
  rw [reflectedPairKernel_zero_half_half] at h
  norm_num [cauchyWeight,norm_div] at h
  linarith only [h]

/-- The exact fourth-derivative comparison model at equal ordinates. -/
def realPoissonModel (x : ℝ) : ℝ := 4/(4-x^2)

def realPoissonMixed (a b : ℝ) : ℝ :=
  (realPoissonModel (a+b)+realPoissonModel (a-b))/2-realPoissonModel a-realPoissonModel b+1

/-- Sharp upper bound for the real comparison model on both full displacement intervals.
The algebraic certificate is a sum of six nonnegative terms in 1−4a² and 1−4b². -/
theorem realPoissonMixed_le_eight_fifteenths (a b : ℝ) (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    realPoissonMixed a b ≤ (8/15)*a^2*b^2 := by
  let A := a^2
  let B := b^2
  let U := 1-4*A
  let V := 1-4*B
  let N := (A-B)^2-12*(A+B)+96
  let D := (4-a^2)*(4-b^2)*(4-(a+b)^2)*(4-(a-b)^2)
  have ha2 : a^2 ≤ (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 ha
  have hb2 : b^2 ≤ (1/2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) (by norm_num)).2 hb
  have hU : 0 ≤ U := by dsimp only [U,A]; linarith only [ha2]
  have hV : 0 ≤ V := by dsimp only [V,B]; linarith only [hb2]
  have hpab : |a+b| ≤ 1 := (abs_add_le _ _).trans (by linarith)
  have hmab : |a-b| ≤ 1 := (abs_sub _ _).trans (by linarith)
  have hzp {t : ℝ} (ht : |t| ≤ 1) : 0 < 4-t^2 := by
    have hsq : t^2 ≤ (1:ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) zero_le_one).2 ht
    linarith only [hsq]
  have hda := hzp (ha.trans (by norm_num))
  have hdb := hzp (hb.trans (by norm_num))
  have hdp := hzp hpab
  have hdm := hzp hmab
  have hD : 0 < D := by dsimp only [D]; positivity
  have hiden : 32*(8*D-15*N) = U*V*(U-V)^2 + 15*(U^3+V^3) + 17*U*V*(U+V) +
      675*(U^2+V^2) + 762*U*V + 8640*(U+V) := by
    dsimp only [D,N,U,V,A,B]
    ring
  have hpos : 0 ≤ U*V*(U-V)^2 + 15*(U^3+V^3) + 17*U*V*(U+V) +
      675*(U^2+V^2) + 762*U*V + 8640*(U+V) := by positivity
  have hrat : N/D ≤ (8/15:ℝ) := (div_le_iff₀ hD).2 (by linarith only [hiden,hpos])
  have hid : realPoissonMixed a b = a^2*b^2*(N/D) := by
    dsimp only [realPoissonMixed,realPoissonModel,N,D,A,B]
    field_simp [hda.ne',hdb.ne',hdp.ne',hdm.ne']
    ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hrat (mul_nonneg (sq_nonneg a) (sq_nonneg b))).trans_eq
    (by ring)

end RiemannResearch.Analysis.MontgomeryCentralDifference

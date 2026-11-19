import RiemannResearch.Analysis.MontgomeryReflectedKernelOptimal

/-! # The optimal affine correction to the near-axis reflected pair bound -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryCentralDifference
open MontgomeryPoisson

/-- A Bernstein polynomial certificate for the near-axis majorant, with exact
intercept and equality at maximal displacements. -/
theorem realPoissonMixed_le_affine (a b : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    realPoissonMixed a b ≤ (3/8+(19/60)*(a^2+b^2))*a^2*b^2 := by
  let A := a^2
  let B := b^2
  let U := 1-4*A
  let V := 1-4*B
  let X := 4*A
  let Y := 4*B
  let N := (A-B)^2-12*(A+B)+96
  let D := (4-a^2)*(4-b^2)*(4-(a+b)^2)*(4-(a-b)^2)
  have ha2 : a^2 ≤ (1 / 2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 ha
  have hb2 : b^2 ≤ (1 / 2 : ℝ)^2 := by
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
  have hX : 0 ≤ X := by dsimp only [X,A]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y,B]; positivity
  let E : ℝ := 323584*(U^4*Y*V^3+X*U^3*V^4) +
    802560*(U^4*Y^2*V^2+X^2*U^2*V^4) +
    647520*(U^4*Y^3*V+X^3*U*V^4) +
    168240*(U^4*Y^4+X^4*V^4) +
    2198528*X*U^3*Y*V^3 +
    4009056*(X*U^3*Y^2*V^2+X^2*U^2*Y*V^3) +
    2768954*(X*U^3*Y^3*V+X^3*U*Y*V^3) +
    633645*(X*U^3*Y^4+X^4*Y*V^3) +
    6285100*X^2*U^2*Y^2*V^2 +
    3830611*(X^2*U^2*Y^3*V+X^3*U*Y^2*V^2) +
    750240*(X^2*U^2*Y^4+X^4*Y^2*V^2) +
    1995456*X^3*U*Y^3*V +
    285120*(X^3*U*Y^4+X^4*Y^3*V)
  have hiden : 61440*((3/8+(19/60)*(A+B))*D-N) = E := by
    dsimp only [E,D,N,U,V,X,Y,A,B]
    ring
  have hpos : 0 ≤ E := by dsimp only [E]; positivity
  have hrat : N/D ≤ 3/8+(19/60)*(A+B) :=
    (div_le_iff₀ hD).2 (by linarith only [hiden,hpos])
  have hid : realPoissonMixed a b = a^2*b^2*(N/D) := by
    dsimp only [realPoissonMixed,realPoissonModel,N,D,A,B]
    field_simp [hda.ne',hdb.ne',hdp.ne',hdm.ne']
    ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hrat (mul_nonneg (sq_nonneg a) (sq_nonneg b))).trans_eq
    (by dsimp only [A,B]; ring)

/-- Exact worst-pair coefficient in each strictly positive symmetric displacement band.
The expression at radius zero denotes its continuous extension. -/
theorem realPoissonMixed_le_radius (a b r : ℝ) (ha : |a| ≤ r) (hb : |b| ≤ r)
    (hr : r ≤ 1 / 2) : realPoissonMixed a b ≤ 3/(2*(4-r^2)*(1-r^2))*a^2*b^2 := by
  let A := a^2
  let B := b^2
  let R := r^2
  let U := R-A
  let V := R-B
  let N := (A-B)^2-12*(A+B)+96
  let D := (4-a^2)*(4-b^2)*(4-(a+b)^2)*(4-(a-b)^2)
  have hr0 := (abs_nonneg a).trans ha
  have hR0 : 0 ≤ R := sq_nonneg _
  have hR1 : R ≤ (1 / 2:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).2 hr
  have hU : 0 ≤ U := sub_nonneg.mpr (by
    simpa only [A,R,sq_abs] using (sq_le_sq₀ (abs_nonneg a) hr0).2 ha)
  have hV : 0 ≤ V := sub_nonneg.mpr (by
    simpa only [B,R,sq_abs] using (sq_le_sq₀ (abs_nonneg b) hr0).2 hb)
  have h4 : 0 < 4-R := by linarith only [hR1]
  have h1 : 0 < 1-R := by linarith only [hR1]
  have h34 : 0 < 34-R := by linarith only [hR1]
  have h5 : 0 < 5-2*R := by linarith only [hR1]
  have h80 : 0 < 80-34*R-R^2 := by
    have hsq : R^2 ≤ ((1 / 2:ℝ)^2)^2 := (sq_le_sq₀ hR0 (by norm_num)).2 hR1
    linarith only [hR1,hsq]
  have hzp {t : ℝ} (ht : |t| ≤ 1) : 0 < 4-t^2 := by
    have hsq : t^2 ≤ (1:ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) zero_le_one).2 ht
    linarith only [hsq]
  have hda := hzp (ha.trans (hr.trans (by norm_num)))
  have hdb := hzp (hb.trans (hr.trans (by norm_num)))
  have hdp := hzp ((abs_add_le a b).trans (by linarith))
  have hdm := hzp ((abs_sub a b).trans (by linarith))
  have hD : 0 < D := by dsimp only [D]; positivity
  let E := 3*U*V*(U-V)^2 + 3*(4-R)*(U^3+V^3) + 3*(R+4)*U*V*(U+V) +
    (34-R)*(4-R)*(U^2+V^2) + 2*(80-34*R-R^2)*U*V + 24*(4-R)*(5-2*R)*(U+V)
  have heq : 3*D-2*(4-R)*(1-R)*N = E := by
    dsimp only [D,N,E,U,V,R,A,B]
    ring
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hrr : 0 < 2*(4-R)*(1-R) := by positivity
  have hrat : N/D ≤ 3/(2*(4-R)*(1-R)) :=
    (div_le_div_iff₀ hD hrr).2 (by linarith only [heq,hE])
  have hid : realPoissonMixed a b = a^2*b^2*(N/D) := by
    dsimp only [realPoissonMixed,realPoissonModel,N,D,A,B]
    field_simp [hda.ne',hdb.ne',hdp.ne',hdm.ne']
    ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hrat (mul_nonneg (sq_nonneg a) (sq_nonneg b))).trans_eq
    (by dsimp only [R]; ring)

/-- The equal-displacement endpoint attains that radius-specific result. -/
theorem realPoissonMixed_diag {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    realPoissonMixed r r = 3/(2*(4-r^2)*(1-r^2))*r^2*r^2 := by
  have hsq := (sq_le_sq₀ hr0 (by norm_num : 0 ≤ (1 / 2:ℝ))).2 hr
  have h4 : 4-r^2 ≠ 0 := by linarith only [hsq]
  have h1 : 1-r^2 ≠ 0 := by linarith only [hsq]
  have h2 : 4-(r+r)^2 ≠ 0 := by nlinarith only [hsq]
  unfold realPoissonMixed realPoissonModel
  have h3 : 4-r^2*4 ≠ 0 := by linarith only [hsq]
  have h3' : 4-4*r^2 ≠ 0 := by linarith only [hsq]
  simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero]
  field_simp [h4,h1,h2,h3,h3'] <;> ring_nf <;> field_simp [h3,h3'] <;> ring

/-- The optimal constant for every symmetric displacement band. -/
theorem reflectedPairKernel_norm_le_radius (u a b d r : ℝ)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hr : r ≤ 1 / 2) :
    ‖reflectedPairKernel u a b d‖ ≤ 3/(2*(4-r^2)*(1-r^2))*
      (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*a^2*b^2*cauchyWeight d := by
  apply (reflectedPairKernel_norm_le_comparison_model poissonJet_norm_le_real_fourth
    u a b d (ha.trans hr) (hb.trans hr)).trans
  have hw : 0 ≤ cauchyWeight d := by unfold cauchyWeight; positivity
  exact (mul_le_mul_of_nonneg_left (realPoissonMixed_le_radius a b r ha hb hr)
    (by positivity : 0 ≤ (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*cauchyWeight d)).trans_eq
    (by ring)

/-- Sharp squared-displacement correction to the limiting coefficient 3/8. -/
theorem reflectedPairKernel_norm_le_affine (u a b d : ℝ)
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    ‖reflectedPairKernel u a b d‖ ≤ (3/8+(19/60)*(a^2+b^2))*
      (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*a^2*b^2*cauchyWeight d := by
  apply (reflectedPairKernel_norm_le_comparison_model poissonJet_norm_le_real_fourth
    u a b d ha hb).trans
  have hw : 0 ≤ cauchyWeight d := by unfold cauchyWeight; positivity
  exact (mul_le_mul_of_nonneg_left (realPoissonMixed_le_affine a b ha hb)
    (by positivity : 0 ≤ (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*cauchyWeight d)).trans_eq
    (by ring)

/-- Any global affine majorant with intercept 3/8 needs slope at least 19/60. -/
theorem reflectedPairKernel_affine_slope_lower {K : ℝ}
    (h : ∀ u a b d : ℝ, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 →
      ‖reflectedPairKernel u a b d‖ ≤ (3/8+K*(a^2+b^2))*
        (1+|u|)^4*Real.exp (|u| * (|a| + |b|))*a^2*b^2*cauchyWeight d) :
    (19/60:ℝ) ≤ K := by
  have hh := h 0 (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num)
  rw [reflectedPairKernel_zero_half_half] at hh
  norm_num [cauchyWeight,norm_div] at hh
  linarith only [hh]

end RiemannResearch.Analysis.MontgomeryCentralDifference

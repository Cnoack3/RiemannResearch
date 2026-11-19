/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryReflectedPoissonJets
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # A common real fourth-derivative majorant for the complex Poisson jets -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryCentralDifference
open MontgomeryPoisson

private theorem near_pole {r A D : ℝ} (hr : 0<r) (hr2 : r≤2) (hA : r≤A)
    (hD : 0≤D) (ha : A^2=r^2+D) (q : ℕ) :
    (4+D)/A^(q+2) ≤ 4/r^(q+2) := by
  have hA0 := hr.trans_le hA
  apply (div_le_div_iff₀ (pow_pos hA0 _) (pow_pos hr _)).mpr
  have hrSq : r^2 ≤ 4 := by
    have hh := pow_le_pow_left₀ hr.le hr2 2
    norm_num at hh
    exact hh
  have h1 : (4+D)*r^2 ≤ 4*A^2 := by
    nlinarith only [ha,mul_nonneg hD (sub_nonneg.mpr hrSq)]
  have h2 := mul_le_mul h1 (pow_le_pow_left₀ hr.le hA q) (pow_nonneg hr.le _) (by positivity)
  rw [pow_add,pow_add]
  calc
    _ = ((4+D)*r^2)*r^q := by ring
    _ ≤ (4*A^2)*A^q := h2
    _ = _ := by ring

private theorem far_pole {s B D : ℝ} (hs : 2≤s) (hB : s≤B)
    (hb : B^2=s^2+D) (hD : 0≤D) (q : ℕ) :
    (4+D)/B^(q+2) ≤ 1/s^q := by
  have hs0 : 0<s := (by norm_num : (0:ℝ)<2).trans_le hs
  have hB0 := hs0.trans_le hB
  apply (div_le_div_iff₀ (pow_pos hB0 _) (pow_pos hs0 _)).mpr
  have hsSq : 4 ≤ s^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hs 2
    norm_num at hh
    exact hh
  have h1 : 4+D ≤ B^2 := by linarith only [hb,hsSq]
  have h2 := mul_le_mul h1 (pow_le_pow_left₀ hs0.le hB q) (pow_nonneg hs0.le _) (sq_nonneg _)
  simpa only [pow_add,one_mul,mul_comm (B^q)] using h2

private theorem intermediate_pole_pair {r s A B D : ℝ} (hr : 0<r) (hr2 : r≤2)
    (hs : 2≤s) (hA : r≤A) (hB : s≤B) (hD : 0≤D)
    (ha : A^2=r^2+D) (hb : B^2=s^2+D) (q : ℕ) (hq : q≤2) :
    (4+D)*(((q+1).factorial:ℝ)/A^(q+2)+((q+1).factorial:ℝ)/B^(q+2)) ≤
      4*24*(1/r^5+1/s^5) := by
  let f : ℝ := (q+1).factorial
  have hf : 0≤f := Nat.cast_nonneg _
  have hs0 : 0<s := (by norm_num : (0:ℝ)<2).trans_le hs
  have hne := mul_le_mul_of_nonneg_left (near_pole hr hr2 hA hD ha q) hf
  have hfa := mul_le_mul_of_nonneg_left (far_pole hs hB hb hD q) hf
  have hnear : f*(4/r^(q+2)) ≤ 48/r^5 := by
    have he : f*(4/r^(q+2)) = (f*4*r^(3-q))/r^5 := by
      interval_cases q <;> norm_num <;> field_simp [hr.ne'] <;> ring
    rw [he]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le _)
    have h3 := pow_le_pow_left₀ hr.le hr2 3
    have h2 := pow_le_pow_left₀ hr.le hr2 2
    dsimp only [f]
    interval_cases q <;> norm_num [Nat.factorial] at h2 h3 ⊢ <;> linarith only [h2,h3,hr2]
  have hfar : f*(1/s^q) ≤ 48/r^5 := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hs0 _) (pow_pos hr _)).mpr
    have hr5 := pow_le_pow_left₀ hr.le hr2 5
    have hs2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hs 2
    dsimp only [f]
    interval_cases q <;> norm_num [Nat.factorial] at hr5 hs2 ⊢ <;> linarith only [hr5,hs2,hs]
  have hsum := add_le_add (hne.trans hnear) (hfa.trans hfar)
  calc
    _ = f*((4+D)/A^(q+2))+f*((4+D)/B^(q+2)) := by dsimp only [f]; ring
    _ ≤ 48/r^5+48/r^5 := hsum
    _ = (4*24)*(1/r^5) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by norm_num)

private theorem fourth_single_pole {r A D : ℝ} (hr : 0<r) (hr3 : r≤3)
    (hA : r≤A) (hD : 0≤D) (hAsq : A^2=r^2+D) :
    (4+D)/A^5 ≤ 4/r^5 := by
  have hA0 := hr.trans_le hA
  apply (div_le_div_iff₀ (pow_pos hA0 _) (pow_pos hr _)).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hr2 : r^2 ≤ 9 := by
    have hh := pow_le_pow_left₀ hr.le hr3 2
    norm_num at hh
    exact hh
  have hr4 : r^4 ≤ 81 := by
    have hh := pow_le_pow_left₀ hr.le hr3 4
    norm_num at hh
    exact hh
  have h10 : 0≤10-r^2 := by linarith only [hr2]
  have h160 : 0≤160-r^4 := by linarith only [hr4]
  have hid : 16*(r^2+D)^5-((4+D)*r^5)^2 =
      D*(8*r^8*(10-r^2)+D*r^6*(160-r^4)+160*r^4*D^2+80*r^2*D^3+16*D^4) := by ring
  have hpos : 0≤D*(8*r^8*(10-r^2)+D*r^6*(160-r^4)+160*r^4*D^2+80*r^2*D^3+16*D^4) := by positivity
  have hA5 : (4*A^5)^2=16*(r^2+D)^5 := by rw [← hAsq]; ring
  linarith only [hid,hpos,hA5]

private theorem real_fourth_jet (x : ℝ) : poissonJet (0:ℝ) 4 x =
    24*(1/(2-x)^5+1/(2+x)^5) := by
  norm_num [poissonJet,poleJet, Nat.factorial,inv_pow,one_div]
  ring

private theorem real_fourth_ge_three_halves {x : ℝ} (hx : |x|≤1) :
    3/2 ≤ poissonJet (0:ℝ) 4 x := by
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx
  have hr : 0<2-x := by linarith
  have hs : 0<2+x := by linarith
  have hprod : (2-x)*(2+x) ≤ 4 := by nlinarith only [sq_nonneg x]
  have hp : (2-x)^5*(2+x)^5 ≤ 4^5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hr.le hs.le) hprod _
  have hsum : 64 ≤ (2-x)^5+(2+x)^5 := by
    have hid : (2-x)^5+(2+x)^5=64+160*x^2+20*x^4 := by ring
    nlinarith only [hid,sq_nonneg x,pow_nonneg (sq_nonneg x) 2]
  rw [real_fourth_jet]
  field_simp [hr.ne',hs.ne']
  nlinarith only [hp,hsum]

/-- The complex Poisson derivatives through order four share the same
positive real fourth-derivative majorant with the exact Cauchy weight. -/
theorem poissonJet_norm_le_real_fourth (d x : ℝ) (hx : |x|≤1) (k : ℕ) (hk : k≤4) :
    ‖poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤ cauchyWeight d*poissonJet (0:ℝ) 4 x := by
  let Z := (x:ℂ)+Complex.I*(d:ℂ)
  let A := ‖2-Z‖
  let B := ‖2+Z‖
  let D := d^2
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx
  have hr : 0<2-x := by linarith
  have hs : 0<2+x := by linarith
  have hA : 2-x≤A := by simpa [A,Z] using Complex.re_le_norm (2-Z)
  have hB : 2+x≤B := by simpa [B,Z] using Complex.re_le_norm (2+Z)
  have hA0 := hr.trans_le hA
  have hB0 := hs.trans_le hB
  have hD : 0≤D := sq_nonneg d
  have ha : A^2=(2-x)^2+D := by
    dsimp only [A,D]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Z,pow_two]
    <;> ring
  have hb : B^2=(2+x)^2+D := by
    dsimp only [B,D]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Z,pow_two]
    <;> ring
  have hw : 0 < cauchyWeight d := by unfold cauchyWeight; positivity
  by_cases hk0 : k=0
  · subst k
    have hm : 2-Z≠0 := norm_pos_iff.mp hA0
    have hp : 2+Z≠0 := norm_pos_iff.mp hB0
    rw [poissonJet_zero_apply hm hp, norm_div, show ‖(4:ℂ)‖=4 by norm_num]
    have hden : 4-x^2+D ≤ ‖(4-Z^2:ℂ)‖ := by
      have he : (4-Z^2:ℂ).re=4-x^2+D := by simp [Z,D,pow_two]; ring
      exact he.symm.trans_le (Complex.re_le_norm _)
    have hx2 : x^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg x) hx 2
    have hnn : 0<4-x^2+D := by linarith only [hx2,hD]
    apply (div_le_div_of_nonneg_left (by norm_num) hnn hden).trans
    apply le_trans _ (mul_le_mul_of_nonneg_left (real_fourth_ge_three_halves hx) hw.le)
    change 4/(4-x^2+D) ≤ (4/(4+D))*(3/2)
    rw [show 4/(4+D)*(3/2) = 6/(4+D) by ring]
    exact (div_le_div_iff₀ hnn (by positivity)).mpr (by linarith only [hx2,hD])
  · have hsum : ‖poissonJet (Complex.I*(d:ℂ)) k (x:ℂ)‖ ≤
        (k.factorial:ℝ)/A^(k+1)+(k.factorial:ℝ)/B^(k+1) := by
      apply (norm_add_le _ _).trans_eq
      simp [poleJet,A,B,Z,div_eq_mul_inv]
      left
      congr 1
      ring
    apply hsum.trans
    rw [real_fourth_jet]
    change _ ≤ (4/(4+D))*(24*(1/(2-x)^5+1/(2+x)^5))
    rw [show (4/(4+D))*(24*(1/(2-x)^5+1/(2+x)^5)) =
      (4*24*(1/(2-x)^5+1/(2+x)^5))/(4+D) by ring]
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    by_cases hk4 : k=4
    · subst k
      have hn := fourth_single_pole hr (by linarith only [hxl]) hA hD ha
      have hf := fourth_single_pole hs (by linarith only [hxr]) hB hD hb
      norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.reduceMul, Nat.reduceAdd]
      convert mul_le_mul_of_nonneg_left (add_le_add hn hf) (by norm_num : (0:ℝ)≤24) using 1 <;> ring
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hq : q≤2 := by omega
      by_cases hpos : 0≤x
      · exact intermediate_pole_pair hr (by linarith) (by linarith) hA hB hD ha hb q hq
      · have hh := intermediate_pole_pair hs (by linarith) (by linarith) hB hA hD hb ha q hq
        simpa only [add_comm] using hh

end RiemannResearch.Analysis.MontgomeryCentralDifference

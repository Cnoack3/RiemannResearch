/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoResidueMoments
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# Actual digamma formula for Pareto progression weights

Source: user-provided discussion of weighted CRT on 11 September 2026.
The partial-fraction identity is the standard digamma identity recorded at
https://dlmf.nist.gov/5.9#E16; its provider here is the proved actual complex
digamma series in `Zeta23.DigammaSeries`, via `ParetoResidueMoments`.
The positive residue convention is `1 ≤ r ≤ Q`, with `r = Q` the zero class.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem positive_unit_interval_mem_integerComplement {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) : (a : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hn' : (n : ℝ) = a := by
    simpa only [Complex.intCast_re, Complex.ofReal_re] using congrArg Complex.re hn
  have hlow : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hhigh : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

private theorem hasSum_reciprocal_difference_off_integer {a : ℝ}
    (hz : ((a - 1 : ℝ) : ℂ) ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1))
      (-(Complex.digamma (a : ℂ)).re - Real.eulerMascheroniConstant) := by
  have hneg : ∀ m : ℕ, ((a - 1 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    exact hz ⟨-(m : ℤ), by
      push_cast
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hm.symm⟩
  have hd := Complex.digamma_apply_add_one ((a - 1 : ℝ) : ℂ) hneg
  have hsum := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have he : ((a - 1 : ℝ) : ℂ) + 1 = (a : ℂ) := by push_cast; ring
  rw [he] at hd
  have hrhs : Complex.digamma ((a - 1 : ℝ) : ℂ) +
      (Real.eulerMascheroniConstant : ℂ) + 1 / ((a - 1 : ℝ) : ℂ) =
        Complex.digamma (a : ℂ) + (Real.eulerMascheroniConstant : ℂ) := by
    rw [hd]
    ring
  rw [hrhs] at hsum
  have hc : HasSum (fun n : ℕ =>
      (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + a) : ℝ))
      ((Complex.digamma (a : ℂ)).re + Real.eulerMascheroniConstant) := by
    have h := Complex.hasSum_re hsum
    convert h using 1 <;> try rfl
    · ext n
      have he' : ((a - 1 : ℝ) : ℂ) + (n : ℂ) + 1 =
          (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
      rw [he']
      have he'' : ((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + a) : ℝ) : ℂ) =
          1 / ((n : ℂ) + 1) - 1 / (((n : ℝ) + a : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [← he'', Complex.ofReal_re]
  have h := hc.neg
  convert h using 1 <;> try rfl
  · ext n; ring
  · ring

/-- The actual reciprocal-difference series, including the regular integer `1`. -/
theorem hasSum_reciprocal_difference_lt_two {a : ℝ} (ha0 : 0 < a) (ha2 : a < 2) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1))
      (-(Complex.digamma (a : ℂ)).re - Real.eulerMascheroniConstant) := by
  rcases lt_trichotomy a 1 with ha1 | ha1 | ha1
  · exact hasSum_reciprocal_difference ha0 ha1
  · subst a
    simpa [Complex.digamma_one] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  · exact hasSum_reciprocal_difference_off_integer
      (positive_unit_interval_mem_integerComplement (by linarith) (by linarith))

/-- Digamma recurrence on the positive real axis. -/
theorem re_digamma_add_one {x : ℝ} (hx : 0 < x) :
    (Complex.digamma ((x + 1 : ℝ) : ℂ)).re =
      (Complex.digamma (x : ℂ)).re + 1 / x := by
  have hneg : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hm' := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hm'
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := congrArg Complex.re (Complex.digamma_apply_add_one (x : ℂ) hneg)
  have hinv : ((x : ℂ)⁻¹).re = x⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.add_re,
    hinv, one_div] using h

private theorem hasSum_shifted_reciprocal_telescope {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + x + 1)) (1 / x) := by
  have hpos (n : ℕ) : 0 ≤ 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + x + 1) := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  apply (hasSum_iff_tendsto_nat_of_nonneg hpos (1 / x)).mpr
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + x + 1))) =
        1 / x - 1 / ((N : ℝ) + x) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_zero,
      add_assoc, add_left_comm, add_comm] using
      Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + x)) N
  simp_rw [he]
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + x) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + x)) atTop (𝓝 0) := by
    convert htop.inv_tendsto_atTop using 1 <;> try rfl
    funext n
    simp only [one_div, Pi.inv_apply]
  simpa only [sub_zero] using tendsto_const_nhds.sub hinv

/-- The standard actual digamma series throughout the positive real axis. -/
theorem hasSum_reciprocal_difference_positive {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1))
      (-(Complex.digamma (x : ℂ)).re - Real.eulerMascheroniConstant) := by
  have aux : ∀ N : ℕ, ∀ x : ℝ, 0 < x → x < (N : ℝ) →
      HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1))
        (-(Complex.digamma (x : ℂ)).re - Real.eulerMascheroniConstant) := by
    intro N
    induction N with
    | zero =>
      intro x hx hxN
      norm_num at hxN
      linarith
    | succ N ih =>
      intro x hx hxN
      by_cases hx2 : x < 2
      · exact hasSum_reciprocal_difference_lt_two hx hx2
      have hx1 : 0 < x - 1 := by linarith
      have hxN' : x - 1 < (N : ℝ) := by
        norm_num only [Nat.cast_succ] at hxN
        linarith
      have hs := (ih (x - 1) hx1 hxN').sub (hasSum_shifted_reciprocal_telescope hx1)
      have hd := re_digamma_add_one hx1
      have he : x - 1 + 1 = x := by ring
      rw [he] at hd
      have hfun (n : ℕ) :
          (1 / ((n : ℝ) + (x - 1)) - 1 / ((n : ℝ) + 1)) -
          (1 / ((n : ℝ) + (x - 1)) - 1 / ((n : ℝ) + (x - 1) + 1)) =
          1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1) := by
        have hen : (n : ℝ) + (x - 1) + 1 = (n : ℝ) + x := by ring
        rw [hen]
        ring
      convert hs using 1 <;> try rfl
      · ext n
        exact (hfun n).symm
      · linarith
  obtain ⟨N, hN⟩ := exists_nat_gt x
  exact aux N x hx hN

/-- The actual digamma is strictly increasing throughout the positive axis. -/
theorem strictMonoOn_re_digamma :
    StrictMonoOn (fun x : ℝ => (Complex.digamma (x : ℂ)).re) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hs := (hasSum_reciprocal_difference_positive hx).sub
    (hasSum_reciprocal_difference_positive hy)
  have hd (n : ℕ) : 0 <
      (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1)) -
      (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + 1)) := by
    have h := one_div_lt_one_div_of_lt
      (show 0 < (n : ℝ) + x by positivity)
      (show (n : ℝ) + x < (n : ℝ) + y by linarith)
    linarith
  have hbound := hs.summable.sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => (hd n).le)
  simp only [Finset.sum_singleton, hs.tsum_eq] at hbound
  have h0 := hd 0
  linarith

/-- Exact closed form for every positive residue, including the zero class. -/
theorem progressionWeight_eq_digamma (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionWeight Q r = 1 / (Q : ℝ) *
      ((Complex.digamma (((r + 1 : ℝ) / Q : ℝ) : ℂ)).re -
       (Complex.digamma (((r : ℝ) / Q : ℝ) : ℂ)).re) := by
  by_cases hQ1 : Q = 1
  · subst Q
    have hr1 : r = 1 := by omega
    subst r
    have hw := progressionWeight_normalization 1 (by norm_num)
    have hd := re_digamma_add_one (x := 1) (by norm_num)
    norm_num at hw hd ⊢
    linarith
  have hQ2 : 2 ≤ Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  have hQ2R : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have ha0 : 0 < (r : ℝ) / Q := div_pos hrR hQr
  have ha2 : (r : ℝ) / Q < 2 := (div_lt_iff₀ hQr).mpr (by linarith)
  have hb0 : 0 < ((r : ℝ) + 1) / Q := by positivity
  have hb2 : ((r : ℝ) + 1) / Q < 2 := (div_lt_iff₀ hQr).mpr (by linarith)
  have hs := ((hasSum_reciprocal_difference_lt_two ha0 ha2).sub
    (hasSum_reciprocal_difference_lt_two hb0 hb2)).mul_left (1 / (Q : ℝ))
  have he (n : ℕ) : (1 / (Q : ℝ)) *
      ((1 / ((n : ℝ) + (r : ℝ) / Q) - 1 / ((n : ℝ) + 1)) -
        (1 / ((n : ℝ) + ((r : ℝ) + 1) / Q) - 1 / ((n : ℝ) + 1))) =
      positiveWeight (r + Q * n) := by
    have h1 : (n : ℝ) + (r : ℝ) / Q ≠ 0 := by positivity
    have h2 : (n : ℝ) + ((r : ℝ) + 1) / Q ≠ 0 := by positivity
    have h3 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (r : ℝ) + (Q : ℝ) * n ≠ 0 := by positivity
    have h5 : (r : ℝ) + (Q : ℝ) * n + 1 ≠ 0 := by positivity
    simp only [positiveWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp
    <;> ring
  have hs' : HasSum (fun n : ℕ => positiveWeight (r + Q * n))
      (1 / (Q : ℝ) *
        ((Complex.digamma (((r + 1 : ℝ) / Q : ℝ) : ℂ)).re -
         (Complex.digamma (((r : ℝ) / Q : ℝ) : ℂ)).re)) := by
    convert hs using 1 <;> try rfl
    · ext n
      exact (he n).symm
    · ring
  exact hs'.tsum_eq

/-- Removing the digamma pole leaves the first Pareto atom exactly intact. -/
theorem progressionWeight_eq_head_digamma (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionWeight Q r = positiveWeight r + 1 / (Q : ℝ) *
      ((Complex.digamma ((1 + ((r : ℝ) + 1) / Q : ℝ) : ℂ)).re -
       (Complex.digamma ((1 + (r : ℝ) / Q : ℝ) : ℂ)).re) := by
  rw [progressionWeight_eq_digamma Q r hQ hr hrQ]
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ha := re_digamma_add_one (div_pos hrR hQr)
  have hb := re_digamma_add_one (x := ((r : ℝ) + 1) / Q) (by positivity)
  rw [add_comm ((r : ℝ) / Q) 1] at ha
  rw [add_comm (((r : ℝ) + 1) / Q) 1] at hb
  rw [ha, hb]
  unfold positiveWeight
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Strict Jensen inequality for the actual digamma on the whole positive
axis. In particular the digamma is concave, not convex. -/
theorem re_digamma_strict_jensen {x y a b : ℝ}
    (hx0 : 0 < x) (hy0 : 0 < y)
    (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * (Complex.digamma (x : ℂ)).re + b * (Complex.digamma (y : ℂ)).re <
      (Complex.digamma ((a * x + b * y : ℝ) : ℂ)).re := by
  let z := a * x + b * y
  have hz0 : 0 < z := by dsimp [z]; positivity
  let d : ℕ → ℝ := fun n =>
    a * (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1)) +
    b * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + 1)) -
    (1 / ((n : ℝ) + z) - 1 / ((n : ℝ) + 1))
  have hsum := (((hasSum_reciprocal_difference_positive hx0).mul_left a).add
    ((hasSum_reciprocal_difference_positive hy0).mul_left b)).sub
    (hasSum_reciprocal_difference_positive hz0)
  have hs : HasSum d
      ((Complex.digamma (z : ℂ)).re -
        (a * (Complex.digamma (x : ℂ)).re + b * (Complex.digamma (y : ℂ)).re)) := by
    convert hsum using 1 <;> try rfl
    linear_combination Real.eulerMascheroniConstant * hab
  have hd (n : ℕ) : d n = a * b * (x - y) ^ 2 /
      (((n : ℝ) + x) * ((n : ℝ) + y) * ((n : ℝ) + z)) := by
    have h1 : (n : ℝ) + x ≠ 0 := by positivity
    have h2 : (n : ℝ) + y ≠ 0 := by positivity
    have h3 : (n : ℝ) + z ≠ 0 := by positivity
    have h4 : (n : ℝ) + 1 ≠ 0 := by positivity
    have ha' : a = 1 - b := by linarith
    dsimp only [d, z]
    rw [ha']
    have h3' : (n : ℝ) + ((1 - b) * x + b * y) ≠ 0 := by
      simpa only [z, ha'] using h3
    field_simp
    <;> ring
  have hdpos (n : ℕ) : 0 < d n := by
    rw [hd]
    exact div_pos (mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)))
      (by positivity)
  have hbound := hs.summable.sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => (hdpos n).le)
  simp only [Finset.sum_singleton, hs.tsum_eq] at hbound
  have h0 := hdpos 0
  dsimp only [z] at hbound
  linarith

/-- The actual digamma is strictly concave throughout the positive real axis. -/
theorem strictConcaveOn_re_digamma :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => (Complex.digamma (x : ℂ)).re) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simpa only [smul_eq_mul] using
    re_digamma_strict_jensen hx hy hxy ha hb hab

end
end RiemannResearch.RH.Pareto

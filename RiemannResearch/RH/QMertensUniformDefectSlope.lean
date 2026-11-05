/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFirstMomentEnvelope
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensAllLogPowers
import RiemannResearch.RH.MertensLeeLeongCriterion

/-!
# Uniform logarithmic slopes for Möbius defects

The ordinary Mertens estimate with every fixed logarithmic exponent controls
the canonical Möbius defect divided by the site, uniformly over every site.
We use the finite envelope on the window through the square of the head
and the elementary complete defect bound past that window. Walfisz's classical
bound, recorded in equation (2) of Gerhold, Acta Arith. 142 (2010), is
stronger than the all-log input. The all-log proof uses the internal provider.
The explicit VK specialization below uses Theorem 1.1 of Lee and Leong,
arXiv:2208.06141v5, as the separate proposition named in its type.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert QAnnihilatorTailEscape
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The elementary complete physical bound for the canonical exact-head defect. -/
theorem abs_defect_le_three_mul (N n : ℕ) (hN : 0 < N) :
    |qSequence (defect N) n| ≤ 3 * (N : ℝ) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simpa using (show (0 : ℝ) ≤ 3 * (N : ℝ) by positivity)
  have hd : qSequence (defect N) n = 1 - Pareto.canonicalMobiusHead N n := by
    change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) n = _
    rw [map_sub]
    change qSequence qOne n - qSequence (QMobiusExactHead.exactHead N) n = _
    rw [QMobiusExactHead.exactHead_sequence]
    simp [qOneSequence, hn.ne']
  rw [hd]
  have ht : |1 - Pareto.canonicalMobiusHead N n| ≤ 1 + |Pareto.canonicalMobiusHead N n| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_one] using
      abs_add_le (1 : ℝ) (-Pareto.canonicalMobiusHead N n)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith [Pareto.canonicalMobiusHead_abs_le_two_mul N hN n]

private theorem eventually_four_shifted_log_pow_le_nat (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, 4 * (6 + Real.log (N : ℝ)) ^ k ≤ (N : ℝ) := by
  have ht : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  have hnr : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : 1 ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hx : Tendsto (fun N : ℕ => Real.exp 6 * (N : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)) hnr
  have hlim := (ht.comp hx).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * Real.exp 6) by positivity))
  filter_upwards [hlim, eventually_ge_atTop (1 : ℕ)] with N h hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  change Real.log (Real.exp 6 * (N : ℝ)) ^ k / (Real.exp 6 * (N : ℝ)) <
    1 / (4 * Real.exp 6) at h
  rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp] at h
  have hh := ((div_lt_iff₀ (mul_pos (Real.exp_pos _) hN0)).mp h).le
  calc
    4 * (6 + Real.log (N : ℝ)) ^ k ≤ 4 * (1 / (4 * Real.exp 6) * (Real.exp 6 * (N : ℝ))) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by field_simp <;> ring

/-- Every fixed logarithmic saving holds for the slope of the complete defect,
unconditionally and uniformly in the physical site. -/
theorem eventually_abs_defect_le_div_shifted_log_pow (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |qSequence (defect N) n| ≤
      (n : ℝ) / (6 + Real.log (N : ℝ)) ^ k := by
  let j := k + 2
  obtain ⟨B, _, hM⟩ := M_shiftedLog_all_nat_powers (j + 1)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_four_shifted_log_pow_le_nat k,
    hlog.eventually (eventually_ge_atTop (max B (10 * ((k : ℝ) + 10)))),
    eventually_ge_atTop (1 : ℕ)] with N hnum hlarge hN
  let L := 6 + Real.log (N : ℝ)
  let U := L ^ k
  let ε := 1 / L ^ j
  have hN0 : 0 < N := by omega
  have hNR0 : 0 < (N : ℝ) := by exact_mod_cast hN0
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNR1]
  have hL0 : 0 < L := by linarith
  have hpowone (a : ℕ) : 1 ≤ L ^ a := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL a
  have hU : 1 ≤ U := hpowone k
  have hU0 : 0 < U := by linarith
  have hBL : B ≤ L := by
    dsimp [L]
    linarith [(le_max_left B (10 * ((k : ℝ) + 10))).trans hlarge]
  have hbig : 2 * (4 + 5 * ((j : ℝ) + 1)) ≤ L := by
    dsimp [j, L]
    push_cast
    linarith [(le_max_right B (10 * ((k : ℝ) + 10))).trans hlarge]
  have hnum' : 4 * U ≤ (N : ℝ) := hnum
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := (div_le_iff₀ (pow_pos hL0 _)).mpr (by simpa using hpowone j)
  have hMt (y : ℝ) (hy : (N : ℝ) ≤ y) : |M y| ≤ ε * y := by
    have hLy : L ≤ 6 + Real.log y := by
      dsimp [L]
      linarith [Real.log_le_log hNR0 hy]
    have hp := pow_le_pow_left₀ hL0.le hLy (j + 1)
    have hm : |M y| * L ^ (j + 1) ≤ L * y := calc
      _ ≤ |M y| * (6 + Real.log y) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ B * y := hM y (hNR1.trans hy)
      _ ≤ L * y := mul_le_mul_of_nonneg_right hBL (hNR0.le.trans hy)
    have hm' : (|M y| * L ^ j) * L ≤ y * L := by
      calc
        _ = |M y| * L ^ (j + 1) := by rw [pow_succ]; ring
        _ ≤ L * y := hm
        _ = _ := mul_comm _ _
    have hmy : |M y| ≤ y / L ^ j :=
      (le_div_iff₀ (pow_pos hL0 _)).mpr (by
        by_contra! h
        exact (not_lt_of_ge hm') (mul_lt_mul_of_pos_right h hL0))
    simpa only [ε, div_eq_mul_inv, one_mul, mul_comm] using hmy
  have hinv : 1 / ε = L ^ j := by simp [ε]
  have hent : ε * (1 + Real.log (1 / ε)) ≤ ((j : ℝ) + 1) / (U * L) := by
    rw [hinv, Real.log_pow]
    calc
      _ ≤ ε * (((j : ℝ) + 1) * L) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hL0)
          (Nat.cast_nonneg j : (0 : ℝ) ≤ _)
        nlinarith
      _ = _ := by
        dsimp only [ε, U, j]
        rw [pow_add]
        field_simp [hL0.ne']
        <;> ring
  have hUL : L ≤ U * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hU hL0.le
  have hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2 := by
    apply hent.trans
    apply (div_le_iff₀ (mul_pos hU0 hL0)).mpr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  intro n
  have hd := abs_defect_le_errorEnvelope N n hN0 ε hε hε1 hsmall hMt
  change |qSequence (defect N) n| ≤ (n : ℝ) / U
  by_cases hhead : n ≤ N
  · have hzero : |qSequence (defect N) n| ≤ 0 := by
      simpa only [errorEnvelope, if_pos hhead] using hd
    exact hzero.trans (div_nonneg (Nat.cast_nonneg _) hU0.le)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  by_cases hnear : n ≤ N ^ 2
  · have hnr : (n : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hnear
    have hlogn := Real.log_le_log hn0 hnr
    rw [Real.log_pow] at hlogn
    have hsite : ε * (2 + Real.log (n : ℝ)) ≤ 4 / (U * L) := by
      calc
        _ ≤ ε * (4 * L) := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          dsimp only [L] at hL ⊢
          norm_num at hlogn
          linarith
        _ = _ := by
          dsimp only [ε, U, j]
          rw [pow_add]
          field_simp [hL0.ne']
          <;> ring
    have hmix : ε * (2 + Real.log (n : ℝ)) + 5 * (ε * (1 + Real.log (1 / ε))) ≤ 1 / (2 * U) := by
      calc
        _ ≤ 4 / (U * L) + 5 * (((j : ℝ) + 1) / (U * L)) :=
          add_le_add hsite (mul_le_mul_of_nonneg_left hent (by norm_num))
        _ = (4 + 5 * ((j : ℝ) + 1)) / (U * L) := by ring
        _ ≤ _ := by
          apply (div_le_div_iff₀ (mul_pos hU0 hL0) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hbig hU0.le]
    have htwo : (2 : ℝ) ≤ (n : ℝ) / (2 * U) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    calc
      _ ≤ 2 + (n : ℝ) * (ε * (2 + Real.log (n : ℝ)) + 5 * (ε * (1 + Real.log (1 / ε)))) := by
        rw [errorEnvelope, if_neg hhead] at hd
        exact hd.trans (min_le_right _ _)
      _ ≤ (n : ℝ) / (2 * U) + (n : ℝ) * (1 / (2 * U)) :=
        add_le_add htwo (mul_le_mul_of_nonneg_left hmix hn0.le)
      _ = _ := by field_simp [hU0.ne'] <;> ring
  · have hnr : (N : ℝ) ^ 2 ≤ (n : ℝ) := by
      exact_mod_cast (show N ^ 2 ≤ n by omega)
    apply (abs_defect_le_three_mul N n hN0).trans
    apply (le_div_iff₀ hU0).mpr
    nlinarith [mul_le_mul_of_nonneg_left (show 3 * U ≤ (N : ℝ) by linarith) hNR0.le]

end RiemannResearch.RH.QMertensFirstMoment

/-!
# Uniform physical slopes of the canonical Möbius defect at the VK scale

The analytic input is the ordinary Walfisz bound, in the form of Gerhold
(Acta Arith. 142 (2010), equation (2)). Its constant and rate are explicit
hypotheses. The conclusion holds simultaneously at all physical sites.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert QAnnihilatorTailEscape

private theorem eventually_const_le_mul_exp_neg_vk (a K : ℝ) (ha : 0 < a) :
    ∀ᶠ y : ℝ in atTop, K ≤ y * Real.exp (-a * vkProfile y) := by
  obtain ⟨x, hx⟩ := (vkProfile_eventual_log_increment (1 / (2 * a)) (by positivity)).exists
  filter_upwards [eventually_ge_atTop x, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop
      (2 * (K + a * vkProfile x)-Real.log x))] with y hy hy0 hlog
  have hh := mul_le_mul_of_nonneg_left (hx y hy) ha.le
  have he : a * (1 / (2 * a) * (Real.log y-Real.log x)) =
      (Real.log y-Real.log x) / 2 := by field_simp [ha.ne'] <;> ring
  rw [he] at hh
  have hle : K ≤ Real.log y - a * vkProfile y := by linarith only [hh, hlog]
  calc
    K ≤ Real.log y - a * vkProfile y := hle
    _ ≤ Real.exp (Real.log y - a * vkProfile y) := by
      linarith only [Real.add_one_le_exp (Real.log y - a * vkProfile y)]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hy0, neg_mul]

/-- A finite scale comparison preserving the VK exponent at power-size cutoffs.
The iterated logarithm in the denominator only improves the lower bound. -/
theorem vkProfile_lower_of_log_ratio {x y θ : ℝ} (hx : Real.exp 1 < x) (hxy : x ≤ y)
    (hθ : 0 ≤ θ) (h : θ * Real.log y ≤ Real.log x) :
    θ ^ (3 / 5 : ℝ) * vkProfile y ≤ vkProfile x := by
  have hx0 := (Real.exp_pos 1).trans hx
  have ht : 1 < Real.log x := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hx
  have ht0 : 0 < Real.log x := by linarith
  have htT := Real.log_le_log hx0 hxy
  have hT0 := ht0.trans_le htT
  have hl := Real.log_pos ht
  have hlL := Real.log_le_log ht0 htT
  have hL := hl.trans_le hlL
  have hnum := Real.rpow_le_rpow (mul_nonneg hθ hT0.le) h (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [Real.mul_rpow hθ hT0.le] at hnum
  unfold vkProfile
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hL _) (Real.rpow_pos_of_pos hl _)).mpr
  exact mul_le_mul hnum (Real.rpow_le_rpow hl.le hlL (by norm_num))
    (Real.rpow_nonneg hl.le _) (Real.rpow_nonneg ht0.le _)

/-- One uniform slope for every physical coordinate and every sufficiently
large Möbius cutoff, at every rate strictly below the input Mertens rate. -/
theorem abs_defect_le_vk_cutoff_slope (a c C : ℝ) (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |qSequence (defect N) n| ≤
      (n : ℝ) * Real.exp (-c * vkProfile (N : ℝ)) := by
  let u := (2 * a + c) / 3
  let v := (a + 2 * c) / 3
  have hcv : c < v := by dsimp [v]; linarith
  have hvu : v < u := by dsimp [u, v]; linarith
  have hua : u < a := by dsimp [u]; linarith
  have hv : 0 < v := hc.trans hcv
  have hu : 0 < u := hv.trans hvu
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    (QSquarefreeMertensProfileCriterion.mertens_vk_absorb_constant a u C hua hM)
  obtain ⟨K, hK, henv⟩ := errorEnvelope_eventually_le_vk u v hv hvu
  have hpar := Tendsto.const_mul_atTop hu vkProfile_tendsto_atTop
  have hgap := Real.tendsto_exp_atTop.comp
    (Tendsto.const_mul_atTop (sub_pos.mpr hcv) vkProfile_tendsto_atTop)
  filter_upwards [henv, hnat.eventually vkProfile_eventually_mono,
    hnat.eventually (eventually_ge_atTop x₀), hnat.eventually (hpar.eventually (eventually_ge_atTop 6)),
    hnat.eventually (eventually_const_le_mul_exp_neg_vk v 2 hv),
    hnat.eventually (hgap.eventually (eventually_ge_atTop (K + 1))), eventually_ge_atTop (1 : ℕ)]
    with N henvN hmono hN0 h6 h2 hgapN hN n
  let E := Real.exp (-u * vkProfile (N : ℝ))
  change 6 ≤ u * vkProfile (N : ℝ) at h6
  have hE : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [h6])
  have hent : E * (1 + Real.log (1 / E)) ≤ 1 / 2 := by
    simpa only [E, neg_mul] using exponential_entropy_small (u * vkProfile (N : ℝ)) h6
  have hMx (y : ℝ) (hy : (N : ℝ) ≤ y) : |M y| ≤ E * y := by
    apply (hx₀ y (hN0.trans hy)).trans
    apply mul_le_mul_of_nonneg_right _ ((Nat.cast_nonneg N).trans hy)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hmono y hy) (neg_nonpos.mpr hu.le))
  have hh := abs_defect_le_errorEnvelope N n (by omega) E hE hE1 hent hMx
  by_cases hhead : n ≤ N
  · rw [errorEnvelope, if_pos hhead] at hh
    exact hh.trans (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hhead))
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsmall := h2.trans (mul_le_mul_of_nonneg_right hNn (Real.exp_pos _).le)
  have he := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (hmono n hNn) (neg_nonpos.mpr hv.le))
  have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hnr) hK
  have heave : (K + 1) * Real.exp (-v * vkProfile (N : ℝ)) ≤ Real.exp (-c * vkProfile (N : ℝ)) := by
    calc
      _ ≤ Real.exp ((v-c) * vkProfile (N : ℝ)) * Real.exp (-v * vkProfile (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hgapN (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ 2 + K * ((n : ℝ) * Real.exp (-v * vkProfile (n : ℝ))) :=
      hh.trans (henvN n)
    _ ≤ (n : ℝ) * ((K + 1) * Real.exp (-v * vkProfile (N : ℝ))) := by
      linarith only [hsmall, ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left heave hnr

/-- Specialization to the exact external inequality of Lee–Leong, Theorem 1.1(11). -/
theorem abs_defect_le_leeLeong_cutoff_slope (h : LeeLeongMertensEstimate)
    (c : ℝ) (hc : 0 < c) (hca : c < leeLeongRate) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |qSequence (defect N) n| ≤
      (n : ℝ) * Real.exp (-c * vkProfile (N : ℝ)) :=
  abs_defect_le_vk_cutoff_slope leeLeongRate c 1 hc hca (mertens_vk_of_leeLeong h)

end RiemannResearch.RH.QMertensFirstMoment

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusVKSquareSamples
import RiemannResearch.Analysis.VinogradovKorobovProfile
import RiemannResearch.RH.QSquarefreeMertensProfileCriterion
import RiemannResearch.Analysis.MertensExponentialEntropy
import Mathlib.Data.Nat.Prime.Infinite

/-!
# VK Mertens bounds and the actual squarefree displacement
The Walfisz estimate is recorded, for example, in Gerhold (2010), equation
(2), DOI 10.4064/aa142-2-8. Its full infinite-range arithmetic bound is a
hypothesis in these formal implications. The norm estimates use complete tails.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMertensProfileCriterion
open RiemannResearch.Analysis
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- A VK Mertens estimate with exponent `a` permits displacement growth at
any fixed exponential rate `b < a/2`. The estimate for `M` is an explicit
arithmetic hypothesis. No uniform lower bound for the displacement is assumed. -/
theorem riemannHypothesis_of_vk_exponential_displacement
    (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * b < a)
    (hM : ∀ᶠ x : ℝ in atTop,
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M x| ≤
        Real.exp (-a * vkProfile x) * x)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
        D * Real.exp (b * vkProfile (n : ℝ))) : RiemannHypothesis := by
  classical
  choose p hpl hpp using (fun j : ℕ => Nat.exists_infinite_primes (j + 2))
  let q : ℕ → ℕ := fun j => p j - 1
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with j hj
    have := hpl j
    dsimp [q]; omega
  have hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1) := by
    apply Eventually.of_forall
    intro j
    have hqp : q j + 1 = p j := by have := hpl j; dsimp [q]; omega
    rw [hqp]; exact (hpp j).squarefree
  have hqr : Tendsto (fun j => (q j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hq
  let P : ℕ → ℝ := fun j => vkProfile (q j : ℝ)
  let ε : ℕ → ℝ := fun j => Real.exp (-a * P j)
  let H : ℕ → ℝ := fun n => Real.exp (b * vkProfile (n : ℝ))
  let c : ℝ := (a + 2 * b) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  have hbc : 0 < c - 2 * b := by dsimp [c]; linarith
  have hP : Tendsto P atTop atTop := vkProfile_tendsto_atTop.comp hqr
  have hlarge : ∀ᶠ j : ℕ in atTop, 6 ≤ a * P j :=
    (Tendsto.const_mul_atTop ha hP).eventually (eventually_ge_atTop (6 : ℝ))
  have hε : ∀ᶠ j : ℕ in atTop,
      0 < ε j ∧ ε j ≤ 1 ∧ ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2 := by
    filter_upwards [hlarge] with j hj
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by nlinarith), ?_⟩
    simpa only [ε, neg_mul] using exponential_entropy_small (a * P j) hj
  have hMtail : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε j * y := by
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hM
    filter_upwards [hqr.eventually (eventually_ge_atTop x₀),
      hqr.eventually vkProfile_eventually_mono] with j hj hmono
    intro y hy
    have hm := mul_le_mul_of_nonneg_left (hmono y hy) ha.le
    apply (hx₀ y (hj.trans hy)).trans
    apply mul_le_mul_of_nonneg_right _ ((Nat.cast_nonneg (q j)).trans hy)
    apply Real.exp_le_exp.mpr
    change -a * vkProfile y ≤ -a * vkProfile (q j : ℝ)
    linarith
  have hnon : ∀ᶠ j : ℕ in atTop, 0 ≤ ε j * (1 + Real.log (1 / ε j)) := by
    filter_upwards [hε] with j hj
    have hi : (1 : ℝ) ≤ 1 / ε j :=
      (le_div_iff₀ hj.1).2 (by simpa only [one_mul] using hj.2.1)
    exact mul_nonneg hj.1.le (by linarith [Real.log_nonneg hi])
  have hpoint (j : ℕ) : ε j * (1 + Real.log (1 / ε j)) ≤
      (a / (a - c)) * Real.exp (-c * P j) := exponential_entropy_le a c (P j) hc.le hca
  have hzero (k : ℝ) (hk : 0 < k) :
      Tendsto (fun j => Real.exp (-k * P j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hk hP)
  have hη : Tendsto (fun j => ε j * (1 + Real.log (1 / ε j))) atTop (𝓝 0) := by
    apply squeeze_zero' hnon (Eventually.of_forall hpoint)
    simpa only [mul_zero] using (hzero c hc).const_mul (a / (a - c))
  have hshape (x : ℝ) (hx : 0 < x) :
      Real.exp (b * vkProfile x) ^ 2 / Real.sqrt x =
        Real.exp (2 * b * vkProfile x - Real.log x / 2) := by
    rw [pow_two, ← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_sub]
    congr 1; ring
  have hprofile : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      H n ^ 2 / Real.sqrt (n : ℝ) ≤ H N ^ 2 / Real.sqrt (N : ℝ) := by
    have hinc := (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (vkProfile_eventual_log_increment (1 / (4 * b)) (by positivity))
    filter_upwards [hinc, eventually_ge_atTop (1 : ℕ)] with N hN hNp
    intro n hn
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog := hN (n : ℝ) (by exact_mod_cast hn.le)
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * b by positivity)
    have heq : (2 * b) * ((1 / (4 * b)) * (Real.log (n : ℝ) - Real.log (N : ℝ))) =
        (Real.log (n : ℝ) - Real.log (N : ℝ)) / 2 := by
      field_simp [hb.ne'] <;> ring
    rw [heq] at hh
    dsimp only [H]
    rw [hshape _ hnr, hshape _ hNr]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsmall : Tendsto (fun j => (ε j * (1 + Real.log (1 / ε j))) * H (q j) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _
      (show Tendsto (fun j => (a / (a - c)) * Real.exp (-(c - 2 * b) * P j))
          atTop (𝓝 0) by
        simpa only [mul_zero] using (hzero (c - 2 * b) hbc).const_mul (a / (a - c)))
    · filter_upwards [hnon] with j hj; exact mul_nonneg hj (sq_nonneg _)
    · apply Eventually.of_forall
      intro j
      calc
        _ ≤ ((a / (a - c)) * Real.exp (-c * P j)) * H (q j) ^ 2 :=
          mul_le_mul_of_nonneg_right (hpoint j) (sq_nonneg _)
        _ = (a / (a - c)) * Real.exp (-(c - 2 * b) * P j) := by
          change ((a / (a - c)) * Real.exp (-c * P j)) * Real.exp (b * P j) ^ 2 = _
          rw [mul_assoc, pow_two, ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
  exact riemannHypothesis_of_mertens_profile_physical_bound q hq ε hlegal hε hMtail hη H D
    hprofile hd hsmall

/-- The selected little-o hypothesis supplies the fixed positive coefficient
required by the stronger constant-exponent theorem. -/
theorem riemannHypothesis_of_vk_log_displacement
    (a : ℝ) (ha : 0 < a)
    (hM : ∀ᶠ x : ℝ in atTop,
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M x| ≤
        Real.exp (-a * vkProfile x) * x)
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
        vkProfile (n : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let b : ℝ := a / 4
  have hb : 0 < b := by dsimp [b]; positivity
  apply riemannHypothesis_of_vk_exponential_displacement a b 1 ha hb
    (by dsimp [b]; linarith) hM
  have hΦ : Tendsto (fun n : ℕ => vkProfile (n : ℝ)) atTop atTop :=
    vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hd.eventually (gt_mem_nhds hb),
    hΦ.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hp
  have hh := Real.exp_le_exp.mpr ((div_lt_iff₀ hp).1 hn).le
  rw [Real.exp_log (by positivity)] at hh
  linarith

/-- A fixed multiplicative constant in a published VK Mertens estimate can
be absorbed at every smaller exponential rate. -/
theorem mertens_vk_absorb_constant (a a' C : ℝ) (h : a' < a)
    (hM : ∀ᶠ x : ℝ in atTop,
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M x| ≤
        (C * Real.exp (-a * vkProfile x)) * x) :
    ∀ᶠ x : ℝ in atTop, |RiemannResearch.NumberTheory.PrimeNumberTheorem.M x| ≤
      Real.exp (-a' * vkProfile x) * x := by
  have hlim := Real.tendsto_exp_atTop.comp
    (Tendsto.const_mul_atTop (sub_pos.mpr h) vkProfile_tendsto_atTop)
  filter_upwards [hM, hlim.eventually (eventually_ge_atTop C),
    eventually_ge_atTop (0 : ℝ)] with x hx hC hx0
  calc
    _ ≤ (C * Real.exp (-a * vkProfile x)) * x := hx
    _ ≤ (Real.exp ((a - a') * vkProfile x) * Real.exp (-a * vkProfile x)) * x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le) hx0
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- The fixed-rate displacement theorem therefore holds literally under the
usual form of the published Walfisz bound, including its implicit constant. -/
theorem riemannHypothesis_of_walfisz_displacement (a b C D : ℝ)
    (hb : 0 < b) (hab : 2*b < a)
    (hM : ∀ᶠ x : ℝ in atTop,
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M x| ≤
        (C * Real.exp (-a * vkProfile x)) * x)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
        D * Real.exp (b * vkProfile (n : ℝ))) : RiemannHypothesis := by
  let a' : ℝ := (a + 2*b)/2
  have ha' : 0 < a' := by dsimp [a']; linarith
  have hba' : 2*b < a' := by dsimp [a']; linarith
  have h' : a' < a := by dsimp [a']; linarith
  exact riemannHypothesis_of_vk_exponential_displacement a' b D ha' hb hba'
    (mertens_vk_absorb_constant a a' C h' hM) hd

open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The boxed little-o criterion needs the published arithmetic bound only on squares. -/
theorem riemannHypothesis_of_square_sample_vk_log_displacement (a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hM : ∀ᶠ k : ℕ in atTop, |M ((k : ℝ) ^ 2)| ≤
      C * (Real.exp (-a * vkProfile ((k : ℝ) ^ 2)) * (k : ℝ) ^ 2))
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      vkProfile (n : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_vk_log_displacement (a / 2) (by positivity) _ hd
  exact mertens_vk_absorb_constant a (a / 2) (C+3) (by linarith)
    (mertens_vk_of_square_samples a C ha hC hM)

end RiemannResearch.RH.QSquarefreeMertensProfileCriterion

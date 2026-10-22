/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.RawMobiusFirstWindow
import RiemannResearch.RH.MobiusQuantitativeRate

/-!
# Quantitative cancellation for the actual first raw Mobius window

Source: direct finite weighted-square estimates and the existing quantitative
prime number theorem, developed for the user's directed RH attempt on
September 24, 2026. The finite Mertens-bound hypotheses are discharged in
mobiusFirstWindowIncrementEnergy_eventual_log_square_bound by the local PNT
provider. The actual head-plus-first-window budget then satisfies
(W_N/N)*log N -> 0 with no unproved arithmetic hypothesis.
This is not a subpower estimate, and the growing window through N^2 is not
claimed controlled at the rate required for RH.
-/

/-!
# Quantitative energy of actual first-window Mertens increments

Source: direct finite-window consequence of the repository's quantitative PNT
provider, developed for the directed RH attempt on September 24, 2026.
The local bound only uses actual Mertens sums on [N,2N]. The final theorem
eliminates that hypothesis through the existing proved arithmetic provider.
The result bounds the first increment window, not the entire square budget.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

theorem mobiusFirstWindowIncrement_abs_le_of_M_bound
    (N k : ℕ) (A : ℝ) (hA : 0 ≤ A) (hNk : N ≤ k) (hk : k ≤ 2*N)
    (hM : ∀ t : ℕ, N ≤ t → t ≤ 2*N →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ A*(t : ℝ)) :
    |mobiusFirstWindowIncrement N k| ≤ 2*A*(k : ℝ) := by
  have hnR : (N : ℝ) ≤ k := by exact_mod_cast hNk
  have hAN := mul_le_mul_of_nonneg_left hnR hA
  calc
    _ ≤ |∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ)| +
        |∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)| := by
      unfold mobiusFirstWindowIncrement
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ))
          (-(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)))
    _ ≤ A*(k : ℝ)+A*(N : ℝ) :=
      add_le_add (hM k hNk hk) (hM N le_rfl (by omega))
    _ ≤ _ := by linarith

theorem mobiusFirstWindowIncrementEnergy_le_of_M_bound
    (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ t : ℕ, N ≤ t → t ≤ 2*N →
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ A*(t : ℝ)) :
    mobiusFirstWindowIncrementEnergy N ≤ 4*A^2*(N : ℝ) := by
  unfold mobiusFirstWindowIncrementEnergy
  calc
    _ ≤ ∑ i ∈ Finset.range N, (4*A^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      let k := i+(N+1)
      have hk : 0 < k := by dsimp [k]; omega
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hd := mobiusFirstWindowIncrement_abs_le_of_M_bound N k A hA
        (by dsimp [k]; omega) (by dsimp [k]; omega) hM
      have hsq0 := mul_self_le_mul_self (abs_nonneg _) hd
      simp only [← pow_two, sq_abs] at hsq0
      have hsq : mobiusFirstWindowIncrement N k^2 ≤ 4*A^2*(k : ℝ)^2 := by
        nlinarith only [hsq0]
      have hw : positiveWeight k*(k : ℝ)^2 ≤ 1 := by
        have he : positiveWeight k*(k : ℝ)^2 = (k : ℝ)/((k : ℝ)+1) := by
          unfold positiveWeight
          field_simp
        rw [he]
        exact (div_le_one (by positivity)).mpr (by linarith)
      have hp := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg k)
      have hp' := mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ 4*A^2)
      change positiveWeight k*mobiusFirstWindowIncrement N k^2 ≤ 4*A^2
      nlinarith only [hp, hp']
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

open RiemannResearch.NumberTheory.PrimeNumberTheorem in
theorem mobiusFirstWindowIncrementEnergy_eventual_log_square_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      mobiusFirstWindowIncrementEnergy N ≤
        4*C^2*(N : ℝ)/(Real.log (N : ℝ))^2 := by
  obtain ⟨C,hC,hM⟩ := exists_M_mul_log_bound_from_quantitative_PNT
  refine ⟨C,hC,?_⟩
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hM
  have hNY : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop Y)
  filter_upwards [hNY, eventually_ge_atTop (2 : ℕ)] with N hNY hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbound : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ (C/Real.log (N : ℝ))*y := by
    intro y hy
    have hy1 : 1 < y := hN1.trans_le hy
    have hlogy : 0 ≤ Real.log y := (Real.log_pos hy1).le
    have hlog : Real.log (N : ℝ) ≤ Real.log y := Real.log_le_log (by positivity) hy
    have hh := hY y (hNY.trans hy)
    rw [abs_mul, abs_of_nonneg hlogy] at hh
    have hl : |M y| *Real.log (N : ℝ) ≤ C*y :=
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)).trans hh
    calc
      |M y| ≤ (C*y)/Real.log (N : ℝ) := (le_div_iff₀ hlogN).mpr hl
      _ = _ := by ring
  have hnat : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ (C/Real.log (N : ℝ))*(t : ℝ) := by
    intro t hNt
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hzero : M (0 : ℝ) = 0 := by
      have hz : Finset.Iic (0 : ℕ) = {0} := by ext n; simp
      simp [M, hz]
    rw [hset, Nat.cast_zero, hzero, sub_zero] at hi
    rw [← hi]
    exact hbound _ (by exact_mod_cast hNt)
  have he := mobiusFirstWindowIncrementEnergy_le_of_M_bound N (C/Real.log (N : ℝ))
    (div_nonneg hC hlogN.le) (fun t ht _ => hnat t ht)
  calc
    _ ≤ 4*(C/Real.log (N : ℝ))^2*(N : ℝ) := he
    _ = _ := by ring

/-! The next results concern the actual raw residual, including its head term. -/

def rawMobiusFirstWindowBudget (N : ℕ) : ℝ :=
  (N : ℝ)*(mobiusReciprocalSum N)^2 + rawMobiusMiddleEnergy N (2*N)

theorem rawMobiusFirstWindowBudget_nonneg (N : ℕ) :
    0 ≤ rawMobiusFirstWindowBudget N := by
  unfold rawMobiusFirstWindowBudget
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (mobiusReciprocalSum N)))
    (rawMobiusMiddleEnergy_nonneg N (2*N))

theorem rawMobiusFirstWindowBudget_le_increment_energy (N : ℕ) :
    rawMobiusFirstWindowBudget N ≤
      3*(N : ℝ)*(mobiusReciprocalSum N)^2 +
        2*mobiusFirstWindowIncrementEnergy N := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range N) :
      rawMobiusCoordinateEnergy N (i+(N+1)) ≤
        2*(mobiusReciprocalSum N)^2 +
          2*(positiveWeight (i+(N+1))*
            mobiusFirstWindowIncrement N (i+(N+1))^2) := by
    have hi' := Finset.mem_range.mp hi
    let k := i+(N+1)
    have hk : 0 < k := by dsimp [k]; omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hid := rawMobiusResidual_first_window N k
      (by dsimp [k]; omega) (by dsimp [k]; omega)
    have hsq : (hilbertSequence (hilbertOne-rawMobiusHilbert N) k)^2 ≤
        2*(k : ℝ)^2*(mobiusReciprocalSum N)^2 +
          2*mobiusFirstWindowIncrement N k^2 := by
      rw [hid]
      nlinarith [sq_nonneg ((k : ℝ)*mobiusReciprocalSum N -
        mobiusFirstWindowIncrement N k)]
    have hw : positiveWeight k*(k : ℝ)^2 ≤ 1 := by
      have he : positiveWeight k*(k : ℝ)^2 = (k : ℝ)/((k : ℝ)+1) := by
        unfold positiveWeight
        field_simp
      rw [he]
      exact (div_le_one (by positivity)).mpr (by linarith)
    have hp := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg k)
    have hp' := mul_le_mul_of_nonneg_right hw (sq_nonneg (mobiusReciprocalSum N))
    change rawMobiusCoordinateEnergy N k ≤ 2*(mobiusReciprocalSum N)^2 +
      2*(positiveWeight k*mobiusFirstWindowIncrement N k^2)
    unfold rawMobiusCoordinateEnergy
    nlinarith only [hp, hp']
  have hsum : rawMobiusMiddleEnergy N (2*N) ≤
      2*(N : ℝ)*(mobiusReciprocalSum N)^2 +
        2*mobiusFirstWindowIncrementEnergy N := by
    calc
      _ = ∑ i ∈ Finset.range N, rawMobiusCoordinateEnergy N (i+(N+1)) := by
        unfold rawMobiusMiddleEnergy
        rw [show 2*N-N = N by omega]
      _ ≤ ∑ i ∈ Finset.range N,
          (2*(mobiusReciprocalSum N)^2 +
            2*(positiveWeight (i+(N+1))*
              mobiusFirstWindowIncrement N (i+(N+1))^2)) :=
        Finset.sum_le_sum hterm
      _ = _ := by
        unfold mobiusFirstWindowIncrementEnergy
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
  unfold rawMobiusFirstWindowBudget
  nlinarith only [hsum]

/-- The actual head-plus-first-window budget has a vanishing logarithmic
normalization, using only established quantitative PNT cancellation. -/
theorem rawMobiusFirstWindowBudget_div_mul_log_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (rawMobiusFirstWindowBudget N/(N : ℝ))*Real.log (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hE⟩ := mobiusFirstWindowIncrementEnergy_eventual_log_square_bound
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => 1/Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have ht : Tendsto (fun N : ℕ =>
      3*(mobiusReciprocalSum N)^2*Real.log (N : ℝ) +
        8*C^2/Real.log (N : ℝ)) atTop (𝓝 0) := by
    have hh := (mobiusReciprocalSum_sq_mul_log_tendsto_zero.const_mul 3).add
      (hi.const_mul (8*C^2))
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext N
    ring
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos hN1).le
    exact ha.trans_le (mul_nonneg
      (div_nonneg (rawMobiusFirstWindowBudget_nonneg N) (Nat.cast_nonneg N)) hlog)
  · intro b hb
    filter_upwards [ht.eventually (gt_mem_nhds hb), hE,
      eventually_ge_atTop (2 : ℕ)] with N hNb hEN hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNR : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hbudget : rawMobiusFirstWindowBudget N/(N : ℝ) ≤
        3*(mobiusReciprocalSum N)^2 + 8*C^2/(Real.log (N : ℝ))^2 := by
      apply (div_le_iff₀ hNR).mpr
      calc
        _ ≤ 3*(N : ℝ)*(mobiusReciprocalSum N)^2 +
            2*mobiusFirstWindowIncrementEnergy N :=
          rawMobiusFirstWindowBudget_le_increment_energy N
        _ ≤ 3*(N : ℝ)*(mobiusReciprocalSum N)^2 +
            2*(4*C^2*(N : ℝ)/(Real.log (N : ℝ))^2) := by linarith only [hEN]
        _ = _ := by ring
    have hfinal : (rawMobiusFirstWindowBudget N/(N : ℝ))*Real.log (N : ℝ) ≤
        3*(mobiusReciprocalSum N)^2*Real.log (N : ℝ) +
          8*C^2/Real.log (N : ℝ) := by
      calc
        _ ≤ (3*(mobiusReciprocalSum N)^2 +
            8*C^2/(Real.log (N : ℝ))^2)*Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hbudget hlog.le
        _ = _ := by
          field_simp [hlog.ne']
    exact hfinal.trans_lt hNb

end RiemannResearch.RH.Pareto

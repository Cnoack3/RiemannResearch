import RiemannResearch.Analysis.MangoldtSquareAsymptotic
import RiemannResearch.Analysis.DyadicPrimeTentConstants

/-!
# Prime-weighted square-root asymptotics

Discrete partial summation transfers the repo's unconditional prime number theorem
for Chebyshev's theta to the first harmonic in the dyadic Wasserstein witness.
The summation variable here is the prime cutoff. No zero-height variable occurs.
-/

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.DyadicZeroWasserstein

private theorem eventual_ratio_lower_of_increments
    {F G : ℕ → ℝ} {a b : ℝ} (hab : a < b) (hG : Tendsto G atTop atTop)
    (hstep : ∀ᶠ n in atTop, b * (G (n + 1) - G n) ≤ F (n + 1) - F n) :
    ∀ᶠ n in atTop, a < F n / G n := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hstep
  have hbound (n : ℕ) (hn : K ≤ n) :
      F K - b * G K + b * G n ≤ F n := by
    induction n, hn using Nat.le_induction with
    | base => linarith
    | succ n hn ih =>
      have h := hK n hn
      linarith
  have hsmall : Tendsto (fun n => (F K - b * G K) / G n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hG
  have huv := hsmall.eventually (eventually_gt_nhds (show a - b < 0 by linarith))
  filter_upwards [huv, hG.eventually_gt_atTop 0, eventually_ge_atTop K] with n hn hpos hkn
  have hlt := (lt_div_iff₀ hpos).mp hn
  apply (lt_div_iff₀ hpos).mpr
  have := hbound n hkn
  linarith

private theorem ratio_tendsto_of_increments
    {F G A : ℕ → ℝ} {c : ℝ} (hG : Tendsto G atTop atTop)
    (hmono : Monotone G) (hA : Tendsto A atTop (𝓝 c))
    (hstep : ∀ᶠ n in atTop, F (n + 1) - F n = A n * (G (n + 1) - G n)) :
    Tendsto (fun n => F n / G n) atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hab, hbc⟩ := exists_between ha
    apply eventual_ratio_lower_of_increments hab hG
    filter_upwards [hstep, hA.eventually (eventually_gt_nhds hbc)] with n hn h
    rw [hn]
    exact mul_le_mul_of_nonneg_right h.le (sub_nonneg.mpr (hmono (Nat.le_succ n)))
  · intro a ha
    obtain ⟨b, hcb, hba⟩ := exists_between ha
    have hs : ∀ᶠ n in atTop,
        (-b) * (G (n + 1) - G n) ≤ (-F (n + 1)) - (-F n) := by
      filter_upwards [hstep, hA.eventually (eventually_lt_nhds hcb)] with n hn h
      have hle := mul_le_mul_of_nonneg_right h.le (sub_nonneg.mpr (hmono (Nat.le_succ n)))
      linarith
    have hlt := eventual_ratio_lower_of_increments (F := fun n => -F n)
      (neg_lt_neg hba) hG hs
    filter_upwards [hlt] with n hn
    simpa only [neg_div, neg_lt_neg_iff] using hn

private def primeRootSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log p / Real.sqrt p

private def primeRootRemainder (n : ℕ) : ℝ :=
  primeRootSum n - Chebyshev.theta n / Real.sqrt n

private theorem primeRootRemainder_step (n : ℕ) (hn : 0 < n) :
    primeRootRemainder (n + 1) - primeRootRemainder n =
      (Chebyshev.theta n / (Real.sqrt n * Real.sqrt (↑(n + 1) : ℝ))) *
      (Real.sqrt (↑(n + 1) : ℝ) - Real.sqrt n) := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have ht : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hnot : n + 1 ∉ n.primesLE :=
    fun h => (Nat.not_succ_le_self n) (Nat.le_of_mem_primesLE h)
  simp only [primeRootRemainder, primeRootSum, Chebyshev.theta_eq_sum_primesLE_log,
    Nat.primesLE_succ]
  by_cases hp : (n + 1).Prime
  · simp only [if_pos hp, Finset.sum_insert hnot]
    field_simp [hs, ht]
    ring
  · simp only [if_neg hp]
    field_simp [hs, ht]
    ring

private theorem theta_root_slope_tendsto :
    Tendsto (fun n : ℕ => Chebyshev.theta n /
      (Real.sqrt n * Real.sqrt (↑(n + 1) : ℝ))) atTop (𝓝 1) := by
  have hsucc : Tendsto (fun n : ℕ => (↑(n + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hone : Tendsto (fun n : ℕ => 1 / (↑(n + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsucc
  have hquot : Tendsto (fun n : ℕ => (n : ℝ) / (↑(n + 1) : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hone
    simp only [sub_zero] at h
    apply h.congr
    intro n
    push_cast
    field_simp <;> ring
  have hθ := MangoldtSquareAsymptotic.theta_ratio_tendsto.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hθ.mul hquot.sqrt
  simp only [Real.sqrt_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have ht : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div (by positivity)]
  field_simp [hs, ht, hn0]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]

/-- Unconditional PNT with the weight appearing in the first cosine and tent modes. -/
theorem prime_log_div_sqrt_sum_asymptotic :
    Tendsto (fun n : ℕ => (∑ p ∈ n.primesLE, Real.log p / Real.sqrt p) /
      Real.sqrt n) atTop (𝓝 2) := by
  let G : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  have hG : Tendsto G atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hm : Monotone G := fun i j hij => Real.sqrt_le_sqrt (by exact_mod_cast hij)
  have hrem := ratio_tendsto_of_increments (F := primeRootRemainder) hG hm
    theta_root_slope_tendsto (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact primeRootRemainder_step n hn)
  have hθ := MangoldtSquareAsymptotic.theta_ratio_tendsto.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hrem.add hθ
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (primeRootSum n - Chebyshev.theta n / Real.sqrt n) / Real.sqrt n +
    Chebyshev.theta n / n = primeRootSum n / Real.sqrt n
  field_simp [hs, hn0]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  ring


/-- The odd-harmonic correction is uniformly bounded under finite prime summation,
so the exact leading coefficient is (4/π²) along prime cutoffs. -/
theorem primeTentConstant_primeCutoff_asymptotic :
    Tendsto (fun n : ℕ => (∑ p ∈ n.primesLE, primeTentConstant p) / Real.sqrt n)
      atTop (𝓝 (4 / Real.pi ^ 2)) := by
  let E (n : ℕ) : ℝ := (∑ p ∈ n.primesLE, primeTentConstant p) -
    (2 / Real.pi ^ 2) * ∑ p ∈ n.primesLE, Real.log p / Real.sqrt p
  obtain ⟨C, hC⟩ := exists_primeTentConstant_correction_sum_bound
  have hbound (n : ℕ) : |E n| ≤ C := hC n.primesLE (fun _ hp => Nat.prime_of_mem_primesLE hp)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => E n / Real.sqrt n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds.div_atTop (a := -C) hroot)
      (tendsto_const_nhds.div_atTop (a := C) hroot)
    · intro n
      exact div_le_div_of_nonneg_right (abs_le.mp (hbound n)).1 (Real.sqrt_nonneg _)
    · intro n
      exact div_le_div_of_nonneg_right (abs_le.mp (hbound n)).2 (Real.sqrt_nonneg _)
  have h := (prime_log_div_sqrt_sum_asymptotic.const_mul (2 / Real.pi ^ 2)).add herr
  rw [show (2 / Real.pi ^ 2) * 2 + 0 = 4 / Real.pi ^ 2 by ring] at h
  apply h.congr
  intro n
  dsimp [E]
  ring

/-- Prime cutoff tends to infinity after the fixed-prime-set lower estimate. -/
theorem primeTentConstant_primeCutoff_tendsto_atTop :
    Tendsto (fun n : ℕ => ∑ p ∈ n.primesLE, primeTentConstant p) atTop atTop := by
  have hc : 0 < (4 / Real.pi ^ 2 : ℝ) := by positivity
  have hs := primeTentConstant_primeCutoff_asymptotic.eventually
    (eventually_gt_nhds (show (4 / Real.pi ^ 2) / 2 < 4 / Real.pi ^ 2 by linarith))
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ (hroot.const_mul_atTop (show 0 < (4 / Real.pi ^ 2) / 2 by linarith))
  filter_upwards [hs, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  exact ((lt_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hpos))).mp hn).le

/-- Exact leading asymptotic in the real cutoff convention of the research note. -/
theorem primeTentConstant_realCutoff_asymptotic :
    Tendsto (fun x : ℝ => (∑ p ∈ (Nat.floor x).primesLE, primeTentConstant p) / Real.sqrt x)
      atTop (𝓝 (4 / Real.pi ^ 2)) := by
  have hf : Tendsto (fun x : ℝ => (Nat.floor x : ℝ) / x) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact hx.ne')).mp (Asymptotics.isEquivalent_nat_floor (R := ℝ))
  have h := (primeTentConstant_primeCutoff_asymptotic.comp tendsto_nat_floor_atTop).mul hf.sqrt
  simp only [Real.sqrt_one, mul_one] at h
  apply h.congr'
  filter_upwards [tendsto_nat_floor_atTop.eventually_gt_atTop (0 : ℕ)] with x hx
  have hpos : Real.sqrt (Nat.floor x : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hx)).ne'
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div (by positivity)]
  field_simp [hpos]

/-- Any family of finite prime sets eventually containing every prime prefix has
divergent tent constants. The sets themselves need not be nested. -/
theorem primeTentConstant_tendsto_of_exhaustion {ι : Type*} {l : Filter ι}
    (S : ι → Finset ℕ) (hprime : ∀ i, ∀ p ∈ S i, p.Prime)
    (hexh : ∀ n : ℕ, ∀ᶠ i in l, n.primesLE ⊆ S i) :
    Tendsto (fun i => ∑ p ∈ S i, primeTentConstant p) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨n, hn⟩ := (primeTentConstant_primeCutoff_tendsto_atTop.eventually_ge_atTop b).exists
  filter_upwards [hexh n] with i hi
  apply hn.trans (Finset.sum_le_sum_of_subset_of_nonneg hi ?_)
  intro p hp _
  exact (primeTentConstant_pos (hprime i p hp)).le

end RiemannResearch.Analysis.DyadicZeroWasserstein

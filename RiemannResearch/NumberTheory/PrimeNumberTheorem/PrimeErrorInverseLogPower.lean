import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogSq

/-! Every fixed inverse-log power follows from the already verified MediumPNT.
The constant and threshold may depend on the exponent. -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

lemma Quantitative.exp_log_tenth_eventually_le_inverseLogPower
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤
        (2 : ℝ) ^ k / (1 + Real.log x) ^ k := by
  have hu : Tendsto
      (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hp : ∀ᶠ t : ℝ in atTop,
      ‖t ^ (10 * k)‖ ≤ 1 * ‖Real.exp (c * t)‖ :=
    (isLittleO_pow_exp_pos_mul_atTop (10 * k) hc).bound (by norm_num)
  filter_upwards [hu.eventually hp,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hpow hlog
  have hlog0 : 0 ≤ Real.log x := le_trans zero_le_one hlog
  have hten :
      ((Real.log x) ^ ((1 : ℝ) / 10)) ^ (10 * k) =
        (Real.log x) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    have he : ((1 : ℝ) / 10) * ((10 * k : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  have hpower : (Real.log x) ^ k ≤
      Real.exp (c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    simpa only [hten, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (pow_nonneg hlog0 k),
      abs_of_pos (Real.exp_pos _)] using hpow
  have hpoly : (1 + Real.log x) ^ k ≤ (2 : ℝ) ^ k * (Real.log x) ^ k := by
    rw [← mul_pow]
    gcongr
    linarith
  have hexp :
      Real.exp (c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hden : 0 < (1 + Real.log x) ^ k := by positivity
  apply (le_div_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_right
    (hpoly.trans (mul_le_mul_of_nonneg_left hpower (by positivity : (0 : ℝ) ≤ 2 ^ k)))
    (Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))).le
  calc
    _ = (1 + Real.log x) ^ k *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by ring
    _ ≤ ((2 : ℝ) ^ k * Real.exp (c * (Real.log x) ^ ((1 : ℝ) / 10))) *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := hscaled
    _ = (2 : ℝ) ^ k := by rw [mul_assoc, hexp, mul_one]

theorem R_inverseLogPower_bound_of_medium (k : ℕ)
    (hMedium : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ k := by
  obtain ⟨c, hc, hmedium⟩ := hMedium
  obtain ⟨A, hA, hAbound⟩ := hmedium.exists_pos
  have htail : ∀ᶠ y : ℝ in atTop,
      |R y| ≤ ((2 : ℝ) ^ k * A) * y / (1 + Real.log y) ^ k := by
    have hAbound' : ∀ᶠ y : ℝ in atTop,
        ‖Chebyshev.psi y - y‖ ≤
          A * ‖y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))‖ := by
      simpa only [Asymptotics.IsBigOWith, Pi.sub_apply, id_eq] using hAbound
    filter_upwards [hAbound',
      Quantitative.exp_log_tenth_eventually_le_inverseLogPower k hc,
      eventually_ge_atTop (1 : ℝ)] with y hbound hdecay hy
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hbound' : |R y| ≤
        A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := by
      simpa only [R, Psi, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hy0 (Real.exp_pos _).le)] using hbound
    calc
      |R y| ≤ A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := hbound'
      _ ≤ A * (y * ((2 : ℝ) ^ k / (1 + Real.log y) ^ k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdecay hy0) hA.le
      _ = ((2 : ℝ) ^ k * A) * y / (1 + Real.log y) ^ k := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let B : ℝ := max 1 T
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨K, hKbound⟩ := R_locally_bounded B (le_trans zero_le_one hB)
  have hK : 0 ≤ K :=
    (abs_nonneg (R 0)).trans
      (hKbound 0 ⟨le_rfl, le_trans zero_le_one hB⟩)
  let C : ℝ := max ((2 : ℝ) ^ k * A) (K * (1 + Real.log B) ^ k)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hden : 0 < (1 + Real.log y) ^ k := by
    have := Real.log_nonneg hy
    positivity
  by_cases hTy : T ≤ y
  · exact (hT y hTy).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0) hden.le)
  · have hyB : y ≤ B := (lt_of_not_ge hTy).le.trans (le_max_right _ _)
    have hlog : Real.log y ≤ Real.log B :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hy) hyB
    have hlogsq : (1 + Real.log y) ^ k ≤ (1 + Real.log B) ^ k := by
      have := Real.log_nonneg hy
      gcongr <;> first | exact hlog | exact hyB | positivity
    apply (le_div_iff₀ hden).2
    calc
      |R y| * (1 + Real.log y) ^ k ≤ K * (1 + Real.log y) ^ k :=
        mul_le_mul_of_nonneg_right (hKbound y ⟨hy0, hyB⟩) hden.le
      _ ≤ K * (1 + Real.log B) ^ k :=
        mul_le_mul_of_nonneg_left hlogsq hK
      _ ≤ C := le_max_right _ _
      _ ≤ C * y := le_mul_of_one_le_right hC.le hy

theorem R_inverseLogPower_bound (k : ℕ) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ k :=
  R_inverseLogPower_bound_of_medium k Quantitative.MediumPNT


end RiemannResearch.NumberTheory.PrimeNumberTheorem

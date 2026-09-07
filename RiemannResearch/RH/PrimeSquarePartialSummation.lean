import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact prime-square summation for window tests

Source: user-provided argument, `RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`
§9.2 and `signed_gain_agent.md` §10.3. These support the statements and the
partial-summation proof strategy.

The arithmetic weights here are exactly `log p / p`, with the predicate
`Nat.Prime`, and the displacement is `2 * log p / R`. The finite formula
retains its upper boundary and the whole prime counting function.
-/

open scoped BigOperators
open MeasureTheory Set
namespace RiemannResearch.RH

/-- The coefficient of the prime-square sector, zero on nonprimes. -/
noncomputable def primeSquareWeight (p : ℕ) : ℝ :=
  if p.Prime then Real.log p / p else 0

/-- Weighted prime counting in the ordinary (not logarithmic) coordinate. -/
noncomputable def primeReciprocalLogSum (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 0 ⌊x⌋₊, primeSquareWeight p

/-- Exact prime-square discrepancy in the ordinary coordinate. -/
noncomputable def primeSquareDiscrepancy (x : ℝ) : ℝ :=
  primeReciprocalLogSum x - Real.log x

/-- Prime-square sector with the exact finite prime cutoff `p ≤ b`. -/
noncomputable def primeSquareCutoff (c : ℝ → ℝ) (R b : ℝ) : ℝ :=
  -2 * ∑ p ∈ Finset.Icc 0 ⌊b⌋₊,
    primeSquareWeight p * c (2 * Real.log p / R)

/-- Prime-square sector, with finiteness proved below for supported profiles. -/
noncomputable def primeSquareSector (c : ℝ → ℝ) (R : ℝ) : ℝ :=
  -2 * ∑' p : ℕ, primeSquareWeight p * c (2 * Real.log p / R)

theorem primeSquareWeight_zero : primeSquareWeight 0 = 0 := by
  simp [primeSquareWeight]

theorem primeSquareWeight_one : primeSquareWeight 1 = 0 := by
  simp [primeSquareWeight]

/-- Abel summation for the actual arithmetic prime-square weights.
No estimate for primes is used, and the upper boundary is retained. -/
theorem primeSquareCutoff_partial_summation (c : ℝ → ℝ) (R b : ℝ)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x)
    (hi : IntegrableOn (deriv (fun x => c (2 * Real.log x / R))) (Icc 1 b)) :
    primeSquareCutoff c R b =
      -2 * c (2 * Real.log b / R) * primeReciprocalLogSum b +
      2 * ∫ x in Ioc 1 b, deriv (fun x => c (2 * Real.log x / R)) x *
        primeReciprocalLogSum x := by
  have h := sum_mul_eq_sub_integral_mul₀ primeSquareWeight primeSquareWeight_zero b hd hi
  simp only [primeSquareCutoff, primeReciprocalLogSum]
  simp_rw [mul_comm (primeSquareWeight _) (c _)]
  rw [h]
  ring

/-- Beyond the support radius, every individual prime-square summand vanishes. -/
theorem primeSquareTerm_eq_zero_of_cutoff (c : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (hc : ∀ s, 1 ≤ s → c s = 0) {b : ℝ} (hb : Real.exp (R / 2) ≤ b)
    {p : ℕ} (hp : ⌊b⌋₊ < p) :
    primeSquareWeight p * c (2 * Real.log p / R) = 0 := by
  have hbp : b < (p : ℝ) := (Nat.floor_lt (le_trans (Real.exp_pos _).le hb)).mp hp
  have hpp : 0 < (p : ℝ) := lt_trans (Real.exp_pos _) (lt_of_le_of_lt hb hbp)
  have hlog : R / 2 ≤ Real.log p :=
    (Real.le_log_iff_exp_le hpp).mpr (le_trans hb hbp.le)
  have hs : 1 ≤ 2 * Real.log p / R := (le_div_iff₀ hR).mpr (by linarith)
  rw [hc _ hs, mul_zero]

/-- The infinite notation equals an actual finite prime sum for supported profiles. -/
theorem primeSquareSector_eq_cutoff (c : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (hc : ∀ s, 1 ≤ s → c s = 0) {b : ℝ} (hb : Real.exp (R / 2) ≤ b) :
    primeSquareSector c R = primeSquareCutoff c R b := by
  unfold primeSquareSector primeSquareCutoff
  congr 1
  apply tsum_eq_sum
  intro p hp
  apply primeSquareTerm_eq_zero_of_cutoff c hR hc hb
  simpa only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] using hp

/-- Integrability of the retained arithmetic discrepancy for a C¹ window profile. -/
theorem integrable_primeSquareDiscrepancy_mul {g : ℝ → ℝ} {b : ℝ}
    (hg' : ContinuousOn (deriv g) (Icc 1 b)) :
    IntegrableOn (fun x => deriv g x * primeSquareDiscrepancy x) (Icc 1 b) := by
  have hl : ContinuousOn Real.log (Icc 1 b) := by
    intro x hx
    exact (Real.continuousAt_log (by linarith [hx.1])).continuousWithinAt
  have hp := integrableOn_mul_sum_Icc primeSquareWeight (m := 0)
    (by norm_num : (0 : ℝ) ≤ 1) hg'.integrableOn_Icc
  have hi := hp.sub (hg'.mul hl).integrableOn_Icc
  convert hi using 1
  ext x
  simp only [primeSquareDiscrepancy, primeReciprocalLogSum, Pi.sub_apply, Pi.mul_apply]
  ring

/-- Exact prime-square main integral and arithmetic discrepancy remainder.
This is partial summation in the ordinary coordinate x, before x = exp t.
The coefficient -2 and the sign +2 of the remainder are exact. -/
theorem primeSquareCutoff_exact_remainder (c : ℝ → ℝ) (R : ℝ) {b : ℝ}
    (hb : 1 ≤ b)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x)
    (hcd : ContinuousOn (deriv (fun x => c (2 * Real.log x / R))) (Icc 1 b)) :
    primeSquareCutoff c R b =
      -2 * c (2 * Real.log b / R) * primeSquareDiscrepancy b
      -2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x)
      +2 * ∫ x in Ioc 1 b, deriv (fun x => c (2 * Real.log x / R)) x *
        primeSquareDiscrepancy x := by
  let g : ℝ → ℝ := fun x => c (2 * Real.log x / R)
  have hl : ContinuousOn Real.log (Icc 1 b) := by
    intro x hx
    exact (Real.continuousAt_log (by linarith [hx.1])).continuousWithinAt
  have hiL : IntegrableOn (fun x => deriv g x * Real.log x) (Ioc 1 b) :=
    (hcd.mul hl).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiE : IntegrableOn (fun x => deriv g x * primeSquareDiscrepancy x) (Ioc 1 b) :=
    (integrable_primeSquareDiscrepancy_mul hcd).mono_set Ioc_subset_Icc_self
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 b) :=
    continuousOn_id.inv₀ (by intro x hx; change x ≠ 0; linarith [hx.1])
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := Real.log) (u' := deriv g) (v' := fun x => x⁻¹)
    (a := 1) (b := b)
    (by simpa only [uIcc_of_le hb] using fun x hx => (hd x hx).hasDerivAt)
    (by
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact Real.hasDerivAt_log (by linarith [hx.1]))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr hcd.integrableOn_Icc)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr hinv.integrableOn_Icc)
  simp only [intervalIntegral.integral_of_le hb, Real.log_one, mul_zero, sub_zero,
    ← div_eq_mul_inv] at hparts
  have hsplit :
      (∫ x in Ioc 1 b, deriv g x * primeReciprocalLogSum x) =
      (∫ x in Ioc 1 b, deriv g x * Real.log x) +
      (∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x) := by
    rw [← integral_add hiL hiE]
    congr 1
    ext x
    simp only [primeSquareDiscrepancy]
    ring
  have hs := primeSquareCutoff_partial_summation c R b hd hcd.integrableOn_Icc
  change primeSquareCutoff c R b =
    -2 * g b * primeReciprocalLogSum b +
      2 * ∫ x in Ioc 1 b, deriv g x * primeReciprocalLogSum x at hs
  rw [hsplit] at hs
  change primeSquareCutoff c R b =
    -2 * g b * primeSquareDiscrepancy b -
    2 * (∫ x in Ioc 1 b, g x / x) +
    2 * ∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x
  rw [hparts, hs]
  unfold primeSquareDiscrepancy
  ring

/-- The same exact formula with a vanishing upper boundary. -/
theorem primeSquareCutoff_exact_remainder_of_boundary_zero (c : ℝ → ℝ) (R : ℝ)
    {b : ℝ} (hb : 1 ≤ b)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x)
    (hcd : ContinuousOn (deriv (fun x => c (2 * Real.log x / R))) (Icc 1 b))
    (hz : c (2 * Real.log b / R) = 0) :
    primeSquareCutoff c R b =
      -2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x)
      +2 * ∫ x in Ioc 1 b, deriv (fun x => c (2 * Real.log x / R)) x *
        primeSquareDiscrepancy x := by
  simpa only [hz, mul_zero, zero_mul, zero_sub, neg_mul] using
    primeSquareCutoff_exact_remainder c R hb hd hcd

/-- C¹ discrepancy control gives a quantitative error for the exact arithmetic sum.
The bound on the actual prime discrepancy is an explicit hypothesis here;
this declaration does not claim a formalized Mertens theorem. -/
theorem abs_primeSquareCutoff_remainder_le (c : ℝ → ℝ) (R : ℝ) {b B : ℝ}
    (hb : 1 ≤ b)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x)
    (hcd : ContinuousOn (deriv (fun x => c (2 * Real.log x / R))) (Icc 1 b))
    (hz : c (2 * Real.log b / R) = 0)
    (hB : ∀ x ∈ Ioc 1 b, |primeSquareDiscrepancy x| ≤ B) :
    |primeSquareCutoff c R b + 2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x)| ≤
      2 * B * ∫ x in Ioc 1 b, |deriv (fun x => c (2 * Real.log x / R)) x| := by
  let g : ℝ → ℝ := fun x => c (2 * Real.log x / R)
  have hi : IntegrableOn (deriv g) (Ioc 1 b) :=
    hcd.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiE : IntegrableOn (fun x => deriv g x * primeSquareDiscrepancy x) (Ioc 1 b) :=
    (integrable_primeSquareDiscrepancy_mul hcd).mono_set Ioc_subset_Icc_self
  have hrem :
      |∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x| ≤
      B * ∫ x in Ioc 1 b, |deriv g x| := by
    calc
      |∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x| ≤
          ∫ x in Ioc 1 b, |deriv g x * primeSquareDiscrepancy x| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => deriv g x * primeSquareDiscrepancy x)
      _ ≤ ∫ x in Ioc 1 b, B * |deriv g x| := by
        apply integral_mono_ae hiE.abs (hi.abs.const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [abs_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg _)
      _ = B * ∫ x in Ioc 1 b, |deriv g x| := integral_const_mul _ _
  rw [primeSquareCutoff_exact_remainder_of_boundary_zero c R hb hd hcd hz]
  have heq : -2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x) +
      2 * (∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x) +
      2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x) =
      2 * (∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x) := by ring
  change |(-2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x) +
      2 * (∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x) +
      2 * (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x))| ≤ _
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2 * |∫ x in Ioc 1 b, deriv g x * primeSquareDiscrepancy x| ≤
      2 * (B * ∫ x in Ioc 1 b, |deriv g x|) :=
        mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ = _ := by ring

/-- The exact change of variables for the prime-square main integral. -/
theorem primeSquare_main_integral_scale (c : ℝ → ℝ) (hc : Continuous c)
    {R b : ℝ} (hR : R ≠ 0) (hb : 1 ≤ b) :
    (∫ x in Ioc 1 b, c (2 * Real.log x / R) / x) =
      R / 2 * ∫ s in (0 : ℝ)..(2 * Real.log b / R), c s := by
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc 1 b) := by
    rw [uIcc_of_le hb]
    exact continuousOn_id.inv₀ (by intro x hx; change x ≠ 0; linarith [hx.1])
  have hs := intervalIntegral.integral_comp_mul_deriv
    (f := fun x => 2 * Real.log x / R) (f' := fun x => 2 * x⁻¹ / R) (g := c)
    (a := 1) (b := b)
    (by
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact ((Real.hasDerivAt_log (by linarith [hx.1])).const_mul 2).div_const R)
    ((hinv.const_mul 2).div_const R) hc
  have heq : (∫ x in (1 : ℝ)..b, (c ∘ (fun x => 2 * Real.log x / R)) x *
      (2 * x⁻¹ / R)) =
      (2 / R) * ∫ x in (1 : ℝ)..b, c (2 * Real.log x / R) / x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    simp only [Function.comp_apply]
    ring
  rw [heq] at hs
  simp only [Real.log_one, mul_zero, zero_div, intervalIntegral.integral_of_le hb] at hs
  rw [← hs]
  field_simp

/-- Chain rule with the exact square displacement and scaling. -/
theorem hasDerivAt_primeSquareProfile (c : ℝ → ℝ) (hc : Differentiable ℝ c)
    (R : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => c (2 * Real.log y / R))
      ((2 / R) * deriv c (2 * Real.log x / R) / x) x := by
  have h : HasDerivAt (fun y => c (2 * Real.log y / R))
      (deriv c (2 * Real.log x / R) * (2 * x⁻¹ / R)) x :=
    (hc (2 * Real.log x / R)).hasDerivAt.comp x
      (((Real.hasDerivAt_log hx).const_mul 2).div_const R)
  have heq : (2 / R) * deriv c (2 * Real.log x / R) / x =
      deriv c (2 * Real.log x / R) * (2 * x⁻¹ / R) := by ring
  rw [heq]
  exact h

/-- A C¹ profile gives a C¹ logarithmically scaled profile away from zero. -/
theorem continuousOn_deriv_primeSquareProfile (c : ℝ → ℝ)
    (hc : Differentiable ℝ c) (hc' : Continuous (deriv c)) (R b : ℝ) :
    ContinuousOn (deriv (fun x => c (2 * Real.log x / R))) (Icc 1 b) := by
  have hl : ContinuousOn Real.log (Icc 1 b) := by
    intro x hx
    exact (Real.continuousAt_log (by linarith [hx.1])).continuousWithinAt
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 b) :=
    continuousOn_id.inv₀ (by intro x hx; change x ≠ 0; linarith [hx.1])
  have hcont : ContinuousOn
      (fun x => ((2 / R) * deriv c (2 * Real.log x / R)) * x⁻¹) (Icc 1 b) :=
    ((hc'.comp_continuousOn ((hl.const_mul 2).div_const R)).const_mul (2 / R)).mul hi
  apply hcont.congr
  intro x hx
  simpa only [div_eq_mul_inv] using
    (hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).deriv

/-- Exact prime-square identity at the support cutoff.
This theorem applies to any C¹ profile vanishing for s ≥ 1. It retains
the actual prime discrepancy and does not assume Mertens or an asymptotic.
The remainder is written in x = exp(t) coordinates. -/
theorem primeSquareSector_exact_remainder (c : ℝ → ℝ)
    (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hsupp : ∀ s, 1 ≤ s → c s = 0) {R : ℝ} (hR : 0 < R) :
    primeSquareSector c R =
      -R * (∫ s in (0 : ℝ)..1, c s) +
      (4 / R) * ∫ x in Ioc 1 (Real.exp (R / 2)),
        deriv c (2 * Real.log x / R) * primeSquareDiscrepancy x / x := by
  let b := Real.exp (R / 2)
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by positivity)
  have hlog : 2 * Real.log b / R = 1 := by
    simp only [b, Real.log_exp]
    field_simp
  have hd : ∀ x ∈ Icc 1 b,
      DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x := by
    intro x hx
    exact (hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).differentiableAt
  have hcd := continuousOn_deriv_primeSquareProfile c hc hc' R b
  rw [primeSquareSector_eq_cutoff c hR hsupp (le_refl _)]
  have hs := primeSquareCutoff_exact_remainder_of_boundary_zero c R hb hd hcd
    (by rw [hlog]; exact hsupp 1 le_rfl)
  have hm := primeSquare_main_integral_scale c hc.continuous hR.ne' hb
  rw [hlog] at hm
  rw [hs, hm]
  have heq :
      (∫ x in Ioc 1 b, deriv (fun x => c (2 * Real.log x / R)) x *
        primeSquareDiscrepancy x) =
      (2 / R) * ∫ x in Ioc 1 b,
        deriv c (2 * Real.log x / R) * primeSquareDiscrepancy x / x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [(hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).deriv]
    ring
  rw [heq]
  ring

/-- Total variation of the logarithmically scaled profile is unchanged. -/
theorem primeSquareProfile_variation (c : ℝ → ℝ)
    (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    {R : ℝ} (hR : 0 < R) :
    (∫ x in Ioc 1 (Real.exp (R / 2)),
      |deriv (fun x => c (2 * Real.log x / R)) x|) =
      ∫ s in (0 : ℝ)..1, |deriv c s| := by
  let b := Real.exp (R / 2)
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by positivity)
  have hlog : 2 * Real.log b / R = 1 := by
    simp only [b, Real.log_exp]
    field_simp
  have heq :
      (∫ x in Ioc 1 b, |deriv (fun x => c (2 * Real.log x / R)) x|) =
      (2 / R) * ∫ x in Ioc 1 b, |deriv c (2 * Real.log x / R)| / x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [(hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).deriv,
      abs_div, abs_mul, abs_of_pos (div_pos (by norm_num) hR),
      abs_of_pos (by linarith [hx.1] : 0 < x)]
    ring
  rw [heq, primeSquare_main_integral_scale (fun s => |deriv c s|) hc'.abs hR.ne' hb,
    hlog]
  field_simp

/-- Uniform discrepancy and fixed profile variation bound the exact prime-square
remainder independently of R. The prime discrepancy bound is an explicit
arithmetic hypothesis, not a claimed proof of Mertens. -/
theorem abs_primeSquareSector_remainder_le (c : ℝ → ℝ)
    (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hsupp : ∀ s, 1 ≤ s → c s = 0) {R B : ℝ} (hR : 0 < R)
    (hB : ∀ x ∈ Ioc 1 (Real.exp (R / 2)), |primeSquareDiscrepancy x| ≤ B) :
    |primeSquareSector c R + R * (∫ s in (0 : ℝ)..1, c s)| ≤
      2 * B * ∫ s in (0 : ℝ)..1, |deriv c s| := by
  let b := Real.exp (R / 2)
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by positivity)
  have hlog : 2 * Real.log b / R = 1 := by
    simp only [b, Real.log_exp]
    field_simp
  have hd : ∀ x ∈ Icc 1 b,
      DifferentiableAt ℝ (fun x => c (2 * Real.log x / R)) x := by
    intro x hx
    exact (hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).differentiableAt
  have hcd := continuousOn_deriv_primeSquareProfile c hc hc' R b
  have h := abs_primeSquareCutoff_remainder_le c R hb hd hcd
    (by rw [hlog]; exact hsupp 1 le_rfl) hB
  rw [primeSquare_main_integral_scale c hc.continuous hR.ne' hb, hlog,
    primeSquareProfile_variation c hc hc' hR] at h
  rw [primeSquareSector_eq_cutoff c hR hsupp (le_refl _)]
  dsimp [b] at h
  have heq : 2 * (R / 2 * ∫ s in (0 : ℝ)..1, c s) =
      R * ∫ s in (0 : ℝ)..1, c s := by ring
  rw [heq] at h
  exact h

end RiemannResearch.RH

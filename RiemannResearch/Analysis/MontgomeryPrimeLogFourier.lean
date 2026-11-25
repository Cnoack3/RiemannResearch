import RiemannResearch.RH.WeilExplicitFormula.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The prime-power probe at the zero-spacing scale

Mertens' first formula (Montgomery and Vaughan, *Multiplicative Number Theory I*,
§2.2) bounds the distribution function of the positive logarithmic prime-power
weights. Finite summation by parts on the unit interval gives a quantitative
Fourier transform estimate with explicit dependence on frequency.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace

/-- The prescribed positive prime-power weights, on the logarithmic frequency scale. -/
def primeFourierProbe (T u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T⌋₊,
    ((ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I *
        ((Real.log n / Real.log T : ℝ) : ℂ))

/-- Fourier transform of uniform mass on the logarithmic frequency interval. -/
def primeContinuumProbe (u : ℝ) : ℂ :=
  ∫ v : ℝ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I * (v : ℂ))

/-- Inclusive logarithmic distribution of the prescribed prime-power mass. -/
def primeLogCDF (T v : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊T ^ v⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) / Real.log T

theorem monotone_primeLogCDF {T : ℝ} (hT : 1 < T) : Monotone (primeLogCDF T) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Real.log_pos hT).le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn0, hna⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn0,
      hna.trans (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hT.le hab))⟩
  · exact fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

theorem measurable_primeLogCDF {T : ℝ} (hT : 1 < T) : Measurable (primeLogCDF T) :=
  (monotone_primeLogCDF hT).measurable

theorem primeLogCDF_error {T : ℝ} (hT : 1 < T) {v : ℝ} (hv : 0 ≤ v) :
    |primeLogCDF T v - v| ≤ (Real.log 4 + 4) / Real.log T := by
  have hL := Real.log_pos hT
  have hm := Zeta23.Cheb.mertensFirst (Real.one_le_rpow hT.le hv)
  rw [Real.log_rpow (zero_lt_one.trans hT)] at hm
  let s : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊T ^ v⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
  change |s / Real.log T - v| ≤ _
  rw [show s / Real.log T - v = (s - v * Real.log T) / Real.log T by field_simp [hL.ne'],
    abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hm hL.le

/-- The interval before the first prime power gives an obstruction to uniform
little-o improvement of Mertens' discrepancy on the scaled unit interval. -/
theorem primeLogCDF_first_interval {T x : ℝ} (hT : 1 < T) (hx : 1 < x) (hx2 : x < 2) :
    primeLogCDF T (Real.log x / Real.log T) = 0 := by
  have hp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have he : T ^ (Real.log x / Real.log T) = x := by
    rw [Real.rpow_def_of_pos hp, show Real.log T * (Real.log x / Real.log T) = Real.log x by
      field_simp [hL.ne'], Real.exp_log (zero_lt_one.trans hx)]
  have hfloor : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith : 0 ≤ x)).mpr (by
    push_cast
    exact ⟨hx.le, by linarith⟩)
  simp [primeLogCDF, he, hfloor, Nat.Ioc_succ_singleton]

theorem primeLogCDF_discrepancy_witness {T x : ℝ} (hT : 2 ≤ T) (hx : 1 < x) (hx2 : x < 2) :
    ∃ v ∈ Set.Icc (0 : ℝ) 1, |primeLogCDF T v - v| * Real.log T = Real.log x := by
  have hT1 : 1 < T := by linarith
  have hL := Real.log_pos hT1
  have hv : 0 ≤ Real.log x / Real.log T := div_nonneg (Real.log_nonneg hx.le) hL.le
  refine ⟨_, ⟨hv, (div_le_iff₀ hL).mpr ?_⟩, ?_⟩
  · rw [one_mul]
    exact Real.log_le_log (zero_lt_one.trans hx) (hx2.le.trans hT)
  · rw [primeLogCDF_first_interval hT1 hx hx2, zero_sub, abs_neg, abs_of_nonneg hv,
      div_mul_cancel₀ _ hL.ne']

private def primeLogWeight (T : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T

private def atomCDF (s : Finset ℕ) (x w : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ n ∈ s, if x n ≤ v then w n else 0

private theorem truncated_atom_integral {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (g : ℝ → ℂ) :
    (∫ v in (0 : ℝ)..1, (Set.Ici z).indicator g v) = ∫ v in z..1, g v := by
  have he : Set.Icc (0 : ℝ) 1 ∩ Set.Ici z = Set.Icc z 1 := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hz.1.trans h.1, h.2⟩, h.1⟩⟩
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Ici, he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hz.2]

/-- Finite summation by parts for C¹ complex tests, with the inclusive distribution
function. This proof also applies to signed weights. -/
private theorem finite_cdf_identity (s : Finset ℕ) (x w : ℕ → ℝ)
    (hx : ∀ n ∈ s, x n ∈ Set.Icc (0 : ℝ) 1)
    (f g : ℝ → ℂ) (hg : Continuous g) (hd : ∀ v, HasDerivAt f (g v) v)
    : (∑ n ∈ s, (w n : ℂ) * f (x n)) - (∫ v in (0 : ℝ)..1, f v) =
      ((atomCDF s x w 1 - 1 : ℝ) : ℂ) * f 1 -
        ∫ v in (0 : ℝ)..1, ((atomCDF s x w v - v : ℝ) : ℂ) * g v := by
  classical
  let D := atomCDF s x w
  let terms := fun n (v : ℝ) => (Set.Ici (x n)).indicator (fun t => (w n : ℂ) * g t) v
  have hterm (n : ℕ) : IntervalIntegrable (terms n) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((continuous_const.mul hg).intervalIntegrable (0 : ℝ) 1).1.indicator measurableSet_Ici
  have hsum (v : ℝ) : (∑ n ∈ s, terms n v) = (D v : ℂ) * g v := by
    dsimp only [D, atomCDF]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : x n ≤ v <;> simp [terms, Set.indicator, h]
  have hintD : IntervalIntegrable (fun v => (D v : ℂ) * g v) volume 0 1 := by
    have he : (∑ n ∈ s, terms n) = fun v => (D v : ℂ) * g v := by
      funext v
      simpa only [Finset.sum_apply] using hsum v
    rw [← he]
    exact IntervalIntegrable.sum s (fun n _ => hterm n)
  have hidentity : (∫ v in (0 : ℝ)..1, (D v : ℂ) * g v) =
      ∑ n ∈ s, (w n : ℂ) * (f 1 - f (x n)) := by
    calc
      _ = ∫ v in (0 : ℝ)..1, ∑ n ∈ s, terms n v :=
        intervalIntegral.integral_congr fun v _ => (hsum v).symm
      _ = ∑ n ∈ s, ∫ v in (0 : ℝ)..1, terms n v :=
        intervalIntegral.integral_finsetSum (fun n _ => hterm n)
      _ = _ := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [show (∫ v in (0 : ℝ)..1, terms n v) =
          ∫ v in (x n)..1, (w n : ℂ) * g v from truncated_atom_integral (hx n hn) _,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
            (hg.intervalIntegrable _ _)]
  have htotal : D 1 = ∑ n ∈ s, w n :=
    Finset.sum_congr rfl fun n hn => if_pos (hx n hn).2
  have hid (v : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) v := by
    convert (Complex.ofRealCLM.hasDerivAt (x := v)) using 1 <;> rfl
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun v => (hd v).continuousAt
  have hxg : Continuous (fun v : ℝ => (v : ℂ) * g v) := Complex.continuous_ofReal.mul hg
  have hprod : (∫ v in (0 : ℝ)..1, f v) + (∫ v in (0 : ℝ)..1, (v : ℂ) * g v) = f 1 := by
    rw [← intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hxg.intervalIntegrable _ _)]
    have hp (v : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) * f t) (f v + (v : ℂ) * g v) v := by
      simpa only [one_mul] using (hid v).fun_mul (hd v)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hp v)
        ((hf.add hxg).intervalIntegrable _ _)]
    simp
  have hsum' : (∑ n ∈ s, (w n : ℂ) * f (x n)) =
      (D 1 : ℂ) * f 1 - ∫ v in (0 : ℝ)..1, (D v : ℂ) * g v := by
    rw [hidentity, htotal, Complex.ofReal_sum, Finset.sum_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sub_sub_cancel]
  rw [hsum']
  simp_rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul]
  rw [intervalIntegral.integral_sub hintD (hxg.intervalIntegrable _ _)]
  linear_combination -hprod

private theorem finite_cdf_error (s : Finset ℕ) (x w : ℕ → ℝ)
    (hx : ∀ n ∈ s, x n ∈ Set.Icc (0 : ℝ) 1)
    (f g : ℝ → ℂ) (hg : Continuous g) (hd : ∀ v, HasDerivAt f (g v) v)
    (E K : ℝ) (hE : ∀ v ∈ Set.Icc (0 : ℝ) 1, |atomCDF s x w v - v| ≤ E)
    (hgK : ∀ v, ‖g v‖ ≤ K) (hf1 : ‖f 1‖ ≤ 1) :
    ‖(∑ n ∈ s, (w n : ℂ) * f (x n)) - ∫ v in (0 : ℝ)..1, f v‖ ≤ E * (1 + K) := by
  let D := atomCDF s x w
  have hdiff := finite_cdf_identity s x w hx f g hg hd
  have hi : ‖∫ v in (0 : ℝ)..1, ((D v - v : ℝ) : ℂ) * g v‖ ≤ E * K := by
    have hb (v : ℝ) (hv : v ∈ Set.uIoc (0 : ℝ) 1) :
        ‖((D v-v : ℝ) : ℂ) * g v‖ ≤ E * K := by
      rw [Set.uIoc_of_le zero_le_one] at hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hE v ⟨hv.1.le, hv.2⟩) (hgK v) (norm_nonneg _)
        ((abs_nonneg _).trans (hE v ⟨hv.1.le, hv.2⟩))
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hE1 := hE 1 ⟨zero_le_one, le_rfl⟩
  rw [hdiff]
  calc
    _ ≤ ‖((D 1 - 1 : ℝ) : ℂ) * f 1‖ + _ := norm_sub_le _ _
    _ ≤ E * 1 + E * K := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hE1 hf1 (norm_nonneg _) ((abs_nonneg _).trans hE1)) hi
    _ = _ := by ring

private theorem atomCDF_prime {T : ℝ} (hT : 1 < T) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    atomCDF (Finset.Ioc 0 ⌊T⌋₊) (fun n => Real.log n / Real.log T) (primeLogWeight T) v =
      (∑ n ∈ Finset.Ioc 0 ⌊T ^ v⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) / Real.log T := by
  classical
  have hp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hvT : T ^ v ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT.le hv.2
  have he : (Finset.Ioc 0 ⌊T⌋₊).filter (fun n : ℕ => Real.log n / Real.log T ≤ v) =
      Finset.Ioc 0 ⌊T ^ v⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    by_cases hn : 0 < n
    · have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
      have hcut : Real.log n / Real.log T ≤ v ↔ n ≤ ⌊T ^ v⌋₊ := by
        rw [div_le_iff₀ hL, Real.log_le_iff_le_exp hnp, mul_comm v,
          ← Real.rpow_def_of_pos hp, Nat.le_floor_iff (Real.rpow_nonneg hp.le _)]
      exact ⟨fun h => ⟨hn, hcut.mp h.2⟩,
        fun h => ⟨⟨hn, h.2.trans (Nat.floor_le_floor hvT)⟩, hcut.mpr h.2⟩⟩
    · simp [hn]
  unfold atomCDF
  rw [← Finset.sum_filter, he, Finset.sum_div]
  rfl

private theorem cdf_prime_error {T : ℝ} (hT : 1 < T) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |atomCDF (Finset.Ioc 0 ⌊T⌋₊) (fun n => Real.log n / Real.log T) (primeLogWeight T) v - v|
      ≤ (Real.log 4 + 4) / Real.log T := by
  rw [atomCDF_prime hT hv]
  exact primeLogCDF_error hT hv.1

private theorem logScale_mem {T : ℝ} (hT : 1 < T) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊T⌋₊) :
    Real.log n / Real.log T ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hn0, hnT⟩ := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn0
  have hnT' := (Nat.cast_le.mpr hnT : (n : ℝ) ≤ ⌊T⌋₊)
  have hL := Real.log_pos hT
  refine ⟨div_nonneg (Real.log_nonneg hn1) hL.le, (div_le_iff₀ hL).mpr ?_⟩
  rw [one_mul]
  exact Real.log_le_log (zero_lt_one.trans_le hn1) (hnT'.trans (Nat.floor_le (by linarith)))

private theorem norm_phase (k v : ℝ) :
    ‖Complex.exp ((k : ℂ) * Complex.I * (v : ℂ))‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem probePhase_hasDeriv (c : ℂ) (v : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (c * Complex.exp (c * (v : ℂ))) v := by
  have hi : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) v := by
    convert (Complex.ofRealCLM.hasDerivAt (x := v)) using 1 <;> rfl
  simpa [mul_comm] using (hi.const_mul c).cexp

/-- Exact endpoint and integral contributions to the arithmetic Fourier error. -/
theorem primeFourierProbe_sub_eq_cdf {T : ℝ} (hT : 1 < T) (u : ℝ) :
    primeFourierProbe T u - primeContinuumProbe u =
      ((primeLogCDF T 1 - 1 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) -
        (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) *
          ∫ v in (0 : ℝ)..1, ((primeLogCDF T v - v : ℝ) : ℂ) *
            Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I * (v : ℂ)) := by
  let s := Finset.Ioc 0 ⌊T⌋₊
  let x := fun n : ℕ => Real.log n / Real.log T
  let c : ℂ := ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I
  let f := fun v : ℝ => Complex.exp (c * (v : ℂ))
  let g := fun v : ℝ => c * f v
  have hf := finite_cdf_identity s x (primeLogWeight T) (fun _ hn => logScale_mem hT hn)
    f g (by dsimp [g, f]; fun_prop) (probePhase_hasDeriv c)
  rw [show primeFourierProbe T u - primeContinuumProbe u =
      (∑ n ∈ s, (primeLogWeight T n : ℂ) * f (x n)) - (∫ v in (0 : ℝ)..1, f v) by rfl, hf]
  rw [atomCDF_prime hT (v := 1) ⟨zero_le_one, le_rfl⟩]
  change ((primeLogCDF T 1 - 1 : ℝ) : ℂ) * f 1 - _ =
    ((primeLogCDF T 1 - 1 : ℝ) : ℂ) * Complex.exp c - c * ∫ v in (0 : ℝ)..1,
      ((primeLogCDF T v - v : ℝ) : ℂ) * f v
  rw [show f 1 = Complex.exp c by simp [f], ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le zero_le_one] at hv
  change ((atomCDF (Finset.Ioc 0 ⌊T⌋₊) (fun n : ℕ => Real.log n / Real.log T)
    (primeLogWeight T) v - v : ℝ) : ℂ) * g v = c * (((primeLogCDF T v - v : ℝ) : ℂ) * f v)
  rw [atomCDF_prime hT hv]
  change ((primeLogCDF T v - v : ℝ) : ℂ) * (c * f v) =
    c * (((primeLogCDF T v - v : ℝ) : ℂ) * f v)
  ring

/-- A moving-frequency estimate. No zero-density or zeta-zero premise enters here. -/
theorem primeFourierProbe_error {T : ℝ} (hT : 1 < T) (u : ℝ) :
    ‖primeFourierProbe T u - primeContinuumProbe u‖ ≤
      ((Real.log 4 + 4) / Real.log T) * (1 + 2 * Real.pi * |u|) := by
  let k := 2 * Real.pi * u
  let c : ℂ := (k : ℂ) * Complex.I
  let f := fun v : ℝ => Complex.exp (c * (v : ℂ))
  let g := fun v : ℝ => c * f v
  have hc : ‖c‖ = 2 * Real.pi * |u| := by
    simp [c, k, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  have hd (v : ℝ) : HasDerivAt f (g v) v := probePhase_hasDeriv c v
  apply finite_cdf_error (Finset.Ioc 0 ⌊T⌋₊)
    (fun n => Real.log n / Real.log T) (primeLogWeight T) (fun _ hn => logScale_mem hT hn)
    f g (by dsimp [g, f]; fun_prop) hd
  · exact fun v hv => cdf_prime_error hT hv
  · intro v
    rw [show ‖g v‖ = ‖c‖ * ‖f v‖ by exact norm_mul _ _, hc, show ‖f v‖ = 1 from norm_phase k v, mul_one]
  · exact (norm_phase k 1).le

/-- Total mass bounds the modulus even when the frequency varies without restriction. -/
theorem norm_primeFourierProbe_le {T : ℝ} (hT : 1 < T) (u : ℝ) :
    ‖primeFourierProbe T u‖ ≤ 1 + (Real.log 4 + 4) / Real.log T := by
  let s := Finset.Ioc 0 ⌊T⌋₊
  have hsum : atomCDF s (fun n => Real.log n / Real.log T) (primeLogWeight T) 1 =
      ∑ n ∈ s, primeLogWeight T n := Finset.sum_congr rfl fun n hn => if_pos (logScale_mem hT hn).2
  have hm := cdf_prime_error hT (v := 1) ⟨zero_le_one, le_rfl⟩
  rw [hsum] at hm
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ n ∈ s, primeLogWeight T n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      have hw : 0 ≤ primeLogWeight T n :=
        div_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
          (Real.log_pos hT).le
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg hw
    _ ≤ _ := by linarith [(abs_le.mp hm).2]

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeFourierProbe_sub_eq_cdf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeFourierProbe_sub_eq_cdf

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeFourierProbe_error' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeFourierProbe_error

end RiemannResearch.Analysis.MontgomeryPrimeTrace

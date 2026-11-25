import RiemannResearch.Analysis.DyadicZeroWassersteinLaws
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Sharp Wasserstein rate for actual dyadic zeta-zero coordinates

The analytic inputs are stated as propositions, so no project-local axiom is
introduced. Goldston, *Notes on Pair Correlation of Zeros and Prime Numbers*,
Theorem 8, equation (10.5), https://arxiv.org/abs/math/0412313, gives the
moment premise `SelbergSixteenth` at k = 8 and T = 2U. In the
right-continuous convention N minus its smooth main term differs from the
usual S by a bounded function almost everywhere. The two endpoint bounds
follow from Riemann--von Mangoldt and the trivial bound for the short sum.

`JacksonAtDegree` is a zero-independent specialization of positive Jackson
convolution on the finite torus and ordinary one-dimensional integration by
parts for its height coefficients. See B. Borda, *Berry--Esseen smoothing
inequality for the Wasserstein metric on compact Lie groups*, J. Fourier
Anal. Appl. 27 (2021), https://arxiv.org/abs/2005.04925, §3, for positive
finite Fourier smoothing with a first moment O(1/H). In the torus case use
the product of normalized squares of Fejér kernels. Convolution in the angle
alone preserves each Haar slice. For a bounded Lipschitz slice function its
coefficient is bounded and Lipschitz in s, uniformly in the mode. Abel
summation gives (2 sup |a| + Lip(a))/|v| for its integral at v ≠ 0. With
degree H = floor(c_P log U), the count of modes is at most (2H+1)^|P| and
both products of prime powers are at most exp(H sum log p). Choosing c_P
small puts all three below the cutoff (2U)^(1/8) for sufficiently large U.
Reflect the height evenly onto the circle of period two and convolve there
too. Evenness and mass one preserve the height integral on [0,1]. The resulting
trace is smooth. Positive convolution preserves its Lipschitz bound.
`tensorJackson_of_degree` verifies the degree choice for each large height.
The first-moment entry only requires approximation at the chosen height for one P.
Classical positive approximation at arbitrary degree supplies this input.
The summation over the resulting modes and outside primes is proved below.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open ActualZeroOrdinate PrimeTorusHaar ZeroOrdinate MontgomeryLocalMass

def shortPrimitive (U t : ℝ) : ℝ := countMain t -
  ∑ q ∈ primesTo (bandwidth U), Real.sin (t * Real.log q) / (Real.pi * Real.sqrt q)

def shortSlope (U t : ℝ) : ℝ := slope t -
  ∑ q ∈ primesTo (bandwidth U), primeWeight q * Real.cos (t * Real.log q)

def residual (U t : ℝ) : ℝ := (Ncount 0 t : ℝ) - shortPrimitive U t

def ShortPrimePrimitive : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in atTop,
  |residual U U| + |residual U (2 * U)| + (∫ t in U..2 * U, |residual U t|) ≤ C * U

/-- Dyadic sixteenth-moment version of Selberg's short-prime theorem, in
the cumulative-count convention. The additive bounded Stirling correction
does not affect a uniform sixteenth moment. -/
def SelbergSixteenth : Prop := ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ U : ℝ in atTop,
  IntervalIntegrable (fun t => |residual U t|) volume U (2 * U) ∧
  IntervalIntegrable (fun t => |residual U t| ^ 16) volume U (2 * U) ∧
  (∫ t in U..2 * U, |residual U t| ^ 16) ≤ D * U

/-- Only the normalized first absolute moment of the counting residual is needed. -/
def DyadicPrimitiveFirstMoment : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ U : ℝ in atTop,
    (∫ t in U..2 * U, |residual U t|) ≤ D * U

/-- Riemann–von Mangoldt controls both endpoints; the average alone suffices. -/
theorem shortPrimePrimitive_of_firstMoment (hs : DyadicPrimitiveFirstMoment) :
    ShortPrimePrimitive := by
  obtain ⟨C, hC, hR⟩ := actual_cumulativeRvM
  obtain ⟨T, hT⟩ := eventually_atTop.1 hR
  obtain ⟨D, hD, hS⟩ := hs
  refine ⟨4 * C + 4 + D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (2 : ℝ), hS] with U hut hu hsu
  have hul : U ≤ 2 * U := by linarith
  have hx : (bandwidth U : ℝ) ≤ 2 * U := by
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ 2 * U) _)).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 2 * U by linarith) (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hq : (primesTo (bandwidth U)).card ≤ bandwidth U :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hend (t : ℝ) (ht : t ∈ Icc U (2 * U)) : |residual U t| ≤ (2 * C + 2) * U := by
    have he := hT t (hut.trans ht.1)
    have hl := Real.log_le_sub_one_of_pos (show 0 < t by linarith [ht.1])
    have hc := mul_le_mul_of_nonneg_left (show Real.log t ≤ 2 * U by linarith [ht.2]) hC
    have hp : |∑ q ∈ primesTo (bandwidth U),
        Real.sin (t * Real.log q) / (Real.pi * Real.sqrt q)| ≤ 2 * U := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _q ∈ primesTo (bandwidth U), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq'
          have hprime := (Finset.mem_filter.mp hq').2
          have hone : (1 : ℝ) ≤ q := by exact_mod_cast hprime.one_lt.le
          have hsqrt : 1 ≤ Real.sqrt (q : ℝ) := by simpa using Real.sqrt_le_sqrt hone
          have hp : 1 ≤ Real.pi * Real.sqrt q :=
            one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) hsqrt
          rw [abs_div, abs_of_pos (zero_lt_one.trans_le hp), div_le_one (zero_lt_one.trans_le hp)]
          exact (Real.abs_sin_le_one _).trans hp
        _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : ((primesTo (bandwidth U)).card : ℝ) ≤ bandwidth U := by
            exact_mod_cast hq
          exact hcard.trans hx
    have hres : residual U t = countError t +
        ∑ q ∈ primesTo (bandwidth U), Real.sin (t * Real.log q) / (Real.pi * Real.sqrt q) := by
      unfold residual shortPrimitive countError
      ring
    rw [hres]
    apply (abs_add_le _ _).trans
    linarith
  linarith [hend U ⟨le_rfl, hul⟩, hend (2 * U) ⟨hul, le_rfl⟩]

theorem primitiveFirstMoment_of_sixteenth (hs : SelbergSixteenth) :
    DyadicPrimitiveFirstMoment := by
  obtain ⟨D, hD, hS⟩ := hs
  refine ⟨1 + D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hS] with U hu hsu
  have hul : U ≤ 2 * U := by linarith
  have hi : (∫ t in U..2 * U, |residual U t|) ≤ U + D * U := by
    have h := intervalIntegral.integral_mono_on hul hsu.1
      (intervalIntegrable_const.add hsu.2.1) (g := fun t => 1 + |residual U t| ^ 16) (by
        intro t _
        by_cases h : |residual U t| ≤ 1
        · linarith [pow_nonneg (abs_nonneg (residual U t)) 16]
        · have hp := pow_le_pow_right₀ (le_of_not_ge h) (by decide : 1 ≤ 16)
          simp only [pow_one] at hp
          linarith)
    rw [intervalIntegral.integral_add intervalIntegrable_const hsu.2.1,
      intervalIntegral.integral_const] at h
    simp only [smul_eq_mul, mul_one] at h
    linarith [hsu.2.2]
  linarith

theorem shortPrimePrimitive_of_sixteenth (hs : SelbergSixteenth) :
    ShortPrimePrimitive :=
  shortPrimePrimitive_of_firstMoment (primitiveFirstMoment_of_sixteenth hs)

/-- Positive torus smoothing of the centered critical-line slice, independent
of any zero-counting measure. Exact zero frequency is retained. -/
def TensorJackson (P : Finset ℕ) : Prop := ∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
  ∀ f : C(Space P, ℝ), Admissible P f →
    ∃ b : FourierTrace P U A, b.zeroMode = 0 ∧
      ∀ t ∈ Icc U (2 * U),
        |f (1 / 2, height U t, primeOrbit P t) - (∫ x, f x ∂nu P) - b.H t| ≤ A / Real.log U

/-- Classical positive Jackson approximation at an arbitrary degree and an
independently prescribed height. The size bound exp(B n) accommodates both
the number of modes and their prime-power numerators and denominators. This
statement has no logarithmic height rate and involves no empirical measure.
The constant is chosen separately in each fixed dimension. -/
def JacksonAtDegree (P : Finset ℕ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ n : ℕ, 0 < n → ∀ U : ℝ, 2 ≤ U →
    ∀ f : C(Space P, ℝ), Admissible P f →
    ∃ b : FourierTrace P U A ⌊Real.exp (B * (n : ℝ))⌋₊, b.zeroMode = 0 ∧
      ∀ t ∈ Icc U (2 * U),
        |f (1 / 2, height U t, primeOrbit P t) - (∫ x, f x ∂nu P) - b.H t| ≤ A / n

def PositivePrimeTorusJackson : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → JacksonAtDegree P

theorem tensorJackson_of_degree (P : Finset ℕ) (hj : JacksonAtDegree P) : TensorJackson P := by
  obtain ⟨A, B, hA, hB, hj⟩ := hj
  let D := 16 * (B + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨2 * D * A, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2 * D)]
    with U hu hl
  have up : 0 < U := by linarith
  have hlp := Real.log_pos (show 1 < U by linarith)
  let n : ℕ := ⌊Real.log U / D⌋₊
  have hratio : 2 ≤ Real.log U / D := (le_div_iff₀ hD).2 (by linarith)
  have hn : 0 < n := (Nat.le_floor_iff (by linarith : 0 ≤ Real.log U / D)).2 (by norm_num; linarith)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo : (n : ℝ) ≤ Real.log U / D := Nat.floor_le (by positivity)
  have hhi : Real.log U / D < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogn : Real.log U ≤ 2 * D * (n : ℝ) := by
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have h := (div_lt_iff₀ hD).mp hhi
    nlinarith [mul_le_mul_of_nonneg_left hn1 hD.le]
  have small : ⌊Real.exp (B * (n : ℝ))⌋₊ ≤ bandwidth U := by
    apply Nat.floor_mono
    rw [Real.rpow_def_of_pos (by linarith : 0 < 2 * U)]
    apply Real.exp_le_exp.mpr
    have hd := (le_div_iff₀ hD).mp hlo
    have hm := Real.log_le_log up (show U ≤ 2 * U by linarith)
    dsimp [D] at hd
    nlinarith
  intro f hf
  obtain ⟨b, hzero, happrox⟩ := hj n hn U hu f hf
  have hbig : A ≤ 2 * D * A := by nlinarith [mul_le_mul_of_nonneg_right hD1 hA.le]
  refine ⟨b.enlarge hbig small, hzero, ?_⟩
  intro t ht
  apply (happrox t ht).trans
  rw [div_le_div_iff₀ hnR hlp]
  nlinarith [mul_le_mul_of_nonneg_left hlogn hA.le]

theorem shortPrimitive_deriv {U t : ℝ} (ht : 0 < t) :
    HasDerivAt (shortPrimitive U) (shortSlope U t) t := by
  apply (countMain_deriv ht).sub
  apply HasDerivAt.fun_sum
  intro q hq
  have h := ((((hasDerivAt_id t).mul_const (Real.log q)).sin).div_const
    (Real.pi * Real.sqrt q))
  convert h using 1 <;> first | rfl | (try dsimp [id, primeWeight]; ring)

theorem probe_re {U v : ℝ} {H : ℝ → ℝ} (hc : Continuous H) :
    (probe U H v).re = ∫ t in U..2 * U, H t * Real.cos (t * v) := by
  have hi : IntervalIntegrable (fun t : ℝ => (H t : ℂ) * phase v t) volume U (2 * U) :=
    (by unfold phase; fun_prop : Continuous (fun t : ℝ => (H t : ℂ) * phase v t))
      |>.intervalIntegrable _ _
  calc
    _ = (∫ t in U..2 * U, ((H t : ℂ) * phase v t).re) := by
      simpa [probe] using (intervalIntegral.intervalIntegral_re hi).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [phase, Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_comm]

/-- The whole signed approximation is applied before expanding any test into
modes. This is what makes the mean error uniform on the Lipschitz unit ball. -/
theorem trace_sum_bound {P : Finset ℕ} {U A C : ℝ} (b : FourierTrace P U A)
    (hu : 2 ≤ U) (hA : 0 ≤ A) (hzero : b.zeroMode = 0)
    (hshort : |residual U U| + |residual U (2 * U)| + (∫ t in U..2 * U, |residual U t|) ≤ C * U)
    (hX : 0 < bandwidth U) (h5 : (bandwidth U : ℝ) ^ 5 ≤ 2 * U)
    (h2 : Real.log U * (bandwidth U : ℝ) ^ 2 ≤ 8 * (2 * U)) :
    |massSum U (fun ρ => b.H ρ.im)| ≤
      A * (C + (1 + |Real.log (2 * Real.pi)|) * 16 + 1 + (∑ p ∈ P, |primeWeight p|) + 2) * U := by
  have up : 0 < U := by linarith
  have hul : U ≤ 2 * U := by linarith
  have hlog : 0 < Real.log U := Real.log_pos (by linarith)
  have hsc : ContinuousOn (shortSlope U) (Icc U (2 * U)) :=
    (slope_continuous up).sub (by fun_prop)
  have habel := abel_estimate (B := shortPrimitive U) (d := shortSlope U) up
    b.derives b.continuousDerivative hsc (fun t ht => shortPrimitive_deriv (up.trans_le ht.1))
    b.boundH b.boundDerivative
  have herr : |massSum U (fun ρ => b.H ρ.im) -
      ∫ t in U..2 * U, b.H t * shortSlope U t| ≤ A * (C * U) := by
    apply habel.trans
    simpa [residual, mul_add] using mul_le_mul_of_nonneg_left hshort hA
  have hδ (t : ℝ) (ht : t ∈ Icc U (2 * U)) : |slope t - slope U| ≤ 1 := by
    have ht0 := up.trans_le ht.1
    rw [slope, slope, ← sub_div, Real.log_div ht0.ne' (by positivity),
      Real.log_div up.ne' (by positivity)]
    have hdiff : 0 ≤ Real.log t - Real.log U := sub_nonneg.mpr (Real.log_le_log up ht.1)
    have hupper := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) up.ne'] at hupper
    rw [show Real.log t - Real.log (2 * Real.pi) - (Real.log U - Real.log (2 * Real.pi)) =
      Real.log t - Real.log U by ring, abs_of_nonneg (div_nonneg hdiff (by positivity))]
    apply (div_le_iff₀ (by positivity)).2
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2), Real.pi_gt_three]
  have hslope : |slope U| ≤ (1 + |Real.log (2 * Real.pi)|) * Real.log U := by
    have hp : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hlp := Real.log_pos hp
    have hhalf : 1 / 2 ≤ Real.log U := by
      have hlow := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hu
      linarith [Real.log_two_gt_d9]
    rw [slope, Real.log_div up.ne' (zero_lt_one.trans hp).ne',
      abs_div, abs_of_pos (zero_lt_one.trans hp)]
    apply (div_le_iff₀ (zero_lt_one.trans hp)).2
    apply (abs_sub _ _).trans
    rw [abs_of_pos hlog]
    nlinarith [Real.pi_gt_three, abs_nonneg (Real.log (2 * Real.pi)),
      mul_nonneg (abs_nonneg (Real.log (2 * Real.pi))) (sub_nonneg.mpr hhalf),
      mul_nonneg (show 0 ≤ 2 * Real.pi - 2 by linarith [Real.pi_gt_three])
        (show 0 ≤ (1 + |Real.log (2 * Real.pi)|) * Real.log U by positivity)]
  have hnorm := probe_zero_error b hA hX
  rw [hzero, sub_zero] at hnorm
  have hconstant : |slope U * (probe U b.H 0).re| ≤
      (1 + |Real.log (2 * Real.pi)|) * A * (16 * U) := by
    rw [abs_mul]
    apply (mul_le_mul hslope ((Complex.abs_re_le_norm _).trans hnorm)
      (abs_nonneg _) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_left h2
      (show 0 ≤ (1 + |Real.log (2 * Real.pi)|) * A by positivity)]
  have hvar : |∫ t in U..2 * U, b.H t * (slope t - slope U)| ≤ A * U := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := U) (b := 2 * U) (C := A) (f := fun t => b.H t * (slope t - slope U)) (by
        intro t ht
        rw [uIoc_of_le hul] at ht
        rw [Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul (b.boundH t ⟨ht.1.le, ht.2⟩) (hδ t ⟨ht.1.le, ht.2⟩) (abs_nonneg _) hA)
    rw [Real.norm_eq_abs, show 2 * U - U = U by ring, abs_of_pos up] at h
    linarith
  have hid : (∫ t in U..2 * U, b.H t * shortSlope U t) =
      slope U * (probe U b.H 0).re + (∫ t in U..2 * U, b.H t * (slope t - slope U)) -
      ∑ q ∈ primesTo (bandwidth U), primeWeight q * (probe U b.H (Real.log q)).re := by
    have hv : IntervalIntegrable (fun t => b.H t * (slope t - slope U)) volume U (2 * U) :=
      (b.continuousH.continuousOn.mul ((slope_continuous up).sub continuousOn_const))
        |>.intervalIntegrable_of_Icc hul
    let F (q : ℕ) (t : ℝ) := primeWeight q * (b.H t * Real.cos (t * Real.log q))
    have hF (q : ℕ) : Continuous (F q) := by
      exact continuous_const.mul (b.continuousH.mul (by fun_prop))
    have hsum : Continuous (fun t => ∑ q ∈ primesTo (bandwidth U), F q t) :=
      continuous_finsetSum _ fun q _ => hF q
    have hconst : IntervalIntegrable (fun t => slope U * b.H t) volume U (2 * U) :=
      (continuous_const.mul b.continuousH).intervalIntegrable _ _
    calc
      _ = ∫ t in U..2 * U, (slope U * b.H t + b.H t * (slope t - slope U)) -
            ∑ q ∈ primesTo (bandwidth U), F q t := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [shortSlope, F, mul_sub, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hconst.add hv) (hsum.intervalIntegrable _ _),
          intervalIntegral.integral_add hconst hv,
          intervalIntegral.integral_finsetSum (fun q _ => (hF q).intervalIntegrable _ _)]
        simp_rw [F, intervalIntegral.integral_const_mul, probe_re b.continuousH]
        simp only [mul_zero, Real.cos_zero, mul_one]
  have hprime := prime_polynomial_bound b up.le hA
  have hprime' := hprime.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h5 hA))
  rw [hid] at herr
  have ha1 := (abs_le.mp herr)
  have ha2 := abs_le.mp hconstant
  have ha3 := abs_le.mp hvar
  have ha4 := abs_le.mp hprime'
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Total absolute horizontal displacement of the actual dyadic zero copies. -/
def DyadicHorizontalFirstMoment : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ U : ℝ in atTop,
    massSum U (fun ρ => |ρ.re - 1 / 2|) ≤ D * U

/-- Uniform control before taking the Kantorovich--Rubinstein supremum. -/
theorem uniform_test_bound_of_firstMoment (P : Finset ℕ) (hs : DyadicHorizontalFirstMoment)
    (hshort : ShortPrimePrimitive) (hj : TensorJackson P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ U : ℝ in atTop, ∀ f : C(Space P, ℝ), Admissible P f →
      |(∫ x, f x ∂mu P U) - ∫ x, f x ∂nu P| ≤ K / Real.log U := by
  obtain ⟨A, hA, hj⟩ := hj
  obtain ⟨C, hC, hshort⟩ := hshort
  obtain ⟨D, hD, hh⟩ := hs
  obtain ⟨c, B, hc, hB, hm⟩ := dyadic_mass_bounds
  let K := A * (C + (1 + |Real.log (2 * Real.pi)|) * 16 + 1 + (∑ p ∈ P, |primeWeight p|) + 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨A + (D + K) / c, by positivity, ?_⟩
  filter_upwards [hj, hshort, hh, hm, bandwidth_budget, eventually_ge_atTop (2 : ℝ)]
    with U hjU hsU hhU hmU hb hu
  have up : 0 < U := by linarith
  have hl : 0 < Real.log U := Real.log_pos (by linarith)
  have hn : 0 < mass U := lt_of_lt_of_le (by positivity) hmU.1
  intro f hf
  obtain ⟨b, hzero, happrox⟩ := hjU f hf
  let m := ∫ x, f x ∂nu P
  have htrace := trace_sum_bound b hu hA.le hzero hsU hb.1 hb.2.1 hb.2.2
  have hcopy (i : Occ U) :
      |f (coord P U i.1.val) - m - b.H i.1.val.im| ≤ |i.1.val.re - 1 / 2| + A / Real.log U := by
    let y : Space P := (1 / 2, height U i.1.val.im, primeOrbit P i.1.val.im)
    have hd : |f (coord P U i.1.val) - f y| ≤ |i.1.val.re - 1 / 2| := by
      simpa only [cost, coord, y, sub_self, abs_zero, dist_self, Finset.sum_const_zero,
        add_zero] using hf.2 (coord P U i.1.val) y
    have h := happrox i.1.val.im ⟨(occ_bounds i).1.le, (occ_bounds i).2⟩
    calc
      _ = |(f (coord P U i.1.val) - f y) + (f y - m - b.H i.1.val.im)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hd h)
  have sumE : |massSum U (fun ρ => f (coord P U ρ)) - mass U * m - massSum U (fun ρ => b.H ρ.im)| ≤
      D * U + mass U * (A / Real.log U) := by
    have hh := (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Occ U)))
      (f := fun i => f (coord P U i.1.val) - m - b.H i.1.val.im)).trans
      (Finset.sum_le_sum (fun i _ => hcopy i))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, card_windowCopies] at hh
    exact hh.trans (add_le_add hhU le_rfl)
  rw [integral_mu, show (∫ x, f x ∂nu P) = m by rfl,
    show massSum U (fun ρ => f (coord P U ρ)) / mass U - m =
      (massSum U (fun ρ => f (coord P U ρ)) - mass U * m) / mass U by field_simp [hn.ne']]
  rw [abs_div, abs_of_pos hn]
  have htot : |massSum U (fun ρ => f (coord P U ρ)) - mass U * m| ≤
      (D + K) * U + mass U * (A / Real.log U) := by
    have hab := abs_add_le
      (massSum U (fun ρ => f (coord P U ρ)) - mass U * m - massSum U (fun ρ => b.H ρ.im))
      (massSum U (fun ρ => b.H ρ.im))
    rw [sub_add_cancel] at hab
    exact hab.trans (by dsimp [K] at *; linarith)
  have hgain : (D + K) * U / mass U ≤ (D + K) * U / (c * U * Real.log U) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hmU.1
  calc
    _ ≤ ((D + K) * U + mass U * (A / Real.log U)) / mass U :=
      div_le_div_of_nonneg_right htot hn.le
    _ = (D + K) * U / mass U + A / Real.log U := by field_simp [hn.ne', hl.ne']
    _ ≤ (D + K) * U / (c * U * Real.log U) + A / Real.log U := add_le_add hgain le_rfl
    _ = (A + (D + K) / c) / Real.log U := by field_simp [hc.ne', hl.ne', up.ne'] <;> ring

theorem uniform_test_bound (P : Finset ℕ) (hs : UniformSelbergDensity (1 / 4))
    (hshort : ShortPrimePrimitive) (hj : TensorJackson P) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ U : ℝ in atTop, ∀ f : C(Space P, ℝ), Admissible P f →
      |(∫ x, f x ∂mu P U) - ∫ x, f x ∂nu P| ≤ K / Real.log U :=
  uniform_test_bound_of_firstMoment P (horizontal_sum hs) hshort hj

/-- Compact support bounds every anchored Lipschitz integral by a common constant. -/
private theorem anchored_integral_bound (P : Finset ℕ) (μ : Measure (Space P))
    [IsProbabilityMeasure μ] (hc : CompactProbabilitySupport μ) :
    ∃ C : ℝ, ∀ f : C(Space P, ℝ), Admissible P f → |∫ x, f x ∂μ| ≤ C := by
  obtain ⟨K, hK, hm⟩ := hc
  let a : Space P := (1/2, 0, 0)
  have hcont : Continuous (fun x : Space P => cost P x a) := by
    unfold cost
    fun_prop
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont.continuousOn
  have hfull : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr ((prob_compl_eq_zero_iff hK.measurableSet).2 hm)
  refine ⟨M, ?_⟩
  intro f hf
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
    filter_upwards [hfull] with x hx
    have h0 : f a = 0 := hf.1
    simpa only [Real.norm_eq_abs, h0, sub_zero] using
      (hf.2 x a).trans (hM ⟨x, hx, rfl⟩)
  simpa [Real.norm_eq_abs, Measure.real] using norm_integral_le_of_norm_le_const hb

/-- With the sum cost, every unit of horizontal displacement can be added
  to the height witness. The lower bound uses no analytic hypothesis. -/
theorem eventually_horizontal_add_height_lower (P : Finset ℕ) {c : ℝ}
    (hc : c < 3 / 4 - Real.log 2) :
    ∀ᶠ U : ℝ in atTop,
      massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U + c / Real.log U ≤
        wassersteinOne P (mu P U) (nu P) := by
  obtain ⟨a, b, ha, hb, hm⟩ := dyadic_mass_bounds
  have hh := (tendsto_order.1 (height_mean_limit P)).1 c hc
  filter_upwards [hm, hh, eventually_gt_atTop (1 : ℝ)] with U hm hh hU
  have hL : 0 < Real.log U := Real.log_pos hU
  have hpos : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  have hn : 0 < Ncount U (2*U) := by unfold mass at hpos; exact_mod_cast hpos
  let _ := mu_probability P hn
  obtain ⟨A,hA⟩ := anchored_integral_bound P _ (mu_compact P hn)
  obtain ⟨B,hB⟩ := anchored_integral_bound P _ (nu_compact P)
  have hbb : BddAbove (differences P (mu P U) (nu P)) := by
    refine ⟨A+B,?_⟩
    rintro _ ⟨g,hg,rfl⟩
    exact (abs_sub _ _).trans (add_le_add (hA g hg) (hB g hg))
  let g : C(Space P, ℝ) := ⟨fun x => x.2.1, continuous_fst.comp continuous_snd⟩
  let f : C(Space P, ℝ) := ⟨fun x => |x.1 - 1 / 2| + x.2.1, by fun_prop⟩
  have had : Admissible P f := by
    constructor
    · simp [f]
    · intro x y
      change |(|x.1 - 1 / 2| + x.2.1) - (|y.1 - 1 / 2| + y.2.1)| ≤ _
      rw [show (|x.1 - 1 / 2| + x.2.1) - (|y.1 - 1 / 2| + y.2.1) =
        (|x.1 - 1 / 2| - |y.1 - 1 / 2|) + (x.2.1-y.2.1) by ring]
      apply (abs_add_le _ _).trans
      have hab := abs_abs_sub_abs_le_abs_sub (x.1 - 1 / 2) (y.1 - 1 / 2)
      rw [show (x.1 - 1 / 2) - (y.1 - 1 / 2) = x.1-y.1 by ring] at hab
      unfold cost
      linarith only [hab, Finset.sum_nonneg (s := Finset.univ)
        (fun (p : P) _ => dist_nonneg (x := x.2.2 p) (y := y.2.2 p))]
  have target : (∫ x, f x ∂nu P) = 1 / 2 := by
    rw [← integral_nu_height P]
    simp only [nu, Measure.dirac_prod]
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable,
        integral_map (by fun_prop) (by fun_prop)]
    simp [f]
  have empirical : (∫ x, f x ∂mu P U) =
      massSum U (fun ρ => |ρ.re - 1/2|) / mass U + ∫ x, g x ∂mu P U := by
    rw [integral_mu, integral_mu]
    simp [massSum, coord, f, g, Finset.sum_add_distrib, add_div]
  have hmem : |(∫ x, f x ∂mu P U) - ∫ x, f x ∂nu P| ∈ differences P (mu P U) (nu P) :=
    ⟨f, had, rfl⟩
  apply le_trans _ (le_csSup hbb hmem)
  rw [target, empirical]
  apply le_trans _ (le_abs_self _)
  have he : c / Real.log U ≤ (∫ x, g x ∂mu P U) - 1 / 2 :=
    (div_le_iff₀ hL).2 (by
      change c ≤ ((∫ x : Space P, x.2.1 ∂mu P U) - 1 / 2) * Real.log U
      simpa only [mul_comm (Real.log U)] using hh.le)
  linarith only [he]

/-- The height bias alone gives an unconditional lower bound in every dimension. -/
theorem eventually_height_lower_wasserstein (P : Finset ℕ) {c : ℝ}
    (hc : c < 3 / 4 - Real.log 2) :
    ∀ᶠ U : ℝ in atTop, c / Real.log U ≤ wassersteinOne P (mu P U) (nu P) := by
  filter_upwards [eventually_horizontal_add_height_lower P hc] with U h
  exact le_trans (le_add_of_nonneg_left (by unfold massSum mass; positivity)) h

/-- For a fixed P, two first absolute moments and direct approximation at the
actual bandwidth imply the sharp product law. -/
theorem sharp_wasserstein_of_firstMoments (P : Finset ℕ)
    (hh : DyadicHorizontalFirstMoment) (hr : DyadicPrimitiveFirstMoment) (hj : TensorJackson P) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c / Real.log U ≤ wassersteinOne P (mu P U) (nu P) ∧
      wassersteinOne P (mu P U) (nu P) ≤ C / Real.log U := by
  obtain ⟨K,hK,hb⟩ := uniform_test_bound_of_firstMoment P hh
    (shortPrimePrimitive_of_firstMoment hr) hj
  let c : ℝ := (3 / 4 - Real.log 2)/2
  have hk : 0 < 3 / 4 - Real.log 2 := by linarith [Real.log_two_lt_d9]
  have hlow := eventually_height_lower_wasserstein P (c := c) (by dsimp [c]; linarith)
  refine ⟨c,K,by dsimp [c]; positivity,hK,?_⟩
  filter_upwards [hlow,hb] with U hU hb
  let f : C(Space P, ℝ) := ⟨fun x => x.2.1, continuous_fst.comp continuous_snd⟩
  have hmem : |(∫ x, f x ∂mu P U) - ∫ x, f x ∂nu P| ∈ differences P (mu P U) (nu P) :=
    ⟨f, height_test P, rfl⟩
  refine ⟨hU, csSup_le ⟨_, hmem⟩ ?_⟩
  · rintro _ ⟨g,hg,rfl⟩
    exact hb g hg

/-- Equality between the two costs only along the actual dyadic sequence is
sufficient for the transport statement. -/
theorem sharp_transport_of_firstMoments (P : Finset ℕ)
    (hh : DyadicHorizontalFirstMoment) (hr : DyadicPrimitiveFirstMoment) (hj : TensorJackson P)
    (hk : ∀ᶠ U : ℝ in atTop, transportOne P (mu P U) (nu P) =
      wassersteinOne P (mu P U) (nu P)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c / Real.log U ≤ transportOne P (mu P U) (nu P) ∧
      transportOne P (mu P U) (nu P) ≤ C / Real.log U := by
  obtain ⟨c,C,hc,hC,hb⟩ := sharp_wasserstein_of_firstMoments P hh hr hj
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hb,hk] with U h e
  rwa [e]

theorem sharp_wasserstein_nu (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : UniformSelbergDensity (1 / 4)) (hsel : SelbergSixteenth)
    (hj : PositivePrimeTorusJackson) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c / Real.log U ≤ wassersteinOne P (mu P U) (nu P) ∧
      wassersteinOne P (mu P U) (nu P) ≤ C / Real.log U :=
  sharp_wasserstein_of_firstMoments P (horizontal_sum hs) (primitiveFirstMoment_of_sixteenth hsel)
    (tensorJackson_of_degree P (hj P hP))

/-- Product notation for the same target. The two requested conclusions are
definitionally equal. -/
theorem sharp_wasserstein_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : UniformSelbergDensity (1 / 4)) (hsel : SelbergSixteenth)
    (hj : PositivePrimeTorusJackson) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c / Real.log U ≤ wassersteinOne P (mu P U)
        ((Measure.dirac (1 / 2 : ℝ)).prod (unif.prod (haar P))) ∧
      wassersteinOne P (mu P U) ((Measure.dirac (1 / 2 : ℝ)).prod (unif.prod (haar P)))
        ≤ C / Real.log U :=
  sharp_wasserstein_nu P hP hs hsel hj

/-- The same two-sided estimate using the infimum over transport plans. -/
theorem sharp_transport_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : UniformSelbergDensity (1 / 4)) (hsel : SelbergSixteenth)
    (hj : PositivePrimeTorusJackson) (hkr : CompactKR) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c / Real.log U ≤ transportOne P (mu P U) (nu P) ∧
      transportOne P (mu P U) (nu P) ≤ C / Real.log U := by
  obtain ⟨c, C, hc, hC, h⟩ := sharp_wasserstein_nu P hP hs hsel hj
  obtain ⟨a, b, ha, hb, hm⟩ := dyadic_mass_bounds
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [h, hm, eventually_gt_atTop (1 : ℝ)] with U hU hm hu
  have hl := Real.log_pos hu
  have hp : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  have hp' : 0 < Ncount U (2 * U) := by unfold mass at hp; exact_mod_cast hp
  rw [hkr P _ _ (mu_probability P hp') inferInstance (mu_compact P hp') (nu_compact P)]
  exact hU

#print axioms shortPrimePrimitive_of_firstMoment
#print axioms primitiveFirstMoment_of_sixteenth
#print axioms uniform_test_bound_of_firstMoment
#print axioms eventually_horizontal_add_height_lower
#print axioms eventually_height_lower_wasserstein
#print axioms sharp_wasserstein_of_firstMoments
#print axioms sharp_transport_of_firstMoments

end RiemannResearch.Analysis.DyadicZeroWasserstein

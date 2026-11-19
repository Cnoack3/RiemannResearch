import RiemannResearch.Analysis.ActualZeroInghamHorizontalEnergy
import RiemannResearch.Analysis.ActualZeroCriticalLineTailFraction
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroTailDensityTransfer
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.LogarithmicMatrixMoments
import RiemannResearch.Analysis.LogMarginAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Count-normalized horizontal displacement moments of actual zeros

The cutoff retains every occurrence with analytic multiplicity. Mellin integration of
its strict displacement tail gives the positive absolute moments. Ingham's exponential
envelope absorbs its two surplus logarithms at displacement
`(3/2) * log(log T) / log T`. Only off-line copies enter the central term.

Analytic inputs used by the unconditional bounds are the repository proofs associated
with Chourasiya–Simonič, Theorem 1 (https://arxiv.org/abs/2507.15184), and
Alpöge–Furman (https://arxiv.org/abs/2608.13637). Ford–Zaharescu, Lemma 2
(https://arxiv.org/abs/math/0405459), supplies the stronger classical density estimate
in the separate Selberg implication.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The absolute moment of a uniformly sampled actual zero occurrence. -/
def displacementMoment (T : ℝ) (k : ℕ) : ℝ :=
  (∑ c : Copies T, copyDisplacement T c ^ k) / (Ncount 0 T : ℝ)

theorem displacementMoment_nonneg (T : ℝ) (k : ℕ) : 0 ≤ displacementMoment T k :=
  div_nonneg (Finset.sum_nonneg fun c _ => pow_nonneg (abs_nonneg (c.1.1.re-1/2)) k)
    (Nat.cast_nonneg _)

theorem displacementMoment_two (T : ℝ) :
    displacementMoment T 2 = horizontalEnergy T / (Ncount 0 T : ℝ) := by
  simp only [displacementMoment, horizontalEnergy, realSum_eq_copies, copyDisplacement, sq_abs]

/-- Sampling the per-zero energy instead of the displacement doubles the moment
order. In particular its second, third and fourth moments use orders 4, 6 and 8. -/
theorem energyMark_moment (T : ℝ) (k : ℕ) :
    (∑ c : Copies T, ((c.1.1.re-1/2)^2)^k) / (Ncount 0 T : ℝ) =
      displacementMoment T (2*k) := by
  simp only [displacementMoment, copyDisplacement, pow_mul, sq_abs]

/-- Finite Mellin identity, including the endpoint of the critical strip. -/
theorem displacementMoment_mellin (T : ℝ) (p : ℕ) :
    displacementMoment T (p + 1) =
      (∫ t in (0 : ℝ)..(1/2), strictTail T t * ((p + 1 : ℝ) * t ^ p)) /
        (Ncount 0 T : ℝ) := by
  have h := badWeightedSum_layerCake T 0 (fun t => t ^ (p + 1))
    (fun t => (p + 1 : ℝ) * t ^ p) (by norm_num) (by fun_prop)
    (fun t => by simpa using hasDerivAt_pow (p + 1) t)
  have hb : badWeightedSum T 0 (fun t => t ^ (p + 1)) =
      ∑ c : Copies T, copyDisplacement T c ^ (p + 1) := by
    unfold badWeightedSum FiniteStrictTail.badSum
    apply Finset.sum_congr rfl
    intro c _
    by_cases hp : 0 < copyDisplacement T c
    · simp [hp]
    · have hz := le_antisymm (le_of_not_gt hp) (abs_nonneg (c.1.1.re - 1/2))
      change copyDisplacement T c = 0 at hz
      simp [hz]
  simpa only [displacementMoment, hb, zero_pow (Nat.succ_ne_zero p), zero_mul, zero_add]
    using congrArg (fun v : ℝ => v / (Ncount 0 T : ℝ)) h

/-- The pointwise smaller of the off-line count and any exponential majorant
retains the finite upper endpoint in the moment bound. -/
theorem displacementMoment_le_mellin_cap (T A a : ℝ) (p : ℕ)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ A * Real.exp (-a*t)) :
    displacementMoment T (p+1) ≤
      (∫ t in (0:ℝ)..(1/2), min (strictTail T 0) (A * Real.exp (-a*t)) *
        ((p+1 : ℝ) * t^p)) / (Ncount 0 T : ℝ) := by
  rw [displacementMoment_mellin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hC : Continuous (fun t : ℝ => min (strictTail T 0) (A * Real.exp (-a*t)) *
      ((p+1 : ℝ)*t^p)) := by fun_prop
  apply intervalIntegral.integral_mono_on (by norm_num)
    (FiniteStrictTail.intervalIntegrable_tail_mul Finset.univ (copyDisplacement T)
      (fun t => (p+1 : ℝ)*t^p) (by fun_prop) 0 (1/2)) (hC.intervalIntegrable _ _)
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (le_min (strictTail_le_zero T t ht.1) (htail t ht))
    (mul_nonneg (by positivity) (pow_nonneg ht.1 p))

/-- Rescale the shifted strict tail before applying the Euler gamma integral. -/
private theorem scaled_excess_moment (T b a A : ℝ) (p : ℕ) (hb : 0 ≤ b)
    (ha : 0 < a) (hA : 0 ≤ A)
    (htail : ∀ t : ℝ, 0 ≤ t → strictTail T (b + t/a) ≤ A * Real.exp (-t)) :
    (∑ c : Copies T, (a * max 0 (copyDisplacement T c - b)) ^ (p+1)) ≤
      A * ((p+1).factorial : ℝ) := by
  let z := fun c : Copies T => a * max 0 (copyDisplacement T c - b)
  apply LogarithmicMatrixMoments.finite_moment_of_exponential_tail Finset.univ z A (a/2) p
    hA (by positivity) (fun c _ => mul_nonneg ha.le (le_max_left _ _))
  · intro c _
    have hx : copyDisplacement T c ≤ 1/2 := (displacement_lt_half c.1.2).le
    have hz : max 0 (copyDisplacement T c-b) ≤ 1/2 := max_le (by norm_num) (by linarith)
    simpa only [z, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hz ha.le
  · intro t ht
    apply le_trans _ (htail t ht)
    apply le_of_eq
    unfold FiniteStrictTail.tail strictTail
    apply Finset.sum_congr rfl
    intro c _
    have hzero : ¬ t / a < 0 := not_lt_of_ge (div_nonneg ht ha.le)
    have he : t < z c ↔ b + t/a < copyDisplacement T c := by
      change t < a * max 0 (copyDisplacement T c - b) ↔ _
      rw [mul_comm a, ← div_lt_iff₀ ha, lt_max_iff, or_iff_right hzero,
        lt_sub_iff_add_lt, add_comm (t/a) b]
    exact if_congr he rfl rfl

/-- Unnormalized factorial bound obtained by integrating the reflected
density envelope. It also holds when the zero multiset is empty. -/
theorem displacementSum_le_of_selberg {T C a : ℝ} (p : ℕ)
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a) (hD : SelbergDensityBound T C a) :
    (a * Real.log T) ^ (p+1) * (∑ c : Copies T, copyDisplacement T c ^ (p+1)) ≤
      (2 * C * T * Real.log T) * ((p+1).factorial : ℝ) := by
  let v := a * Real.log T
  have hT0 : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hv : 0 < v := mul_pos ha hL
  have hs := scaled_excess_moment T 0 v (2*C*T*Real.log T) p le_rfl hv
    (by positivity : 0 ≤ 2*C*T*Real.log T) (by
      intro t ht
      rw [zero_add]
      by_cases hhalf : t/v ≤ 1/2
      · have h := strictTail_of_selbergDensity T C a (t/v) hT0
          ⟨div_nonneg ht hv.le, hhalf⟩ hD
        have he : -(a * Real.log T) * (t / v) = -t := by
          change -v * (t/v) = -t
          field_simp
        simpa only [he] using h
      · have hz : strictTail T (t/v) = 0 := by
          apply Finset.sum_eq_zero
          intro c _
          exact if_neg (not_lt_of_ge ((displacement_lt_half c.1.2).le.trans (le_of_not_ge hhalf)))
        rw [hz]
        positivity)
  have hx (c : Copies T) : 0 ≤ copyDisplacement T c := abs_nonneg _
  simp only [sub_zero, max_eq_right (hx _), mul_pow, ← Finset.mul_sum] at hs
  exact hs

/-- A quantitative consequence of the classical Selberg density hypothesis in its
actual-zero, inclusive counting convention. -/
theorem displacementMoment_le_of_selberg {T C a : ℝ} (p : ℕ)
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a) (hD : SelbergDensityBound T C a) :
    displacementMoment T (p+1) * (a * Real.log T) ^ (p+1) ≤
      (2 * C * T * Real.log T / (Ncount 0 T : ℝ)) * ((p+1).factorial : ℝ) := by
  have hs := displacementSum_le_of_selberg p hT hC ha hD
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Ncount 0 T) : 0 ≤ (Ncount 0 T : ℝ))
  simpa only [displacementMoment, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hd

/-- Euler's integral bounds the truncated polynomial-exponential integral by
the full positive half-line integral after scaling. -/
private theorem integral_scaled_gamma_le (p : ℕ) (b M : ℝ)
    (hb : 0 < b) (hM : 0 ≤ M) :
    (∫ t in (0 : ℝ)..M, Real.exp (-b*t) * t^p) ≤ (p.factorial : ℝ) / b^(p+1) := by
  let g := fun t : ℝ => Real.exp (-t) * t^p
  have hsub : Ioc (0 : ℝ) (b*M) ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le p)
  have hup : (∫ t in (0:ℝ)..b*M, g t) ≤ (p.factorial : ℝ) := by
    rw [intervalIntegral.integral_of_le (mul_nonneg hb.le hM)]
    exact (setIntegral_mono_set (LogarithmicMatrixMoments.integrableOn_pow_mul_exp_neg p)
      hnn hsub.eventuallyLE).trans_eq (LogarithmicMatrixMoments.integral_pow_mul_exp_neg p)
  have he (t : ℝ) : Real.exp (-b*t)*t^p = (b^p)⁻¹ * g (b*t) := by
    dsimp [g]
    rw [mul_pow, ← neg_mul]
    field_simp
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left g hb.ne',
    smul_eq_mul, mul_zero]
  calc
    _ ≤ (b^p)⁻¹ * (b⁻¹ * (p.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup (by positivity)) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

private theorem hasDerivAt_tiltedMoment (p : ℕ) (v t : ℝ) :
    HasDerivAt (fun x : ℝ => x^(p+1) * Real.exp (v*x))
      ((((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)) t := by
  have h := (hasDerivAt_pow (p+1) t).mul (((hasDerivAt_id t).const_mul v).exp)
  convert h using 1 <;> try simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    id_eq, mul_one]
  all_goals first | rfl | ring

private theorem tiltedMoment_badSum (T v : ℝ) (p : ℕ) :
    badWeightedSum T 0 (fun t => t^(p+1) * Real.exp (v*t)) =
      ∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c) := by
  unfold badWeightedSum FiniteStrictTail.badSum
  apply Finset.sum_congr rfl
  intro c _
  by_cases hx : 0 < copyDisplacement T c
  · simp only [if_pos hx]
  · have hz : copyDisplacement T c = 0 := le_antisymm (le_of_not_gt hx) (abs_nonneg _)
    simp [hz]

/-- Exact finite-interval identity for any positive integer order and any real tilt.
The endpoint term at zero vanishes, including for copies on the critical line. -/
theorem tiltedMoment_layerCake (T v : ℝ) (p : ℕ) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) =
      ∫ t in (0 : ℝ)..(1/2), strictTail T t *
        ((((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)) := by
  have h := badWeightedSum_layerCake T 0 (fun t => t^(p+1) * Real.exp (v*t))
    (fun t => (((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)) (by norm_num)
    (by fun_prop) (hasDerivAt_tiltedMoment p v)
  simpa only [tiltedMoment_badSum, zero_pow (Nat.succ_ne_zero p), zero_mul, zero_add] using h

/-- Finite compensated tail bound for every positive integer order. It retains both
the strict off-line mass cap and the finite endpoint of the critical strip. -/
theorem tiltedMoment_le_mellin_cap {T K q v : ℝ} (p : ℕ) (hv : 0 ≤ v)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ K * Real.exp (-q*t)) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) ≤
      ∫ t in (0 : ℝ)..(1/2), min (strictTail T 0) (K * Real.exp (-q*t)) *
        ((((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)) := by
  rw [tiltedMoment_layerCake]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (FiniteStrictTail.intervalIntegrable_tail_mul Finset.univ (copyDisplacement T) _
      (by fun_prop) 0 (1/2)) (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  exact mul_le_mul_of_nonneg_right (le_min (strictTail_le_zero T t ht.1) (htail t ht))
    (by have ht0 : 0 ≤ t := ht.1; positivity)

/-- At the crossing of the off-line cap and an exponential majorant, the
head contribution cancels the integration-by-parts term at the lower limit.
The finite endpoint makes the bound valid even at and above the density rate. -/
theorem tiltedMoment_le_compensated_expTail {T F K q v d : ℝ} (p : ℕ)
    (hF : strictTail T 0 ≤ F) (hK : 0 ≤ K) (hq : 0 ≤ q) (hv : 0 ≤ v)
    (hd : d ∈ Icc (0 : ℝ) (1/2)) (hcross : K * Real.exp (-q*d) = F)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ K * Real.exp (-q*t)) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) ≤
      K * ((1/2 : ℝ)^(p+1) * Real.exp ((v-q)*(1/2)) +
        q * ∫ t in d..(1/2), t^(p+1) * Real.exp ((v-q)*t)) := by
  let f := fun t : ℝ => (((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)
  let φ := fun t : ℝ => t^(p+1) * Real.exp (v*t)
  let ψ := fun t : ℝ => t^(p+1) * Real.exp ((v-q)*t)
  let g := fun t : ℝ => (((p : ℝ)+1)*t^p + (v-q)*t^(p+1)) * Real.exp ((v-q)*t)
  let a := fun t : ℝ => min F (K * Real.exp (-q*t)) * f t
  have hc : Continuous a := by dsimp [a,f]; fun_prop
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have h1 : (∫ t in (0 : ℝ)..d, a t) = F * φ d := by
    have he : (∫ t in (0 : ℝ)..d, a t) = ∫ t in (0 : ℝ)..d, F * f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hd.1] at ht
      have h := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hq))) hK
      rw [hcross] at h
      dsimp [a]
      rw [min_eq_left h]
    rw [he, intervalIntegral.integral_const_mul]
    have hi : (∫ t in (0 : ℝ)..d, f t) = φ d - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_tiltedMoment p v t) (hf.intervalIntegrable _ _)
    rw [hi, show φ 0 = 0 by simp [φ], sub_zero]
  have h2 : (∫ t in d..(1/2), a t) = K * ((ψ (1/2) - ψ d) + q * ∫ t in d..(1/2), ψ t) := by
    have he : (∫ t in d..(1/2), a t) = ∫ t in d..(1/2), K * (g t + q * ψ t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hd.2] at ht
      have h := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hq))) hK
      rw [hcross] at h
      dsimp [a]
      rw [min_eq_right h]
      dsimp [g,f,ψ]
      rw [show (v-q)*t = -q*t + v*t by ring, Real.exp_add]
      ring
    have hqψ : Continuous (fun t : ℝ => q * ψ t) := continuous_const.mul hψ
    rw [he, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hg.intervalIntegrable _ _)
        (hqψ.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    have hi : (∫ t in d..(1/2), g t) = ψ (1/2) - ψ d :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_tiltedMoment p (v-q) t) (hg.intervalIntegrable _ _)
    rw [hi]
  have hhead : F*φ d = K*ψ d := by
    rw [← hcross]
    dsimp [φ,ψ]
    rw [show (v-q)*d = -q*d + v*d by ring, Real.exp_add]
    ring
  rw [tiltedMoment_layerCake]
  apply le_trans (b := ∫ t in (0 : ℝ)..(1/2), a t)
  · apply intervalIntegral.integral_mono_on (by norm_num)
      (FiniteStrictTail.intervalIntegrable_tail_mul Finset.univ (copyDisplacement T) f
        hf 0 (1/2)) (hc.intervalIntegrable _ _)
    intro t ht
    apply mul_le_mul_of_nonneg_right
      (le_min ((strictTail_le_zero T t ht.1).trans hF) (htail t ht))
    have ht0 : 0 ≤ t := ht.1
    dsimp [f]
    positivity
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 d) (hc.intervalIntegrable d (1/2)), h1, h2, hhead]
    change K*ψ d + K*((ψ (1/2)-ψ d) + q*∫ t in d..(1/2), ψ t) ≤
      K*(ψ (1/2) + q*∫ t in d..(1/2), ψ t)
    apply le_of_eq
    ring

/-- The endpoint polynomial in an integer-order incomplete gamma integral. -/
def gammaEndpointPolynomial (p : ℕ) (x : ℝ) : ℝ :=
  (p.factorial : ℝ) * ∑ j ∈ Finset.range (p+1), x^j / (j.factorial : ℝ)

private theorem gammaEndpointPolynomial_succ (p : ℕ) (x : ℝ) :
    gammaEndpointPolynomial (p+1) x =
      ((p : ℝ)+1) * gammaEndpointPolynomial p x + x^(p+1) := by
  unfold gammaEndpointPolynomial
  rw [Finset.sum_range_succ]
  have hp : ((p+1).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_add, show ((p+1).factorial : ℝ)*(x^(p+1)/((p+1).factorial : ℝ)) =
    x^(p+1) by field_simp]
  rw [Nat.factorial_succ]
  push_cast
  ring

private theorem hasDerivAt_exp_gammaEndpoint (p : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x) * gammaEndpointPolynomial p x)
      (-Real.exp (-t) * t^p) t := by
  have hexp := ((hasDerivAt_id t).neg).exp
  induction p with
  | zero => simpa [gammaEndpointPolynomial] using hexp
  | succ p ih =>
    have hh := (ih.const_mul ((p : ℝ)+1)).add (hexp.mul (hasDerivAt_pow (p+1) t))
    have hf : (fun x : ℝ => Real.exp (-x) * gammaEndpointPolynomial (p+1) x) =
        ((fun x : ℝ => ((p : ℝ)+1) * (Real.exp (-x)*gammaEndpointPolynomial p x)) +
          (fun x : ℝ => Real.exp (-x)) * fun x : ℝ => x^(p+1)) := by
      funext x
      simp only [gammaEndpointPolynomial_succ, Pi.add_apply, Pi.mul_apply]
      ring
    rw [hf]
    apply hh.congr_deriv
    simp only [Pi.neg_apply, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_neg, mul_one]
    ring

/-- Exact integral between arbitrary finite endpoints. This expression is valid
for both signs of the exponent and records the compensating upper boundary. -/
theorem integral_pow_exp_between (p : ℕ) (b d B : ℝ) (hb : b ≠ 0) :
    (∫ x in d..B, x^p * Real.exp (-b*x)) =
      (Real.exp (-b*d) * gammaEndpointPolynomial p (b*d) -
        Real.exp (-b*B) * gammaEndpointPolynomial p (b*B)) / b^(p+1) := by
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => -(Real.exp (-b*y) * gammaEndpointPolynomial p (b*y)) / b^(p+1))
      (x^p * Real.exp (-b*x)) x := by
    have h := (((hasDerivAt_exp_gammaEndpoint p (b*x)).comp x
      ((hasDerivAt_id x).const_mul b)).neg).div_const (b^(p+1))
    have he : -(-Real.exp (-(b*x))*(b*x)^p*(b*1))/b^(p+1) =
        x^p*Real.exp (-b*x) := by
      rw [mul_pow, pow_succ]
      field_simp [hb]
      <;> ring
    rw [he] at h
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_mul] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The all-order cap at unequal density and tilt rates in finite arithmetic form. -/
theorem tiltedMoment_le_compensated_polynomial {T F K q v d : ℝ} (p : ℕ)
    (hF : strictTail T 0 ≤ F) (hK : 0 ≤ K) (hq : 0 ≤ q) (hv : 0 ≤ v) (hgap : q ≠ v)
    (hd : d ∈ Icc (0 : ℝ) (1/2)) (hcross : K * Real.exp (-q*d) = F)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ K * Real.exp (-q*t)) :
    let b := q-v
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) ≤
      K * ((1/2 : ℝ)^(p+1) * Real.exp (-b*(1/2)) + q *
        ((Real.exp (-b*d) * gammaEndpointPolynomial (p+1) (b*d) -
          Real.exp (-b*(1/2)) * gammaEndpointPolynomial (p+1) (b*(1/2))) / b^(p+2))) := by
  dsimp only
  have he := tiltedMoment_le_compensated_expTail p hF hK hq hv hd hcross htail
  rw [show v-q = -(q-v) by ring] at he
  rwa [integral_pow_exp_between (p+1) (q-v) d (1/2) (sub_ne_zero.mpr hgap)] at he

/-- The incomplete gamma endpoint polynomial contains its highest monomial. -/
theorem pow_le_gammaEndpointPolynomial (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x^p ≤ gammaEndpointPolynomial p x := by
  cases p with
  | zero => simp [gammaEndpointPolynomial]
  | succ p =>
    rw [gammaEndpointPolynomial_succ]
    apply le_add_of_nonneg_left
    apply mul_nonneg (by positivity)
    unfold gammaEndpointPolynomial
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ =>
      div_nonneg (pow_nonneg hx j) (Nat.cast_nonneg _))

/-- For tilts below the density rate, deleting the nonpositive upper boundary
leaves the incomplete gamma polynomial at the cap crossing. -/
theorem tiltedMoment_le_compensated_subcritical {T F K q v d : ℝ} (p : ℕ)
    (hF : strictTail T 0 ≤ F) (hK : 0 ≤ K) (hv : 0 ≤ v) (hvq : v < q)
    (hd : d ∈ Icc (0 : ℝ) (1/2)) (hcross : K * Real.exp (-q*d) = F)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ K * Real.exp (-q*t)) :
    let b := q-v
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) ≤
      F * Real.exp (v*d) * (q * gammaEndpointPolynomial (p+1) (b*d) / b^(p+2)) := by
  let b := q-v
  have hb : 0 < b := sub_pos.mpr hvq
  have hq : 0 ≤ q := hv.trans hvq.le
  have he := tiltedMoment_le_compensated_polynomial p hF hK hq hv (ne_of_gt hvq) hd hcross htail
  have hh := pow_le_gammaEndpointPolynomial (p+1) (mul_nonneg hb.le (by norm_num : 0 ≤ (1/2 : ℝ)))
  have hbp : (1/2 : ℝ)^(p+1)*b^(p+2) ≤ q * gammaEndpointPolynomial (p+1) (b*(1/2)) := calc
    _ = b*((b*(1/2))^(p+1)) := by rw [pow_succ b (p+1), mul_pow]; ring
    _ ≤ _ := mul_le_mul (show b ≤ q by dsimp [b]; linarith) hh (by positivity) hq
  have hhB := mul_le_mul_of_nonneg_right hbp (Real.exp_pos (-b*(1/2))).le
  have hcmp : ((1/2 : ℝ)^(p+1)*Real.exp (-b*(1/2)) + q *
      ((Real.exp (-b*d) * gammaEndpointPolynomial (p+1) (b*d) -
        Real.exp (-b*(1/2)) * gammaEndpointPolynomial (p+1) (b*(1/2))) / b^(p+2))) ≤
      Real.exp (-b*d) * (q * gammaEndpointPolynomial (p+1) (b*d) / b^(p+2)) := by
    calc
      _ = (((1/2 : ℝ)^(p+1)*Real.exp (-b*(1/2)))*b^(p+2) + q *
          (Real.exp (-b*d) * gammaEndpointPolynomial (p+1) (b*d) -
            Real.exp (-b*(1/2)) * gammaEndpointPolynomial (p+1) (b*(1/2)))) / b^(p+2) := by
        field_simp [hb.ne']
      _ ≤ (Real.exp (-b*d)*(q * gammaEndpointPolynomial (p+1) (b*d))) / b^(p+2) :=
        div_le_div_of_nonneg_right (by nlinarith only [hhB]) (pow_nonneg hb.le _)
      _ = _ := by ring
  have hE : K * Real.exp (-b*d) = F*Real.exp (v*d) := by
    rw [← hcross, show -b*d = -q*d+v*d by dsimp [b]; ring, Real.exp_add]
    ring
  apply he.trans ((mul_le_mul_of_nonneg_left hcmp hK).trans_eq ?_)
  rw [← mul_assoc, hE]

/-- At tilt equal to the density rate, the finite cap reduces to an elementary
polynomial in the crossing position. -/
theorem tiltedMoment_le_compensated_at_rate {T F K q d : ℝ} (p : ℕ)
    (hF : strictTail T 0 ≤ F) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hd : d ∈ Icc (0 : ℝ) (1/2)) (hcross : K * Real.exp (-q*d) = F)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1/2), strictTail T t ≤ K * Real.exp (-q*t)) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (q*copyDisplacement T c)) ≤
      K * ((1/2 : ℝ)^(p+1) + q * (((1/2 : ℝ)^(p+2) - d^(p+2)) / ((p : ℝ)+2))) := by
  have h := tiltedMoment_le_compensated_expTail p hF hK hq hq hd hcross htail
  simpa only [sub_self, zero_mul, Real.exp_zero, mul_one, integral_pow, Nat.cast_add,
    Nat.cast_one, add_assoc, one_add_one_eq_two] using h

/-- When a two-sided displacement tail has majorant K exp(−q t), the full
half-line weighted factorial constant is K k! q/(q−v)^(k+1) for each k≥1. -/
theorem tiltedMoment_le_expTail {T K q v : ℝ} (p : ℕ) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hvq : v < q) (htail : ∀ t ∈ Icc (0 : ℝ) (1/2),
      strictTail T t ≤ K * Real.exp (-q*t)) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) ≤
      K * (((p+1).factorial : ℝ) * q / (q-v)^(p+2)) := by
  let b := q-v
  let f := fun t : ℝ => (((p : ℝ)+1)*t^p + v*t^(p+1)) * Real.exp (v*t)
  have hb : 0 < b := sub_pos.mpr hvq
  have h := badWeightedSum_le_of_expTail T 0 K q (fun t => t^(p+1)*Real.exp (v*t)) f
    (by norm_num) (by dsimp [f]; fun_prop) (hasDerivAt_tiltedMoment p v) (by simp)
    (fun t ht => by have ht0 : 0 ≤ t := ht.1; dsimp [f]; positivity) htail
  simp only [tiltedMoment_badSum, zero_pow (Nat.succ_ne_zero p), zero_mul, zero_add] at h
  have hsplit (t : ℝ) : Real.exp (-q*t) * f t =
      ((p : ℝ)+1)*(Real.exp (-b*t)*t^p) + v*(Real.exp (-b*t)*t^(p+1)) := by
    have he : Real.exp (-q*t)*Real.exp (v*t) = Real.exp (-b*t) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [b]
      ring
    dsimp [f]
    rw [← he]
    ring
  simp_rw [hsplit] at h
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have hp := integral_scaled_gamma_le p b (1/2) hb (by norm_num)
  have hs := integral_scaled_gamma_le (p+1) b (1/2) hb (by norm_num)
  have hh := add_le_add (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (p : ℝ)+1))
    (mul_le_mul_of_nonneg_left hs hv)
  apply (h.trans (mul_le_mul_of_nonneg_left hh hK)).trans_eq
  change K*(((p : ℝ)+1)*((p.factorial : ℝ)/b^(p+1)) +
    v*(((p+1).factorial : ℝ)/b^((p+1)+1))) =
    K*(((p+1).factorial : ℝ)*q/b^((p+1)+1))
  have he : q = b+v := by dsimp [b]; ring
  rw [he, pow_succ b (p+1), Nat.factorial_succ]
  push_cast
  field_simp
  <;> ring

/-- Quartic specialization in the signed horizontal coordinate used by the
reflected Gram kernel. -/
theorem weightedFourthSum_le_expTail {T K q v : ℝ} (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hvq : v < q) (htail : ∀ t ∈ Icc (0:ℝ) (1/2),
      strictTail T t ≤ K * Real.exp (-q * t)) :
    (∑ c : Copies T, (c.1.1.re-1/2)^4 * Real.exp (v*|c.1.1.re-1/2|)) ≤
      K*(24*q/(q-v)^5) := by
  have h := tiltedMoment_le_expTail 3 hK hv hvq htail
  norm_num [Nat.factorial] at h
  have hs (x : ℝ) : |x|^4 = x^4 := by
    rw [show (4 : ℕ) = 2*2 by decide, pow_mul, sq_abs, ← pow_mul]
  simpa only [copyDisplacement, hs] using h

/-- Height-normalized tilted absolute moments of every positive integer
order, with a single inclusive density constant and the full open tilt range. -/
theorem tiltedMoment_div_height_of_selberg {T C a v : ℝ} (p : ℕ)
    (hT : 1 < T) (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hvq : v < a*Real.log T) (hD : SelbergDensityBound T C a) :
    (∑ c : Copies T, copyDisplacement T c^(p+1) * Real.exp (v*copyDisplacement T c)) / T ≤
      2*C*Real.log T * (((p+1).factorial : ℝ)*(a*Real.log T)/(a*Real.log T-v)^(p+2)) := by
  have ht := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have h := tiltedMoment_le_expTail p (by positivity : 0 ≤ 2*C*T*Real.log T) hv hvq
    (fun t ht' => strictTail_of_selbergDensity T C a t ht ht' hD)
  apply (div_le_iff₀ ht).mpr
  apply h.trans_eq
  ring

/-- An exponential weight uses part of the density exponent. After reflection
and division by height, its fourth moment is bounded with the exact
half-line constant for the given tail majorant. -/
theorem weightedFourthMoment_div_height_of_selberg {T C a v : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a) (hv : 0 ≤ v)
    (hvq : v < a * Real.log T) (hD : SelbergDensityBound T C a) :
    (∑ c : Copies T, (c.1.1.re-1/2)^4 * Real.exp (v*|c.1.1.re-1/2|)) / T ≤
      48*C*Real.log T*(a*Real.log T)/(a*Real.log T-v)^5 := by
  have ht : 0 < T := by linarith
  have hL := Real.log_pos hT
  have h := weightedFourthSum_le_expTail (by positivity : 0 ≤ 2*C*T*Real.log T) hv hvq
    (fun t ht' => strictTail_of_selbergDensity T C a t ht ht' hD)
  apply (div_le_iff₀ ht).mpr
  apply h.trans_eq
  ring

/-- For any fixed closed subband of the density frequency band, the fourth
moment with exponential weight is O((log T)⁻³) after dividing by height. -/
theorem weightedFourthMoment_div_height_band {T C a u θ : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a) (hθ : θ < 1)
    (hu : 2 * |u| ≤ θ*(a*Real.log T)) (hD : SelbergDensityBound T C a) :
    (∑ c : Copies T, (c.1.1.re-1/2)^4 * Real.exp (2 * |u| * |c.1.1.re-1/2|)) / T ≤
      (48*C / ((1-θ)^5 * a^4)) / (Real.log T)^3 := by
  have hL := Real.log_pos hT
  have hq : 0 < a * Real.log T := mul_pos ha hL
  have hs : 0 < 1-θ := sub_pos.mpr hθ
  have hv : 2 * |u| < a*Real.log T := hu.trans_lt (by nlinarith [mul_pos hs hq])
  have h := weightedFourthMoment_div_height_of_selberg hT hC ha
    (show 0 ≤ 2 * |u| by positivity) hv hD
  have hden : (1-θ)*(a*Real.log T) ≤ a*Real.log T - 2 * |u| := by linarith
  have hp := pow_le_pow_left₀ (mul_pos hs hq).le hden 5
  apply h.trans
  calc
    _ ≤ 48*C*Real.log T*(a*Real.log T) / ((1-θ)*(a*Real.log T))^5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by rw [mul_pow, mul_pow]; field_simp <;> ring

/-- The exact cap in the central strip is the number of off-line copies.
The excess is measured in units of `1/a`. -/
private theorem moment_split (T b a θ : ℝ) (p : ℕ) (hb : 0 ≤ b) (ha : 0 < a) (hθ : 0 < θ) :
    (∑ c : Copies T, copyDisplacement T c ^ (p+1)) ≤
      ((1+θ)*b) ^ (p+1) * strictTail T 0 +
      ((1+θ⁻¹)/a) ^ (p+1) *
        (∑ c : Copies T, (a * max 0 (copyDisplacement T c-b)) ^ (p+1)) := by
  unfold strictTail FiniteStrictTail.tail
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  let x := copyDisplacement T c
  have hx : 0 ≤ x := abs_nonneg _
  change x ^ (p+1) ≤ ((1+θ)*b) ^ (p+1) * (if 0 < x then 1 else 0) +
    ((1+θ⁻¹)/a) ^ (p+1) * (a * max 0 (x-b)) ^ (p+1)
  by_cases hx0 : 0 < x
  · rw [if_pos hx0, mul_one]
    by_cases hnear : x ≤ (1+θ)*b
    · exact (pow_le_pow_left₀ hx hnear _).trans (le_add_of_nonneg_right (by positivity))
    · have hxb : 0 ≤ x-b := by nlinarith [mul_nonneg hθ.le hb]
      rw [max_eq_right hxb, ← mul_pow]
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      apply pow_le_pow_left₀ hx
      have hxθ : θ*x ≤ (θ+1)*(x-b) := by nlinarith only [le_of_not_ge hnear]
      have hc : (1+θ⁻¹)/a * (a*(x-b)) = ((θ+1)*(x-b))/θ := by
        field_simp
      rw [hc]
      exact (le_div_iff₀ hθ).mpr (by linarith)
  · have he := le_antisymm (le_of_not_gt hx0) hx
    rw [he, zero_pow (Nat.succ_ne_zero p)]
    positivity

/-- Width at which the Ingham exponential absorbs the excess logarithms. -/
def inghamDisplacementScale (T : ℝ) : ℝ := Real.log (Real.log T) / Real.log T

/-- The finite upper bound keeps the observed off-line fraction. One constant
works for all positive moment orders and all positive splitting parameters. -/
theorem exists_displacementMoment_bound_by_offline_fraction :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (p : ℕ) (θ : ℝ), 0 < θ →
      displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
        ((1+θ)*(3/2 : ℝ)) ^ (p+1) * (strictTail T 0 / (Ncount 0 T : ℝ)) +
        (K * ((p+1).factorial : ℝ)) * (((1+θ⁻¹)*(3/4 : ℝ)) / Real.log (Real.log T)) ^ (p+1) := by
  obtain ⟨C,hC,hIngham⟩ := exists_strictTail_ingham_exponential
  obtain ⟨c,hc,hcount⟩ := exists_count_normalization
  refine ⟨C/c, div_pos hC hc, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (max 2 (Real.exp 1)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T hN hT hℓ
  let L := Real.log T
  let ℓ := Real.log L
  let b := (3/2 : ℝ)*ℓ/L
  let a := (4/3 : ℝ)*L
  have hT1 : 1 < T := by linarith [le_max_left (2:ℝ) (Real.exp 1)]
  have hL : 0 < L := Real.log_pos hT1
  change 0 < ℓ at hℓ
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hNR : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hnum : C*T*L ≤ (C/c)*(Ncount 0 T : ℝ) := by
    calc
      C*T*L = (C/c)*(c*T*L) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (div_nonneg hC.le hc.le)
  have hab : a*b = 2*ℓ := by dsimp [a,b]; field_simp; ring
  have hexp : Real.exp (2*ℓ) = L^2 := by
    rw [show (2:ℝ)*ℓ = (2:ℕ)*ℓ by norm_num, Real.exp_nat_mul, Real.exp_log hL]
  have htail (t : ℝ) (ht : 0 ≤ t) :
      strictTail T (b+t/a) ≤ ((C/c)*(Ncount 0 T : ℝ)) * Real.exp (-t) := by
    have h := hIngham T hT (b+t/a) (add_nonneg hb (div_nonneg ht ha.le))
    change strictTail T (b+t/a) ≤ C*T*L^3*Real.exp (-(a*(b+t/a))) at h
    have he : -(a*(b+t/a)) = -(a*b) + -t := by field_simp; ring
    rw [he, Real.exp_add, hab, Real.exp_neg (2*ℓ), hexp] at h
    apply h.trans
    calc
      C*T*L^3*((L^2)⁻¹*Real.exp (-t)) = C*T*L*Real.exp (-t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
  intro p θ hθ
  have hZ := scaled_excess_moment T b a ((C/c)*(Ncount 0 T : ℝ)) p hb ha (by positivity) htail
  have hsum := (moment_split T b a θ p hb ha hθ).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hZ
      (show 0 ≤ ((1+θ⁻¹)/a) ^ (p+1) by positivity)))
  have h1 := div_le_div_of_nonneg_right hsum hNR.le
  have h2 := div_le_div_of_nonneg_right h1 (pow_nonneg (div_nonneg hℓ.le hL.le) (p+1))
  apply h2.trans_eq
  change (_ + _) / (Ncount 0 T : ℝ) / (ℓ/L)^(p+1) =
    ((1+θ)*(3/2 : ℝ))^(p+1) * (strictTail T 0/(Ncount 0 T : ℝ)) +
      ((C/c)*((p+1).factorial : ℝ)) * (((1+θ⁻¹)*(3/4 : ℝ))/ℓ)^(p+1)
  have hwidth : (1+θ)*b = ((1+θ)*(3/2 : ℝ))*(ℓ/L) := by dsimp [b]; ring
  have hexcess : (1+θ⁻¹)/a = (((1+θ⁻¹)*(3/4 : ℝ))/ℓ)*(ℓ/L) := by
    dsimp [a]; field_simp [hL.ne', hℓ.ne']
  simp only [hwidth, hexcess, mul_pow _ (ℓ/L)]
  have hs : (ℓ/L)^(p+1) ≠ 0 := pow_ne_zero _ (div_ne_zero hℓ.ne' hL.ne')
  field_simp [hNR.ne', hs]

/-- Every positive fixed order retains the off-line proportion in its leading
coefficient. Equivalently the limsup on the Ingham scale is at most
`(3/2)^(p+1)/3`. -/
theorem eventually_displacementMoment_ratio_le (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
      (3/2 : ℝ) ^ (p+1) / 3 + ε := by
  let F (t : ℝ) := ((1+t)*(3/2 : ℝ)) ^ (p+1) * (1/3+t)
  have hf : Continuous F := by dsimp [F]; fun_prop
  have h0 : F 0 < (3/2 : ℝ) ^ (p+1) / 3 + ε := by dsimp [F]; linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, F t < (3/2 : ℝ) ^ (p+1) / 3 + ε :=
    ((hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h0))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨θ, hθ, hgap⟩ := (hpos.and hev).exists
  obtain ⟨K, _, hbound⟩ := exists_displacementMoment_bound_by_offline_fraction
  have hz := (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_div_atTop
    ((1+θ⁻¹)*(3/4 : ℝ))).pow (p+1)).const_mul (K * ((p+1).factorial : ℝ))
  have hlim : Tendsto (fun T : ℝ => F θ +
      (K * ((p+1).factorial : ℝ)) * (((1+θ⁻¹)*(3/4 : ℝ)) / Real.log (Real.log T)) ^ (p+1))
      atTop (𝓝 (F θ)) := by
    simpa only [Function.comp_apply, zero_pow (Nat.succ_ne_zero p), mul_zero, add_zero] using
      (tendsto_const_nhds (x := F θ)).add hz
  filter_upwards [hbound, eventually_normalized_strictTail_le_third θ hθ,
    hlim.eventually (gt_mem_nhds hgap)] with T hb hoff hsmall
  exact (hb p θ hθ).trans ((add_le_add
    (mul_le_mul_of_nonneg_left (hoff 0 le_rfl)
      (show 0 ≤ ((1+θ)*(3/2 : ℝ)) ^ (p+1) by positivity)) (le_refl _)).trans hsmall.le)

/-- In the original height normalization the off-line count improves the
coefficient from `9/(8π)` to `3/(8π)`. -/
theorem eventually_horizontalEnergy_ratio_le_critical_count {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, horizontalEnergy T / (T * horizontalLogRate T) ≤
      3 / (8 * Real.pi) + ε := by
  let F (t : ℝ) := (3/4+t) * (1/(2*Real.pi)+t)
  have hf : Continuous F := by dsimp [F]; fun_prop
  have h0 : F 0 < 3/(8*Real.pi)+ε := by
    have he : F 0 = 3/(8*Real.pi) := by dsimp [F]; ring
    linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, F t < 3/(8*Real.pi)+ε :=
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h0)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨θ,hθ,hsmall⟩ := (hpos.and hev).exists
  have hsecond := eventually_displacementMoment_ratio_le 1 hθ
  have hcount := eventually_count_le_log_of_lt
    (show 1/(2*Real.pi) < 1/(2*Real.pi)+θ by linarith)
  filter_upwards [hsecond, hcount, eventually_count_pos, eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
      with T hm hn hp ht hℓ
  have hT : 0 < T := zero_lt_one.trans ht
  have hL := Real.log_pos ht
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  have h2 : horizontalEnergy T / (Ncount 0 T : ℝ) / inghamDisplacementScale T ^ 2 ≤ 3/4+θ := by
    norm_num [displacementMoment_two] at hm ⊢
    exact hm
  have hratio : (Ncount 0 T : ℝ) / (T * Real.log T) ≤ 1/(2*Real.pi)+θ :=
    (div_le_iff₀ (mul_pos hT hL)).mpr (by simpa only [mul_assoc] using hn)
  have he : horizontalEnergy T / (T * horizontalLogRate T) =
      (horizontalEnergy T / (Ncount 0 T : ℝ) / inghamDisplacementScale T ^ 2) *
        ((Ncount 0 T : ℝ) / (T * Real.log T)) := by
    unfold horizontalLogRate inghamDisplacementScale
    field_simp [hN, hL.ne', hℓ.ne', hT.ne']
  rw [he]
  exact (mul_le_mul h2 hratio (by positivity) (by positivity)).trans hsmall.le

/-- Positive absolute moments converge along all real heights. -/
theorem tendsto_displacementMoment (p : ℕ) :
    Tendsto (fun T : ℝ => displacementMoment T (p+1)) atTop (𝓝 0) := by
  have hscale : Tendsto inghamDisplacementScale atTop (𝓝 0) :=
    Real.log_div_self_tendsto_zero.comp Real.tendsto_log_atTop
  have hu := (hscale.pow (p+1)).const_mul ((3/2 : ℝ) ^ (p+1) / 3 + 1)
  simp only [zero_pow (Nat.succ_ne_zero p), mul_zero] at hu
  apply squeeze_zero' (Eventually.of_forall fun T => displacementMoment_nonneg T _) _ hu
  filter_upwards [eventually_displacementMoment_ratio_le p zero_lt_one,
    eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T hb hT hℓ
  exact (div_le_iff₀ (pow_pos (div_pos hℓ (Real.log_pos hT)) _)).mp hb

/-- One Selberg constant works simultaneously in the factorial moment bounds.
The positive-exponent density statement is the sole analytic premise of this
sharper rate. -/
theorem exists_selberg_displacementMoment_bound {a : ℝ} (ha : 0 < a)
    (hd : UniformSelbergDensity a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ p : ℕ,
      displacementMoment T (p+1) * (a * Real.log T) ^ (p+1) ≤ K * ((p+1).factorial : ℝ) := by
  obtain ⟨C,T₀,hC,hT₀,hD⟩ := hd
  obtain ⟨c,hc,hcount⟩ := exists_count_normalization
  refine ⟨2*C/c, by positivity, ?_⟩
  filter_upwards [hcount,eventually_ge_atTop T₀] with T hN ht
  have hT := hT₀.trans_le ht
  have hL := Real.log_pos hT
  have hT0 : 0 < T := by linarith
  have hn : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hratio : 2*C*T*Real.log T / (Ncount 0 T : ℝ) ≤ 2*C/c := by
    apply (div_le_iff₀ hn).2
    calc
      _ = (2*C/c)*(c*T*Real.log T) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)
  intro p
  exact (displacementMoment_le_of_selberg p hT hC ha (hD T ht)).trans
    (mul_le_mul_of_nonneg_right hratio (by positivity))

/-- Reflection cancels every signed odd displacement moment against an arbitrary
ordinate weight, at each finite cutoff. -/
theorem ordinate_weighted_odd_displacement_sum (T : ℝ) (g : ℝ → ℝ) (p : ℕ) :
    realSum T (fun ρ => g ρ.im * (ρ.re - 1/2) ^ (2*p+1)) = 0 := by
  let f := fun ρ : ℂ => g ρ.im * (ρ.re - 1/2) ^ (2*p+1)
  have h := realSum_reflect T f
  have hn (ρ : ℂ) : f (reflect ρ) = -f ρ := by
    simp only [f, reflect_im, reflect_re]
    rw [show 1-ρ.re-1/2 = -(ρ.re-1/2) by ring, pow_succ, pow_succ,
      pow_mul, pow_mul, neg_sq]
    ring
  simp_rw [hn] at h
  simp only [realSum, mul_neg, Finset.sum_neg_distrib] at h
  change realSum T f = 0
  unfold realSum
  linarith

end RiemannResearch.Analysis.ActualZeroOrdinate

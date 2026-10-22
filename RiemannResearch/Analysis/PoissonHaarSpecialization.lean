import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Poisson kernels against normalized circle Haar measure

Source: the Fourier specialization proved in
`FMZ_Haar_Poisson_Pareto_Paper_Proofs_20261011.md`. The terminology and
prime-axis limiting density agree with Ford--Meng--Zaharescu,
https://www.ford126.web.illinois.edu/wwwpapers/FMZ.pdf, formula (1.3).

The kernel here is an actual continuous function on `AddCircle 1`, built by
convergent geometric series. Its Haar coefficients are computed by continuous
linear maps, not inserted as a hypothesis. Arithmetic asymptotics for actual
zeros are deliberately outside this deterministic harmonic module.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace RiemannResearch.Analysis.PoissonHaar
open RiemannResearch.Analysis.ZeroOrdinate

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev CircleSpace := AddCircle (1 : ℝ)
abbrev CircleFunction := C(CircleSpace, ℂ)

def haarIntegralCLM : CircleFunction →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    (RiemannResearch.Analysis.ZeroOrdinate.probabilityIntegral
      (AddCircle.haarAddCircle (T := 1)) : CircleFunction →ₗ[ℂ] ℂ)
    1 (fun f : CircleFunction => by
      simpa only [one_mul] using
        (RiemannResearch.Analysis.ZeroOrdinate.probabilityIntegral_bound
          (AddCircle.haarAddCircle (T := 1)) f))

def coefficientCLM (k : ℤ) : CircleFunction →L[ℂ] ℂ :=
  haarIntegralCLM.comp ((ContinuousLinearMap.mul ℂ CircleFunction) (fourier (-k)))

@[simp] theorem coefficientCLM_apply (k : ℤ) (f : CircleFunction) :
    coefficientCLM k f = fourierCoeff f k := by
  change (∫ x : CircleSpace, fourier (-k) x * f x ∂AddCircle.haarAddCircle) =
    ∫ x : CircleSpace, fourier (-k) x • f x ∂AddCircle.haarAddCircle
  simp only [ContinuousMap.mul_apply, smul_eq_mul]

@[simp] theorem coefficientCLM_fourier (k n : ℤ) :
    coefficientCLM k (fourier n) = if n = k then 1 else 0 := by
  rw [coefficientCLM_apply]
  simpa [Pi.single_apply, eq_comm] using congrFun (fourierCoeff_fourier (T := 1) n) k

def poissonRatio (a : ℝ) (sign : ℤ) : CircleFunction := (a : ℂ) • fourier sign

def poissonKernel (a : ℝ) : CircleFunction :=
  (∑' n : ℕ, poissonRatio a 1 ^ n) +
    (∑' n : ℕ, poissonRatio a (-1) ^ n) - 1

theorem poissonRatio_norm (a : ℝ) (sign : ℤ) (ha : 0 ≤ a) :
    ‖poissonRatio a sign‖ = a := by
  simp [poissonRatio, norm_smul, fourier_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]

theorem poissonRatio_summable (a : ℝ) (sign : ℤ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun n : ℕ => poissonRatio a sign ^ n) := by
  apply summable_geometric_of_norm_lt_one
  rwa [poissonRatio_norm a sign ha]

theorem fourier_nat_mul (sign : ℤ) (n : ℕ) (x : CircleSpace) :
    fourier ((n : ℤ) * sign) x = fourier sign x ^ n := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, fourier_add, ih, pow_succ]

theorem poissonRatio_pow (a : ℝ) (sign : ℤ) (n : ℕ) :
    poissonRatio a sign ^ n = (a : ℂ)^n • fourier ((n : ℤ) * sign) := by
  ext x
  simp only [poissonRatio, ContinuousMap.pow_apply, ContinuousMap.smul_apply,
    smul_eq_mul, mul_pow, fourier_nat_mul]

/-- The exact Haar coefficient computation before evaluating the single-mode sums. -/
theorem poissonKernel_fourierCoeff_series (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (k : ℤ) :
    fourierCoeff (poissonKernel a) k =
      (∑' n : ℕ, (a : ℂ)^n * (if (n : ℤ) = k then 1 else 0)) +
      (∑' n : ℕ, (a : ℂ)^n * (if -(n : ℤ) = k then 1 else 0)) -
      (if k = 0 then 1 else 0) := by
  rw [← coefficientCLM_apply]
  simp only [poissonKernel, map_sub, map_add]
  rw [(coefficientCLM k).map_tsum (poissonRatio_summable a 1 ha ha1),
    (coefficientCLM k).map_tsum (poissonRatio_summable a (-1) ha ha1)]
  simp only [poissonRatio_pow, map_smul, smul_eq_mul, mul_one, mul_neg_one,
    coefficientCLM_fourier]
  have hconst : coefficientCLM k (1 : CircleFunction) = if k = 0 then 1 else 0 := by
    have hzero : (1 : CircleFunction) = fourier (0 : ℤ) := by ext x; simp [fourier_zero]
    rw [hzero, coefficientCLM_fourier]
    simp only [eq_comm]
  rw [hconst]

/-- Both positive and negative modes are present, and the constant mode is one. -/
theorem poissonKernel_fourierCoeff (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (k : ℤ) :
    fourierCoeff (poissonKernel a) k = (a : ℂ)^k.natAbs := by
  rw [poissonKernel_fourierCoeff_series a ha ha1 k]
  cases k with
  | ofNat k =>
      simp only [Int.ofNat_eq_natCast]
      have hp : (∑' n : ℕ, (a : ℂ)^n * (if (n : ℤ) = (k : ℤ) then 1 else 0)) =
          (a : ℂ)^k := by
        rw [tsum_eq_single k]
        · simp
        · intro n hn
          have : (n : ℤ) ≠ (k : ℤ) := by exact_mod_cast hn
          simp [this]
      rw [hp]
      cases k with
      | zero =>
          have hn : (∑' n : ℕ, (a : ℂ)^n * (if -(n : ℤ) = 0 then 1 else 0)) = 1 := by
            rw [tsum_eq_single 0]
            · simp
            · intro n hn
              have : -(n : ℤ) ≠ 0 := by
                intro h
                apply hn
                exact_mod_cast (neg_eq_zero.mp h)
              simp [this]
          simp [hn]
      | succ k =>
          have hn : (∑' n : ℕ, (a : ℂ)^n *
              (if -(n : ℤ) = ((k + 1 : ℕ) : ℤ) then 1 else 0)) = 0 := by
            calc
              _ = ∑' _n : ℕ, (0 : ℂ) := tsum_congr (fun n => by
                have hne : -(n : ℤ) ≠ ((k + 1 : ℕ) : ℤ) := by omega
                simp only [if_neg hne, mul_zero])
              _ = 0 := tsum_zero
          rw [hn]
          have hkz : ((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
          simp only [if_neg hkz, Int.natAbs_natCast, add_zero, sub_zero]
  | negSucc k =>
      have hp : (∑' n : ℕ, (a : ℂ)^n *
          (if (n : ℤ) = Int.negSucc k then 1 else 0)) = 0 := by
        calc
          _ = ∑' _n : ℕ, (0 : ℂ) := tsum_congr (fun n => by
            have hne : (n : ℤ) ≠ Int.negSucc k := by omega
            simp only [if_neg hne, mul_zero])
          _ = 0 := tsum_zero
      have hn : (∑' n : ℕ, (a : ℂ)^n *
          (if -(n : ℤ) = Int.negSucc k then 1 else 0)) = (a : ℂ)^(k+1) := by
        rw [tsum_eq_single (k+1)]
        · have heq : -((k + 1 : ℕ) : ℤ) = Int.negSucc k := by omega
          simp only [heq, if_pos rfl, if_true, mul_one]
        · intro n hn
          have : -(n : ℤ) ≠ Int.negSucc k := by omega
          simp [this]
      simp [hp, hn]

/-- The real Poisson kernel written as its two geometric resolvents. -/
theorem poissonKernel_apply_resolvent (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (x : CircleSpace) :
    poissonKernel a x =
      (1 - (a : ℂ) * fourier 1 x)⁻¹ +
      (1 - (a : ℂ) * fourier (-1) x)⁻¹ - 1 := by
  have heval (sign : ℤ) :
      (∑' n : ℕ, poissonRatio a sign ^ n) x =
        (1 - (a : ℂ) * fourier sign x)⁻¹ := by
    rw [show (∑' n : ℕ, poissonRatio a sign ^ n) x =
        ∑' n : ℕ, ((a : ℂ) * fourier sign x)^n by
      simpa [poissonRatio] using
        (ContinuousMap.evalCLM ℂ x).map_tsum (poissonRatio_summable a sign ha ha1)]
    apply tsum_geometric_of_norm_lt_one
    simp [norm_mul, fourier_apply, Circle.norm_coe, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha, ha1]
  simp only [poissonKernel, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, heval]

/-- The kernel is the actual real Poisson density, not just a formal list of
Fourier coefficients. The denominator is the squared distance to `a χ₁`. -/
theorem poissonKernel_apply_real (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (x : CircleSpace) :
    poissonKernel a x =
      (((1 - a ^ 2) / ‖1 - (a : ℂ) * fourier 1 x‖ ^ 2 : ℝ) : ℂ) := by
  let z : ℂ := fourier 1 x
  let w : ℂ := 1 - (a : ℂ) * z
  have hz : ‖z‖ = 1 := by
    simp [z, fourier_apply, Circle.norm_coe]
  have haz : ‖(a : ℂ) * z‖ < 1 := by
    simpa [norm_mul, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      using ha1
  have hw : w ≠ 0 := by
    intro h
    have hmul : (a : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖(a : ℂ) * z‖ = 1 := by rw [hmul]; simp
    rw [hnorm] at haz
    exact (lt_irrefl (1 : ℝ)) haz
  have hwc : conj w ≠ 0 := by
    intro h
    apply hw
    have h' := congrArg conj h
    simpa using h'
  have hzz : z * conj z = 1 := by
    simpa [hz] using Complex.mul_conj' z
  have hnum : w + conj w - w * conj w = 1 - (a : ℂ) ^ 2 := by
    simp only [w, map_sub, map_one, map_mul, Complex.conj_ofReal]
    calc
      (1 - (a : ℂ) * z) + (1 - (a : ℂ) * conj z) -
          (1 - (a : ℂ) * z) * (1 - (a : ℂ) * conj z) =
          1 - (a : ℂ) ^ 2 * (z * conj z) := by ring
      _ = 1 - (a : ℂ) ^ 2 := by rw [hzz]; ring
  have hid : w⁻¹ + (conj w)⁻¹ - 1 =
      (1 - (a : ℂ) ^ 2) / (w * conj w) := by
    field_simp [hw, hwc]
    linear_combination hnum
  rw [poissonKernel_apply_resolvent a ha ha1 x]
  have hneg : fourier (-1 : ℤ) x = conj z := by
    simpa [z] using (fourier_neg (T := 1) (n := 1) (x := x))
  rw [hneg]
  change w⁻¹ + (1 - (a : ℂ) * conj z)⁻¹ - 1 = _
  have hconj : 1 - (a : ℂ) * conj z = conj w := by simp [w]
  rw [hconj, hid, Complex.mul_conj']
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow, w, z]

theorem poissonKernel_apply_im_zero (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (x : CircleSpace) :
    (poissonKernel a x).im = 0 := by
  rw [poissonKernel_apply_real a ha ha1 x]
  exact Complex.ofReal_im _

/-- The usual angular denominator `1 - 2 a cos θ + a²`, where the real part
of the unit circle character is `cos θ`. -/
theorem poissonKernel_apply_rational (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (x : CircleSpace) :
    poissonKernel a x =
      (((1 - a ^ 2) / (1 - 2 * a * (fourier 1 x).re + a ^ 2) : ℝ) : ℂ) := by
  have hz : ‖fourier (1 : ℤ) x‖ = 1 := by
    simp [fourier_apply, Circle.norm_coe]
  have hzz : fourier (1 : ℤ) x * conj (fourier (1 : ℤ) x) = 1 := by
    rw [Complex.mul_conj', hz]
    norm_num
  have hsq : (((‖1 - (a : ℂ) * fourier 1 x‖ ^ 2 : ℝ) : ℂ)) =
      ((1 - 2 * a * (fourier 1 x).re + a ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_sub, map_one, map_mul, Complex.conj_ofReal]
    calc
      (1 - (a : ℂ) * fourier 1 x) *
          (1 - (a : ℂ) * conj (fourier 1 x)) =
          1 - (a : ℂ) * (fourier 1 x + conj (fourier 1 x)) +
            (a : ℂ) ^ 2 * (fourier 1 x * conj (fourier 1 x)) := by ring
      _ = ((1 - 2 * a * (fourier 1 x).re + a ^ 2 : ℝ) : ℂ) := by
        rw [hzz, Complex.add_conj]
        push_cast
        ring
  have hden : ‖1 - (a : ℂ) * fourier 1 x‖ ^ 2 =
      1 - 2 * a * (fourier 1 x).re + a ^ 2 := Complex.ofReal_injective hsq
  rw [poissonKernel_apply_real a ha ha1 x, hden]

/-- Strict positivity holds pointwise for every allowed Poisson radius. -/
theorem poissonKernel_apply_re_pos (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (x : CircleSpace) :
    0 < (poissonKernel a x).re := by
  rw [poissonKernel_apply_real a ha ha1 x, Complex.ofReal_re]
  have haz : ‖(a : ℂ) * fourier 1 x‖ < 1 := by
    simpa [norm_mul, fourier_apply, Circle.norm_coe, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha] using ha1
  have hw : 1 - (a : ℂ) * fourier 1 x ≠ 0 := by
    intro h
    have hmul : (a : ℂ) * fourier 1 x = 1 := (sub_eq_zero.mp h).symm
    rw [hmul] at haz
    simpa using haz
  have hnum : 0 < 1 - a ^ 2 := by
    have hp := mul_pos (sub_pos.mpr ha1) (show 0 < 1 + a by linarith)
    nlinarith [hp]
  exact div_pos hnum (sq_pos_of_pos (norm_pos_iff.mpr hw))

/-- The positive real kernel has exactly total mass one under circle Haar. -/
theorem poissonKernel_integral_one (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    (∫ x : CircleSpace, poissonKernel a x ∂AddCircle.haarAddCircle) = 1 := by
  simpa [fourierCoeff, fourier_zero] using poissonKernel_fourierCoeff a ha ha1 0

def centeredPoissonMultiplier (a : ℝ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else (a : ℂ)^k.natAbs

/-- Centering is genuine subtraction of Haar's constant density. -/
theorem centeredPoisson_fourierCoeff (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (k : ℤ) :
    fourierCoeff
      ((poissonKernel a - (1 : CircleFunction) : CircleFunction) : CircleSpace → ℂ) k =
      centeredPoissonMultiplier a k := by
  rw [← coefficientCLM_apply, map_sub, coefficientCLM_apply,
    poissonKernel_fourierCoeff a ha ha1]
  have hconst : coefficientCLM k (1 : CircleFunction) = if k = 0 then 1 else 0 := by
    have hzero : (1 : CircleFunction) = fourier (0 : ℤ) := by ext x; simp [fourier_zero]
    rw [hzero, coefficientCLM_fourier]
    simp only [eq_comm]
  rw [hconst]
  by_cases hk : k = 0 <;> simp [centeredPoissonMultiplier, hk]

def oneZeroMultiplier (c a : ℝ) (k : ℤ) : ℂ :=
  -(c : ℂ) * centeredPoissonMultiplier a k

def balancedPoissonMultiplier (c a : ℝ) (r : ℕ) (k : ℤ) : ℂ :=
  (c : ℂ)^(2*r) * centeredPoissonMultiplier (a^(2*r)) k

/-- The full balanced power keeps both signs and exactly multiplies the
Poisson radius. With `a = p^(-1/2)`, the resulting radius is `p^(-r)`. -/
theorem oneZeroMultiplier_even_power (c a : ℝ) (r : ℕ) (hr : 0 < r) (k : ℤ) :
    oneZeroMultiplier c a k ^ (2*r) = balancedPoissonMultiplier c a r k := by
  by_cases hk : k = 0
  · have hn : 2 * r ≠ 0 := by omega
    simp only [oneZeroMultiplier, balancedPoissonMultiplier, centeredPoissonMultiplier,
      hk, if_pos rfl, if_true, mul_zero, zero_pow hn]
  · simp only [oneZeroMultiplier, balancedPoissonMultiplier, centeredPoissonMultiplier,
      if_neg hk]
    rw [mul_pow]
    have hneg : (-(c : ℂ)) ^ (2 * r) = (c : ℂ) ^ (2 * r) := by
      calc
        _ = ((-(c : ℂ)) ^ 2) ^ r := pow_mul _ 2 r
        _ = ((c : ℂ) ^ 2) ^ r := by rw [neg_sq]
        _ = _ := (pow_mul _ 2 r).symm
    rw [hneg, Complex.ofReal_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end RiemannResearch.Analysis.PoissonHaar

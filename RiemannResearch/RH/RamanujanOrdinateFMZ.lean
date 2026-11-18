import RiemannResearch.Analysis.ActualFixedFrequencyLandau
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import RiemannResearch.Analysis.ActualSelbergIngham
import RiemannResearch.RH.ParetoPacketGreenGram
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Prime-root ordinate frequencies recover classical Ramanujan sums

Ford--Zaharescu, Corollary 2 and (1.9)--(1.10),
https://arxiv.org/abs/math/0405459, give the one-dimensional prime-root
Fourier coefficient. Ford--Meng--Zaharescu, https://arxiv.org/abs/1511.06814,
provide the simultaneous torus context. The fixed modes here are derived
from the actual contour. The ordinate transfer uses sublinear horizontal
energy, implied in the repository by Selberg density at any positive exponent.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Ingham's classical inclusive count estimate implies the horizontal
energy input even with its fifth logarithmic power. -/
theorem sublinearHorizontalEnergy_of_inghamDensityBound
    (hD : InghamDensityBound) : SublinearHorizontalEnergy := by
  apply sublinearHorizontalEnergy_of_logLossDensity 1 5 (by norm_num)
  obtain ⟨C, H, hC, hH, hD⟩ := hD
  refine ⟨C, H, hC, hH, fun T hT σ hσ => ?_⟩
  have hT1 : 1 ≤ T := le_trans hH.le hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hpow : 3 * (1 - σ) / (2 - σ) ≤ 1 - (σ - 1 / 2) := by
    simpa only [zero_mul, mul_zero, add_zero, one_mul] using
      (ingham_exponent_add_gap_le (a := 1) (η := 0) (σ := σ)
        (by norm_num) le_rfl (by simpa only [add_zero] using hσ))
  have he : T ^ (1 - (σ - 1 / 2)) = T * Real.exp (-(1 * Real.log T) * (σ - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hT0]
    conv_rhs => lhs; rw [← Real.exp_log hT0]
    rw [← Real.exp_add]
    congr 1
    ring
  have hlog : (Real.log T) ^ (5 : ℝ) = (Real.log T) ^ (5 : ℕ) := Real.rpow_natCast _ 5
  calc
    _ ≤ _ := hD T hT σ hσ
    _ ≤ C * T ^ (1 - (σ - 1 / 2)) * (Real.log T) ^ (5 : ℕ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hpow) hC)
        (pow_nonneg (Real.log_nonneg hT1) _)
    _ = _ := by rw [he, hlog]; ring



/-- Angular frequency at harmonic n of the prime-root orbit of denominator d. -/
def primeRootFrequency (p d n : ℕ) : ℝ := (n : ℝ) / d * Real.log p

private theorem primeRootFrequency_pos {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hn : 0 < n) : 0 < primeRootFrequency p d n :=
  mul_pos (div_pos (by exact_mod_cast hn) (by exact_mod_cast hd))
    (Real.log_pos (by exact_mod_cast hp.one_lt))

/-- An integral Dirichlet-series resonance forces divisibility of the harmonic.
This also handles composite denominators and unreduced fractions. -/
theorem dvd_of_primeRootFrequency_eq_log {p d n k : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hn : 0 < n)
    (h : primeRootFrequency p d n = Real.log k) : d ∣ n := by
  have hk : k ≠ 0 := by
    intro h0
    subst k
    have := primeRootFrequency_pos hp hd hn
    simp at h
    linarith
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hlog : (n : ℝ)*Real.log p = (d : ℝ)*Real.log k := by
    unfold primeRootFrequency at h
    field_simp [hd'] at h
    linarith
  have he : (p : ℝ)^n = (k : ℝ)^d := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    apply Real.log_injOn_pos (show (0 : ℝ) < (p : ℝ)^n from pow_pos hpR n)
      (show (0 : ℝ) < (k : ℝ)^d from pow_pos hkR d)
    simpa only [Real.log_pow] using hlog
  have hnat : p^n = k^d := by exact_mod_cast he
  have hf := congrArg (fun v : ℕ => v.factorization p) hnat
  change (p^n).factorization p = (k^d).factorization p at hf
  rw [Nat.factorization_pow_self hp, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] at hf
  exact ⟨k.factorization p,hf⟩

/-- Signed fixed-mode main coefficient before undoing its prime weight. -/
def primeRootMain (p d n : ℕ) : ℝ :=
  if d ∣ n then -Real.log p / (2 * Real.pi * Real.sqrt (Real.exp (primeRootFrequency p d n)))
  else 0

/-- Unconditional actual centered-zero identity at every positive prime-root
frequency, including the irrational nonresonances. -/
theorem tendsto_primeRoot_landau {p d n : ℕ} (hp : p.Prime) (hd : 0 < d) (hn : 0 < n) :
    Tendsto (fun T : ℝ => landauSum T (primeRootFrequency p d n) / (T : ℂ))
      atTop (𝓝 (primeRootMain p d n : ℂ)) := by
  by_cases h : d ∣ n
  · obtain ⟨k,rfl⟩ := h
    have hk : k ≠ 0 := by intro h; simp [h] at hn
    have hk1 : 1 < p^k := one_lt_pow₀ hp.one_lt hk
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have he : primeRootFrequency p d (d*k) = Real.log ((p^k : ℕ) : ℝ) := by
      simp only [primeRootFrequency, Nat.cast_mul, Nat.cast_pow, Real.log_pow]
      field_simp
    have hp0 : (0:ℝ) < ((p^k : ℕ) : ℝ) := by exact_mod_cast (pow_pos hp.pos k)
    have hlim := tendsto_rational_landau_div (n:=p^k) (m:=1) (by decide) hk1
    rw [rationalLandauMain_eq_vonMangoldt_div_sqrt (by decide : 1 ≤ 1) hk1] at hlim
    simp only [primeRootMain, dvd_mul_right, if_true, he, Real.exp_log hp0, neg_div]
    simpa only [Nat.cast_one, div_one, one_dvd, if_true, Nat.div_one,
      ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp,
      Complex.ofReal_neg] using hlim
  · simpa [primeRootMain,h] using tendsto_landau_div_of_nonresonance
      (primeRootFrequency_pos hp hd hn)
      (fun k hlog => h (dvd_of_primeRootFrequency_eq_log hp hd hn hlog))

/-- Actual positive ordinates counted with analytic multiplicity, at height
normalization. The sole analytic premise is sublinear horizontal energy. -/
theorem tendsto_primeRoot_ordinate {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hn : 0 < n) (hE : SublinearHorizontalEnergy) :
    Tendsto (fun T : ℝ => ordinateSum T (primeRootFrequency p d n) / (T : ℂ))
      atTop (𝓝 (primeRootMain p d n : ℂ)) := by
  have h := (tendsto_ordinate_landau_error_of_sublinear_horizontal
    (primeRootFrequency p d n) hE).add (tendsto_primeRoot_landau hp hd hn)
  simp only [zero_add] at h
  convert h using 1
  funext T
  ring

/-- The normalized divisor probe uses every zero in the actual cutoff. -/
def ordinateDivisorProbe (p d n : ℕ) (T : ℝ) : ℂ :=
  let u := primeRootFrequency p d n
  ((-(2 * Real.pi * Real.sqrt (Real.exp u)) / Real.log p : ℝ) : ℂ) *
    (ordinateSum T u / (T : ℂ))

theorem tendsto_ordinateDivisorProbe {p d n : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hn : 0 < n) (hE : SublinearHorizontalEnergy) :
    Tendsto (ordinateDivisorProbe p d n) atTop (𝓝 (if d ∣ n then (1 : ℂ) else 0)) := by
  have h := (tendsto_primeRoot_ordinate hp hd hn hE).const_mul
    (((-(2 * Real.pi * Real.sqrt (Real.exp (primeRootFrequency p d n))) / Real.log p : ℝ) : ℂ))
  have hl : Real.log (p:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hs : Real.sqrt (Real.exp (primeRootFrequency p d n)) ≠ 0 :=
    (Real.sqrt_pos.2 (Real.exp_pos _)).ne'
  unfold ordinateDivisorProbe
  convert h using 1
  apply congrArg nhds
  by_cases hdn : d ∣ n
  · simp only [primeRootMain,hdn,if_true]
    norm_cast
    field_simp [hl,hs,Real.pi_ne_zero]
  · simp [primeRootMain,hdn]

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ActualZeroOrdinate

/-- Möbius synthesis of the divisor probes into the repository's actual
Ramanujan sum. No squarefreeness, simplicity, or critical-line premise. -/
theorem tendsto_ramanujanSum_ordinateProbes {p n : ℕ} (q : ℕ)
    (hp : p.Prime) (hn : 0 < n) (hE : SublinearHorizontalEnergy) :
    Tendsto (fun T : ℝ => ∑ d ∈ q.divisors,
      ((ArithmeticFunction.moebius (q/d) : ℂ) * (d : ℂ)) * ordinateDivisorProbe p d n T)
      atTop (𝓝 (ramanujanSum q n : ℂ)) := by
  have h := tendsto_finsetSum q.divisors fun d hd =>
    (tendsto_ordinateDivisorProbe hp (Nat.pos_of_mem_divisors hd) hn hE).const_mul
      ((ArithmeticFunction.moebius (q/d) : ℂ) * (d : ℂ))
  convert h using 1
  apply congrArg nhds
  unfold ramanujanSum
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n <;> simp [hdn]


/-- The signed finite prefix recovers the integrated packet used in the
Green Gram identities, with the same height T for all of its modes. -/
theorem tendsto_ramanujanPacket_ordinateProbes {p q : ℕ} (k : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hE : SublinearHorizontalEnergy) :
    Tendsto (fun T : ℝ => -(∑ n ∈ Finset.Ico 1 (k+1), ∑ d ∈ q.divisors,
      ((ArithmeticFunction.moebius (q/d) : ℂ) * (d : ℂ)) * ordinateDivisorProbe p d n T))
      atTop (𝓝 (ramanujanPacket q k : ℂ)) := by
  have h := (tendsto_finsetSum (Finset.Ico 1 (k+1)) (fun n hn =>
    tendsto_ramanujanSum_ordinateProbes q hp (Finset.mem_Ico.mp hn).1 hE)).neg
  rw [ramanujanPacket_prefix q k hq]
  simpa only [Complex.ofReal_neg, Complex.ofReal_sum] using h


end RiemannResearch.RH.Pareto

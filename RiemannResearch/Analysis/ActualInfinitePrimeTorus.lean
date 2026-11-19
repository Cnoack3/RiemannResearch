import RiemannResearch.Analysis.CompactGaugeOrbitLaw
import RiemannResearch.Analysis.ActualPrimeTorusFMZ
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannResearch.Analysis.InfiniteTorusCharacters
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroFixedStripConcentration
import RiemannResearch.Analysis.ActualFixedFrequencyLandau
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.FinitePrimeModeArithmetic
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.Analysis.PrimePhaseTorus
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual multiplicity-weighted laws on the infinite prime torus

Source: the user-requested actual-zero specialization of the compact-orbit
transfer. The atoms are actual zeta zeros and every analytic multiplicity is
retained through ActualZeroOrdinate.Copies. Empty cutoffs are completed by
the Dirac probability at the identity. The count-normalized horizontal second
moment and fixed-frequency Landau theorem give unconditional Haar character
limits. Their dense span identifies the full prime-torus law and its
continuous Hilbert-orbit pushforward.
-/

noncomputable section
open MeasureTheory Filter Zeta23
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate CompactCharacter CompactGaugeOrbitLaw

local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace HilbertSpace := borel HilbertSpace
local instance : BorelSpace HilbertSpace := ⟨rfl⟩

/-- All prime phases of a real ordinate, simultaneously. -/
def phasePoint (t : ℝ) : PrimeTorus :=
  fun p => Circle.exp (Real.log (p : ℕ) * t)

/-- One equal-weight atom per analytic zero copy. -/
def rawEmpiricalMeasure (T : ℝ) : Measure PrimeTorus :=
  ∑ c : Copies T, ENNReal.ofReal ((Ncount 0 T : ℝ)⁻¹) •
    Measure.dirac (phasePoint c.1.1.im)

theorem rawEmpiricalMeasure_isProbability (T : ℝ) (hN : 0 < Ncount 0 T) :
    IsProbabilityMeasure (rawEmpiricalMeasure T) := by
  constructor
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  simp only [rawEmpiricalMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  simp [hn]

/-- A probability at every height, using the identity atom for empty cutoffs. -/
def empiricalProbability (T : ℝ) : ProbabilityMeasure PrimeTorus :=
  if hN : 0 < Ncount 0 T then
    ⟨rawEmpiricalMeasure T, rawEmpiricalMeasure_isProbability T hN⟩
  else ⟨Measure.dirac 1, inferInstance⟩

theorem empiricalProbability_eq_raw (T : ℝ) (hN : 0 < Ncount 0 T) :
    (empiricalProbability T : Measure PrimeTorus) = rawEmpiricalMeasure T := by
  simp [empiricalProbability, hN]

/-- Exact multiplicity-weighted integral identity; no continuity premise is needed. -/
theorem integral_empiricalProbability (T : ℝ) (hN : 0 < Ncount 0 T)
    (f : PrimeTorus → ℂ) :
    (∫ z, f z ∂empiricalProbability T) =
      sum T (fun ρ => f (phasePoint ρ.im)) / (Ncount 0 T : ℂ) := by
  rw [empiricalProbability_eq_raw T hN]
  unfold rawEmpiricalMeasure
  rw [integral_finsetSum_measure (fun c _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Ncount 0 T : ℝ)⁻¹),
    sum_eq_copies, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [Finset.mul_sum]

/-- The finite prime set appearing in a word; repeated coordinates occur once. -/
def wordPrimes (s : List (Nat.Primes × ℤ)) : Finset ℕ :=
  (s.map (fun a => (a.1 : ℕ))).toFinset

/-- Exponents at repeated prime coordinates are added, including cancellation. -/
def wordMode : List (Nat.Primes × ℤ) → ℕ → ℤ
  | [] => fun _ => 0
  | (p,k) :: s => fun n => (if n = (p : ℕ) then k else 0) + wordMode s n

def wordFrequency : List (Nat.Primes × ℤ) → ℝ
  | [] => 0
  | (p,k) :: s => (k : ℝ) * Real.log (p : ℕ) + wordFrequency s

theorem wordPrimes_prime (s : List (Nat.Primes × ℤ)) :
    ∀ p ∈ wordPrimes s, p.Prime := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact a.1.property

theorem wordFrequency_eq_sum (s : List (Nat.Primes × ℤ)) (P : Finset ℕ)
    (hP : ∀ a ∈ s, (a.1 : ℕ) ∈ P) :
    wordFrequency s = ∑ p ∈ P, (wordMode s p : ℝ) * Real.log p := by
  induction s with
  | nil => simp [wordFrequency, wordMode]
  | cons a s ih =>
    rcases a with ⟨p,k⟩
    have hp : (p : ℕ) ∈ P := hP (p,k) (by simp)
    have hs : ∀ a ∈ s, (a.1 : ℕ) ∈ P := fun a ha => hP a (by simp [ha])
    simp only [wordFrequency, wordMode, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← ih hs]
    simp [hp]


theorem coordinatePower_phasePoint (p : Nat.Primes) (k : ℤ) (t : ℝ) :
    coordinatePower p k (phasePoint t) =
      fourier k (PrimePhaseTorus.primePhase (p : ℕ) t) := by
  change (((Circle.exp (Real.log (p : ℕ) * t)) ^ k : Circle) : ℂ) = _
  rw [← Circle.exp_zsmul, Circle.coe_exp, PrimePhaseTorus.fourier_primePhase]
  congr 1
  simp only [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

theorem character_phasePoint (s : List (Nat.Primes × ℤ)) (t : ℝ) :
    character s (phasePoint t) = ZeroOrdinate.phase (wordFrequency s) t := by
  induction s with
  | nil => simp [character, wordFrequency, ZeroOrdinate.phase]
  | cons a s ih =>
    rcases a with ⟨p,k⟩
    simp only [character, ContinuousMap.mul_apply, coordinatePower_phasePoint, ih]
    rw [PrimePhaseTorus.fourier_primePhase]
    simp only [ZeroOrdinate.phase, wordFrequency]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Every word is exactly the existing finite-prime character on its prime set. -/
theorem character_phasePoint_eq_finite (s : List (Nat.Primes × ℤ)) (t : ℝ) :
    character s (phasePoint t) =
      PrimeTorusHaar.character (fun p : wordPrimes s => wordMode s p)
        (PrimeTorusHaar.primeOrbit (wordPrimes s) t) := by
  rw [character_phasePoint, ActualPrimeTorusFMZ.character_primeOrbit_eq_phase]
  congr 1
  exact wordFrequency_eq_sum s (wordPrimes s) (fun a ha => by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))

/-- Exact bridge to the existing multiplicity-weighted finite-prime sums. -/
theorem integral_character_eq_sampleFunctional (s : List (Nat.Primes × ℤ))
    (T : ℝ) (hN : 0 < Ncount 0 T) :
    (∫ z, character s z ∂empiricalProbability T) =
      ActualPrimeTorusFMZ.sampleFunctional (wordPrimes s) T
        (PrimeTorusHaar.character (fun p : wordPrimes s => wordMode s p)) /
          (Ncount 0 T : ℂ) := by
  rw [integral_empiricalProbability T hN]
  simp_rw [character_phasePoint_eq_finite]
  rfl

/-- The finite product-Haar moment associated with a word. -/
def haarMoment (s : List (Nat.Primes × ℤ)) : ℂ :=
  PrimeTorusHaar.haarIntegral
    (PrimeTorusHaar.character (fun p : wordPrimes s => wordMode s p))

theorem haarMoment_eq (s : List (Nat.Primes × ℤ)) :
    haarMoment s = if (fun p : wordPrimes s => wordMode s p) = 0 then 1 else 0 := by
  exact PrimeTorusHaar.haarIntegral_character_eq _


/-- Exact normalization identity before taking the limit: the signed order-height
correction is preserved even when it is nonzero. -/
theorem integral_character_centered_identity (s : List (Nat.Primes × ℤ))
    (T : ℝ) (hN : 0 < Ncount 0 T) (hT : T ≠ 0) :
    (∫ z, character s z ∂empiricalProbability T) = haarMoment s +
      ((T : ℂ) / (Ncount 0 T : ℂ)) *
        ((ActualPrimeTorusFMZ.sampleFunctional (wordPrimes s) T
          (PrimeTorusHaar.character (fun p : wordPrimes s => wordMode s p)) -
          (Ncount 0 T : ℂ) * haarMoment s) / (T : ℂ)) := by
  rw [integral_character_eq_sampleFunctional s T hN]
  apply normalized_centered_identity
  · exact_mod_cast hN.ne'
  · exact_mod_cast hT

/-- Every word character has its product-Haar moment. The actual count-normalized
second moment supplies the fixed-strip hypothesis for the ordinate Fourier modes. -/
theorem tendsto_integral_character (s : List (Nat.Primes × ℤ)) :
    Tendsto (fun T : ℝ => ∫ z, character s z ∂empiricalProbability T)
      atTop (𝓝 (haarMoment s)) := by
  let P := wordPrimes s
  let k := wordMode s
  let u := PrimePhaseTorus.primeFrequency P k
  have he : ((fun p : P => k p) = 0) ↔ u = 0 :=
    (ActualPrimeTorusFMZ.restrictedMode_eq_zero_iff P k).trans
      (PrimePhaseTorus.primeFrequency_eq_zero_iff P k (wordPrimes_prime s)).symm
  have ha : ∀ᶠ T : ℝ in atTop, (∫ z, character s z ∂empiricalProbability T) =
      ordinateSum T u / (Ncount 0 T : ℂ) := by
    filter_upwards [eventually_count_pos] with T hN
    rw [integral_character_eq_sampleFunctional s T hN,
      ActualPrimeTorusFMZ.sampleFunctional_character]
  rw [haarMoment_eq]
  change Tendsto _ atTop (𝓝 (if (fun p : P => k p) = 0 then 1 else 0))
  by_cases hu : u = 0
  · rw [if_pos (he.mpr hu)]
    apply tendsto_const_nhds.congr'
    filter_upwards [ha,eventually_count_pos] with T hi hN
    have hn : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [hi, hu, ordinateSum_zero, hn]
  · rw [if_neg (fun h => hu (he.mp h))]
    have hE : Tendsto (fun T : ℝ => horizontalEnergy T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
      simpa only [show 1+1 = (2:ℕ) by decide, displacementMoment_two] using
        tendsto_displacementMoment 1
    have hstrip := fixedStrip_of_relativeEnergy_tendsto_zero hE
    have hmode : Tendsto (fun T : ℝ => ordinateSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
      rcases lt_or_gt_of_ne hu with hneg | hpos
      · simpa [ordinateSum_neg] using
          (tendsto_ordinate_div_count_of_pos (neg_pos.mpr hneg) hstrip).star
      · exact tendsto_ordinate_div_count_of_pos hpos hstrip
    exact hmode.congr' (ha.mono fun _ h => h.symm)

/-- The actual zero-copy laws converge on the infinite prime torus and on
every fixed Hilbert orbit. All finite joint Haar moments are identified. -/
theorem existsUnique_actual_orbit_limit
    (h : HilbertSpace) :
    ∃! ν : ProbabilityMeasure PrimeTorus,
      (∀ s, ∫ z, character s z ∂ν = haarMoment s) ∧
      Tendsto empiricalProbability atTop (𝓝 ν) ∧
      Tendsto (fun T => orbitLaw h (empiricalProbability T)) atTop
        (𝓝 (orbitLaw h ν)) :=
  existsUnique_orbit_limit h empiricalProbability haarMoment tendsto_integral_character

end RiemannResearch.Analysis.ActualInfinitePrimeTorus

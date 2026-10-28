/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PoissonHaarSpecialization
import RiemannResearch.Analysis.PrimePhaseTorus
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite prime-torus Haar and Poisson specialization

The reference Haar measure is the actual finite product of normalized circle
Haar measures. The signed FMZ density is a sum of centered Poisson kernels on
the coordinate axes. All of its character integrals are evaluated here from
Fubini and the previously proved circle Poisson coefficients.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeTorusHaar
open RiemannResearch.Analysis.PoissonHaar
open RiemannResearch.Analysis.ZeroOrdinate

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Torus (ι : Type*) := ι → CircleSpace

def haar (ι : Type*) [Fintype ι] : Measure (Torus ι) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle (T := 1))

instance haar_isProbabilityMeasure : IsProbabilityMeasure (haar ι) := by
  unfold haar
  infer_instance

def coordinate (i : ι) : C(Torus ι, CircleSpace) :=
  ⟨fun x => x i, continuous_apply i⟩

def character (k : ι → ℤ) : C(Torus ι, ℂ) :=
  ∏ i, (fourier (k i)).comp (coordinate i)

@[simp] theorem character_apply (k : ι → ℤ) (x : Torus ι) :
    character k x = ∏ i, fourier (k i) (x i) := by
  simp [character, coordinate]

def haarIntegral : C(Torus ι, ℂ) →ₗ[ℂ] ℂ := probabilityIntegral (haar ι)

@[simp] theorem haarIntegral_apply (f : C(Torus ι, ℂ)) :
    haarIntegral f = ∫ x, f x ∂haar ι := rfl

theorem haarIntegral_character (k : ι → ℤ) :
    haarIntegral (character k) = ∏ i, (if k i = 0 then (1 : ℂ) else 0) := by
  rw [haarIntegral_apply]
  simp only [character_apply, haar]
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact haarIntegral_fourier (k i)

theorem haarIntegral_character_eq (k : ι → ℤ) :
    haarIntegral (character k) = if k = 0 then 1 else 0 := by
  rw [haarIntegral_character]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Each summand is a signed centered Poisson kernel on one coordinate. -/
def density (c a : ι → ℝ) : C(Torus ι, ℂ) :=
  ∑ i, -(c i : ℂ) • ((poissonKernel (a i)).comp (coordinate i) - 1)

@[simp] theorem density_apply (c a : ι → ℝ) (x : Torus ι) :
    density c a x = ∑ i, -(c i : ℂ) * (poissonKernel (a i) (x i) - 1) := by
  simp [density, coordinate]

def axisMultiplier (c a : ι → ℝ) (k : ι → ℤ) : ℂ :=
  ∑ i, -(c i : ℂ) * ∏ j,
    if j = i then centeredPoissonMultiplier (a i) (k j)
    else if k j = 0 then 1 else 0

private theorem circle_centered_integral (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (k : ℤ) :
    (∫ x : CircleSpace, fourier k x * (poissonKernel a x - 1)
      ∂AddCircle.haarAddCircle) = centeredPoissonMultiplier a k := by
  have h := centeredPoisson_fourierCoeff a ha ha1 (-k)
  simpa [fourierCoeff, smul_eq_mul, centeredPoissonMultiplier] using h

theorem haarIntegral_character_centered (k : ι → ℤ) (i : ι)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    haarIntegral (character k * ((poissonKernel a).comp (coordinate i) - 1)) =
      ∏ j, if j = i then centeredPoissonMultiplier a (k j)
        else if k j = 0 then 1 else 0 := by
  have hprod (x : Torus ι) :
      character k x * (poissonKernel a (x i) - 1) =
        ∏ j, (fourier (k j) (x j) *
          if j = i then poissonKernel a (x j) - 1 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [character_apply]
  rw [haarIntegral_apply]
  change (∫ x : Torus ι, character k x * (poissonKernel a (x i) - 1)
    ∂haar ι) = _
  simp_rw [hprod]
  rw [haar, integral_fintype_prod_eq_prod (fun j (y : CircleSpace) =>
    fourier (k j) y * if j = i then poissonKernel a y - 1 else 1)]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · simp only [hji, if_pos rfl]
    exact circle_centered_integral a ha ha1 (k i)
  · simp only [hji, if_false, mul_one]
    exact haarIntegral_fourier (k j)

/-- The actual product-Haar integral, with every off-axis character retained.
Its explicit product vanishes unless a frequency is supported on one axis. -/
theorem haarIntegral_character_density (c a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) (k : ι → ℤ) :
    haarIntegral (character k * density c a) = axisMultiplier c a k := by
  classical
  simp only [density, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    smul_eq_mul, haarIntegral_character_centered k _ _ (ha _) (ha1 _),
    axisMultiplier]

@[simp] theorem axisMultiplier_zero (c a : ι → ℝ) :
    axisMultiplier c a 0 = 0 := by
  unfold axisMultiplier
  apply Finset.sum_eq_zero
  intro i hi
  have hz : (∏ j : ι, if j = i then centeredPoissonMultiplier (a i) (0 : ℤ)
      else if (0 : ℤ) = 0 then (1 : ℂ) else 0) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [centeredPoissonMultiplier])
  simpa using congrArg (fun z : ℂ => -(c i : ℂ) * z) hz

/-- A frequency on a single coordinate has exactly the circle coefficient. -/
theorem axisMultiplier_single (c a : ι → ℝ) (i : ι) (n : ℤ) :
    axisMultiplier c a (Pi.single i n) =
      -(c i : ℂ) * centeredPoissonMultiplier (a i) n := by
  unfold axisMultiplier
  rw [Finset.sum_eq_single i]
  · congr 1
    have hp : (∏ j : ι, if j = i then
        centeredPoissonMultiplier (a i) ((Pi.single i n : ι → ℤ) j)
        else if (Pi.single i n : ι → ℤ) j = 0 then (1 : ℂ) else 0) =
        ∏ j : ι, if j = i then centeredPoissonMultiplier (a i) n else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · simp [hji, Pi.single_apply, Ne.symm hji]
    rw [hp]
    simp
  · intro j hj hji
    have hz : (∏ l : ι, if l = j then
        centeredPoissonMultiplier (a j) ((Pi.single i n : ι → ℤ) l)
        else if (Pi.single i n : ι → ℤ) l = 0 then (1 : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Pi.single_apply, hji, Ne.symm hji, centeredPoissonMultiplier]
    rw [hz, mul_zero]
  · simp

/-- Every genuinely mixed character has zero signed Poisson correction. -/
theorem axisMultiplier_eq_zero_of_two_nonzero (c a : ι → ℝ) (k : ι → ℤ)
    (i l : ι) (hil : i ≠ l) (hi : k i ≠ 0) (hl : k l ≠ 0) :
    axisMultiplier c a k = 0 := by
  unfold axisMultiplier
  apply Finset.sum_eq_zero
  intro j hj
  suffices hz : (∏ q : ι, if q = j then centeredPoissonMultiplier (a j) (k q)
      else if k q = 0 then (1 : ℂ) else 0) = 0 by rw [hz, mul_zero]
  by_cases hji : j = i
  · subst j
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp [Ne.symm hil, hl]
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Ne.symm hji, hi]

/-- The signed density has zero total mass under the actual product Haar measure. -/
theorem haarIntegral_density (c a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) :
    haarIntegral (density c a) = 0 := by
  have h := haarIntegral_character_density c a ha ha1 (0 : ι → ℤ)
  have hc : character (0 : ι → ℤ) = 1 := by ext x; simp [fourier_zero]
  simpa [hc] using h

theorem density_apply_poisson (c a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) (x : Torus ι) :
    density c a x = ∑ i, -(c i : ℂ) *
      (((1 - (a i) ^ 2) /
        (1 - 2 * a i * (fourier 1 (x i)).re + (a i) ^ 2) : ℝ) - 1 : ℂ) := by
  rw [density_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [poissonKernel_apply_rational (a i) (ha i) (ha1 i) (x i)]

def primeRadius (p : ℕ) : ℝ := (Real.sqrt (p : ℝ))⁻¹

theorem primeRadius_nonneg (p : ℕ) : 0 ≤ primeRadius p := by
  unfold primeRadius
  positivity

theorem primeRadius_lt_one {p : ℕ} (hp : p.Prime) : primeRadius p < 1 := by
  unfold primeRadius
  apply inv_lt_one_of_one_lt₀
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hnonneg := Real.sqrt_nonneg (p : ℝ)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  nlinarith

def primeOrbit (P : Finset ℕ) (t : ℝ) : Torus P :=
  fun p => PrimePhaseTorus.primePhase (p : ℕ) t

theorem character_primeOrbit (P : Finset ℕ) (k : ℕ → ℤ) (t : ℝ) :
    character (fun p : P => k p) (primeOrbit P t) =
      ∏ p ∈ P, fourier (k p) (PrimePhaseTorus.primePhase p t) := by
  rw [character_apply]
  exact Finset.prod_coe_sort P
    (fun p : ℕ => fourier (k p) (PrimePhaseTorus.primePhase p t))

/-- A continuous product window on the actual finite prime torus. -/
def productTest (f : ι → CircleFunction) : C(Torus ι, ℂ) :=
  ∏ i, (f i).comp (coordinate i)

omit [DecidableEq ι] in
@[simp] theorem productTest_apply (f : ι → CircleFunction) (x : Torus ι) :
    productTest f x = ∏ i, f i (x i) := by
  simp [productTest, coordinate]

omit [DecidableEq ι] in
/-- Product-Haar mass factors exactly into the coordinate masses. -/
theorem haarIntegral_productTest (f : ι → CircleFunction) :
    haarIntegral (productTest f) = ∏ i, PoissonHaar.haarIntegralCLM (f i) := by
  classical
  rw [haarIntegral_apply]
  simp only [productTest_apply, haar]
  rw [integral_fintype_prod_eq_prod]
  rfl

/-- The exact contribution of one centered coordinate kernel. -/
theorem haarIntegral_productTest_centered (f : ι → CircleFunction)
    (i : ι) (a : ℝ) :
    haarIntegral (productTest f * ((poissonKernel a).comp (coordinate i) - 1)) =
      ∏ j, if j = i then PoissonHaar.haarIntegralCLM (f j * (poissonKernel a - 1))
        else PoissonHaar.haarIntegralCLM (f j) := by
  have hprod (x : Torus ι) :
      productTest f x * (poissonKernel a (x i) - 1) =
        ∏ j, (f j (x j) * if j = i then poissonKernel a (x j) - 1 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [productTest_apply]
  rw [haarIntegral_apply]
  change (∫ x : Torus ι, productTest f x * (poissonKernel a (x i) - 1)
    ∂haar ι) = _
  simp_rw [hprod]
  rw [haar, integral_fintype_prod_eq_prod (fun j (y : CircleSpace) =>
    f j y * if j = i then poissonKernel a y - 1 else 1)]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · simp only [hji]
    rfl
  · simp only [hji, if_false, mul_one]
    rfl

/-- Complete signed first correction for a product window. Every unaltered
coordinate mean is retained, so vanishing means can be used without division. -/
theorem haarIntegral_productTest_density (f : ι → CircleFunction) (c a : ι → ℝ) :
    haarIntegral (productTest f * density c a) =
      ∑ i, -(c i : ℂ) * ∏ j,
        if j = i then PoissonHaar.haarIntegralCLM (f j * (poissonKernel (a i) - 1))
        else PoissonHaar.haarIntegralCLM (f j) := by
  simp only [density, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    smul_eq_mul, haarIntegral_productTest_centered]

omit [DecidableEq ι] in
/-- One centered coordinate kills the Haar mean of the whole product. -/
theorem haarIntegral_productTest_eq_zero (f : ι → CircleFunction)
    (i : ι) (hi : PoissonHaar.haarIntegralCLM (f i) = 0) :
    haarIntegral (productTest f) = 0 := by
  rw [haarIntegral_productTest]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

omit [DecidableEq ι] in
/-- Two distinct centered factors kill the entire signed first correction,
including every Poisson harmonic on every coordinate. -/
theorem haarIntegral_productTest_density_eq_zero_of_two_centered
    (f : ι → CircleFunction) (c a : ι → ℝ) (i l : ι) (hil : i ≠ l)
    (hi : PoissonHaar.haarIntegralCLM (f i) = 0)
    (hl : PoissonHaar.haarIntegralCLM (f l) = 0) :
    haarIntegral (productTest f * density c a) = 0 := by
  classical
  rw [haarIntegral_productTest_density]
  apply Finset.sum_eq_zero
  intro j hj
  suffices hz : (∏ q : ι,
      if q = j then PoissonHaar.haarIntegralCLM (f q * (poissonKernel (a j) - 1))
      else PoissonHaar.haarIntegralCLM (f q)) = 0 by rw [hz, mul_zero]
  by_cases hji : j = i
  · subst j
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp [Ne.symm hil, hl]
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Ne.symm hji, hi]

end RiemannResearch.Analysis.PrimeTorusHaar

#print axioms RiemannResearch.Analysis.PrimeTorusHaar.haarIntegral_character_density

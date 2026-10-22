import RiemannResearch.Analysis.OrthogonalAffineSeries
import RiemannResearch.RH.ParetoRoughTailCertificates

/-!
# The actual infinite averaged coprime tail certificate

Source: continuation of the user-provided Pareto capacity formalization
(2026-09-21), whose scope section explicitly left the infinite vector and
its infinite-family equality characterization unfinished.
The normalized reciprocal-energy series is constructed in the original
Pareto Hilbert space. It minimizes over this orthogonal coprime family;
its excess over the unrestricted finite-dictionary minimum is retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.Analysis.OrthogonalAffineSeries
open RiemannResearch.RH.ArithmeticCumulative

/-- Indices of the disjoint odd two-point vectors for the support modulus P. -/
abbrev CoprimeCertificateIndex (P : ℕ) := {k : ℕ // coprimePairIndex P (k + 2)}

def coprimeCertificateFamily (P : ℕ) (i : CoprimeCertificateIndex P) : ThresholdHilbert :=
  differenceCertificate i.val

theorem coprimeCertificateFamily_orthogonal (P : ℕ) :
    Pairwise (fun i j : CoprimeCertificateIndex P =>
      inner ℝ (coprimeCertificateFamily P i) (coprimeCertificateFamily P j) = 0) := by
  intro i j hij
  apply differenceCertificate_orthogonal
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hi := i.property.2.1
  have hj := j.property.2.1
  omega

theorem coprimeCertificateFamily_ne_zero (P : ℕ) (i : CoprimeCertificateIndex P) :
    coprimeCertificateFamily P i ≠ 0 := by
  intro h
  have hn := differenceCertificate_norm_sq i.val
  change ‖coprimeCertificateFamily P i‖ ^ 2 = _ at hn
  rw [h, norm_zero, zero_pow (by decide)] at hn
  have hp : 0 < 2 * ((i.val : ℝ) + 2) ^ 2 := by positivity
  linarith

private theorem coprimeShiftMass_hasSum (P : ℕ) :
    HasSum (fun k => coprimePairMass P (k + 2)) (∑' p, coprimePairMass P p) := by
  apply (hasSum_nat_add_iff 2).mpr
  have hz : (∑ k ∈ Finset.range 2, coprimePairMass P k) = 0 := by
    norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
  rw [hz, add_zero]
  exact (coprimePairMass_summable P).hasSum

private theorem reciprocalEnergy_indicator (P : ℕ) :
    Set.indicator {k : ℕ | coprimePairIndex P (k + 2)}
      (fun k => (2 * ((k : ℝ) + 2) ^ 2)⁻¹) =
      fun k => coprimePairMass P (k + 2) / 2 := by
  funext k
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, coprimePairMass]
  split_ifs <;> simp [mul_inv_rev, div_eq_mul_inv]

theorem coprimeCertificate_reciprocalEnergy_summable (P : ℕ) :
    Summable (fun i : CoprimeCertificateIndex P =>
      (‖coprimeCertificateFamily P i‖ ^ 2)⁻¹) := by
  simp only [coprimeCertificateFamily, differenceCertificate_norm_sq]
  apply (summable_subtype_iff_indicator (s := {k : ℕ | coprimePairIndex P (k + 2)})
    (f := fun k : ℕ => (2 * ((k : ℝ) + 2) ^ 2)⁻¹)).mpr
  rw [reciprocalEnergy_indicator]
  exact (coprimeShiftMass_hasSum P).summable.div_const 2

/-- Exact mass of the entire infinite coprime certificate family. -/
theorem coprimeCertificate_reciprocalEnergyMass (P : ℕ) :
    reciprocalEnergyMass (coprimeCertificateFamily P) =
      (∑' p, coprimePairMass P p) / 2 := by
  unfold reciprocalEnergyMass
  simp only [coprimeCertificateFamily, differenceCertificate_norm_sq]
  calc
    _ = ∑' k : ℕ, Set.indicator {k : ℕ | coprimePairIndex P (k + 2)}
        (fun k : ℕ => (2 * ((k : ℝ) + 2) ^ 2)⁻¹) k := by
      exact tsum_subtype {k : ℕ | coprimePairIndex P (k + 2)}
        (fun k : ℕ => (2 * ((k : ℝ) + 2) ^ 2)⁻¹)
    _ = _ := by
      rw [reciprocalEnergy_indicator, tsum_div_const, (coprimeShiftMass_hasSum P).tsum_eq]

theorem coprimeCertificate_reciprocalEnergyMass_pos (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    0 < reciprocalEnergyMass (coprimeCertificateFamily P) := by
  rw [coprimeCertificate_reciprocalEnergyMass]
  exact div_pos (coprimePairMass_tsum_pos P hP h2) (by norm_num)

/-- The actual normalized infinite Hilbert sum, not merely its scalar bound. -/
def infiniteCoprimeCertificate (P : ℕ) : ThresholdHilbert :=
  affineMinimum (coprimeCertificateFamily P)

theorem infiniteCoprimeCertificate_hasSum (P : ℕ) :
    HasSum (fun i : CoprimeCertificateIndex P =>
      ((reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹ *
        (‖coprimeCertificateFamily P i‖ ^ 2)⁻¹) • coprimeCertificateFamily P i)
      (infiniteCoprimeCertificate P) :=
  affineMinimum_hasSum (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)


/-- The infinite vector still has no first-coordinate component. -/
theorem infiniteCoprimeCertificate_inner_firstPoint (P : ℕ) :
    inner ℝ (infiniteCoprimeCertificate P) (paretoPointHilbert 0) = 0 := by
  have hi (k : CoprimeCertificateIndex P) :
      inner ℝ (paretoPointHilbert 0) (coprimeCertificateFamily P k) = 0 := by
    rw [real_inner_comm]
    apply differenceCertificate_inner_firstPoint
    have hk := k.property.1
    omega
  have h := (innerSL ℝ (paretoPointHilbert 0)).hasSum
    (infiniteCoprimeCertificate_hasSum P)
  change HasSum (fun k : CoprimeCertificateIndex P =>
    inner ℝ (paretoPointHilbert 0)
      (((reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹ *
        (‖coprimeCertificateFamily P k‖ ^ 2)⁻¹) • coprimeCertificateFamily P k))
    (inner ℝ (paretoPointHilbert 0) (infiniteCoprimeCertificate P)) at h
  simp only [inner_smul_right, hi, mul_zero] at h
  rw [real_inner_comm]
  exact h.unique hasSum_zero

theorem infiniteCoprimeCertificate_coefficients_hasSum (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    HasSum (fun i : CoprimeCertificateIndex P =>
      (reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹ *
        (‖coprimeCertificateFamily P i‖ ^ 2)⁻¹) 1 :=
  affineMinimum_coefficients_hasSum (coprimeCertificate_reciprocalEnergy_summable P)
    (ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2))

theorem infiniteCoprimeCertificate_norm_sq (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    ‖infiniteCoprimeCertificate P‖ ^ 2 =
      2 / (coprimeReciprocalSquareMass P - 1) := by
  rw [infiniteCoprimeCertificate,
    affineMinimum_norm_sq (coprimeCertificateFamily_orthogonal P)
      (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
      (ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2)),
    coprimeCertificate_reciprocalEnergyMass, coprimeReciprocalSquareMass,
    add_sub_cancel_left, inv_div]

theorem coprimeCertificateFamily_observation (n P : ℕ)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) (k : CoprimeCertificateIndex P)
    (i : Fin n) :
    inner ℝ (tailAtom i.val) (coprimeCertificateFamily P k) = reciprocalSource n i := by
  apply differenceCertificate_observation n k.val
  · have hk := k.property.1
    omega
  · intro j hdiv
    have hdone : j.val + 2 ∣ 1 := by
      simpa only [show Nat.gcd (k.val + 2) P = 1 from k.property.2.2] using
        Nat.dvd_gcd hdiv (hmod j)
    have he := Nat.dvd_one.mp hdone
    omega

/-- The infinite average satisfies the actual finite dictionary observations. -/
theorem infiniteCoprimeCertificate_observation (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) (i : Fin n) :
    inner ℝ (tailAtom i.val) (infiniteCoprimeCertificate P) = reciprocalSource n i := by
  have hs := reciprocalEnergy_summable (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
  have hM := ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2)
  rw [infiniteCoprimeCertificate, affineMinimum, inner_smul_right]
  change _ * (innerSL ℝ (tailAtom i.val))
    (∑' k, (‖coprimeCertificateFamily P k‖ ^ 2)⁻¹ • coprimeCertificateFamily P k) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  change _ * (∑' k, inner ℝ (tailAtom i.val)
    ((‖coprimeCertificateFamily P k‖ ^ 2)⁻¹ • coprimeCertificateFamily P k)) = _
  simp only [inner_smul_right, coprimeCertificateFamily_observation n P hmod, tsum_mul_right]
  change (reciprocalEnergyMass (coprimeCertificateFamily P))⁻¹ *
    (reciprocalEnergyMass (coprimeCertificateFamily P) * reciprocalSource n i) = _
  rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- Exact infinite-family completion for every convergent signed affine series. -/
theorem infiniteCoprimeCertificate_affine_energy_completion (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (a : CoprimeCertificateIndex P → ℝ) (z : ThresholdHilbert)
    (hz : HasSum (fun i => a i • coprimeCertificateFamily P i) z)
    (ha : ∑' i, a i = 1) :
    ‖z‖ ^ 2 = 2 / (coprimeReciprocalSquareMass P - 1) +
      ‖z - infiniteCoprimeCertificate P‖ ^ 2 := by
  have h := affine_energy_completion (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
    (ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2)) hz ha
  have hm := infiniteCoprimeCertificate_norm_sq P hP h2
  have hn := affineMinimum_norm_sq (coprimeCertificateFamily_orthogonal P)
    (coprimeCertificateFamily_ne_zero P) (coprimeCertificate_reciprocalEnergy_summable P)
    (ne_of_gt (coprimeCertificate_reciprocalEnergyMass_pos P hP h2))
  change ‖infiniteCoprimeCertificate P‖ ^ 2 = _ at hn
  rw [← hn, hm] at h
  exact h

theorem infiniteCoprimeCertificate_affine_energy_eq_iff (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (a : CoprimeCertificateIndex P → ℝ) (z : ThresholdHilbert)
    (hz : HasSum (fun i => a i • coprimeCertificateFamily P i) z)
    (ha : ∑' i, a i = 1) :
    ‖z‖ ^ 2 = 2 / (coprimeReciprocalSquareMass P - 1) ↔
      z = infiniteCoprimeCertificate P := by
  rw [infiniteCoprimeCertificate_affine_energy_completion P hP h2 a z hz ha]
  constructor
  · intro h
    have hn : ‖z - infiniteCoprimeCertificate P‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro h
    rw [h, sub_self, norm_zero]
    ring

/-- The gap from this explicit Euler certificate to the unrestricted optimum
is exactly a squared Hilbert distance. -/
theorem infiniteCoprimeCertificate_capacity_gap (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) :
    2 / (coprimeReciprocalSquareMass P - 1) =
      tailCapacity n + ‖infiniteCoprimeCertificate P - tailMinimum n‖ ^ 2 := by
  rw [← infiniteCoprimeCertificate_norm_sq P hP h2]
  exact finiteTailCertificate_energy_completion n (infiniteCoprimeCertificate P)
    (infiniteCoprimeCertificate_observation n P hP h2 hmod)

/-- All Euler factors remain in this equality, together with the full excess. -/
theorem infiniteCoprimeCertificate_eulerProduct_capacity_gap (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P) :
    2 / ((Real.pi ^ 2 / 6) * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) - 1) =
      tailCapacity n + ‖infiniteCoprimeCertificate P - tailMinimum n‖ ^ 2 := by
  rw [← coprimeReciprocalSquareMass_eulerProduct P hP h2]
  exact infiniteCoprimeCertificate_capacity_gap n P hP h2 hmod

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

import RiemannResearch.RH.ParetoSieveMobiusBridge
import RiemannResearch.RH.ParetoParitySieveMass

/-!
Actual finite legal Möbius vectors have vanishing complete odd-pair
contrast energy. This is a proper component of their full Hilbert energy;
the orthogonal block-mean remainder is not estimated or discarded.
The full-norm estimate needed for RH remains Open.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization.TailCapacity

/-- The entire odd-pair contrast energy of an actual Hilbert vector. -/
def fullOddPairContrastEnergy (f : ThresholdHilbert) : ℝ :=
  ∑' p, coprimePairMass 2 p *
    (inner ℝ (differenceCertificate (p-2)) f)^2 / 2

theorem oddHeadConstant_eq_mass_quotient :
    oddHeadConstant = ((∑' p, coprimePairMass 2 p)+1)/(∑' p, coprimePairMass 2 p) := by
  have hS : (∑' p, coprimePairMass 2 p) ≠ 0 :=
    ne_of_gt (coprimePairMass_tsum_pos 2 (by decide) (by decide))
  rw [oddHeadConstant, infiniteCoprimeCertificate_norm_sq 2 (by decide) (by decide)]
  simp only [coprimeReciprocalSquareMass, add_sub_cancel_left]
  field_simp [hS]
  <;> ring

theorem sieve_contrast_mask_hasSum (P : ℕ) (a : ℝ) :
    HasSum (fun p => coprimePairMass 2 p *
      (oddHeadConstant-a*(if Nat.Coprime P p then 0 else 1))^2/2)
      (((oddHeadConstant-a)^2/2)*(∑' p, coprimePairMass 2 p) +
        ((oddHeadConstant^2-(oddHeadConstant-a)^2)/2)*
          (∑' p, coprimePairMass (2*P) p)) := by
  have he : (fun p => coprimePairMass 2 p *
      (oddHeadConstant-a*(if Nat.Coprime P p then 0 else 1))^2/2) =
      (fun p => ((oddHeadConstant-a)^2/2)*coprimePairMass 2 p +
        ((oddHeadConstant^2-(oddHeadConstant-a)^2)/2)*coprimePairMass (2*P) p) := by
    funext p
    rw [coprimePairMass_mul_two_mask]
    split_ifs <;> ring
  rw [he]
  exact ((coprimePairMass_summable 2).hasSum.mul_left _).add
    ((coprimePairMass_summable (2*P)).hasSum.mul_left _)

theorem sieveMobiusNormalizedTail_contrast_summand (P p : ℕ) (a : ℝ) (hP : P ≠ 0) :
    coprimePairMass 2 p *
      (inner ℝ (differenceCertificate (p-2)) (sieveMobiusNormalizedTail P a))^2/2 =
    coprimePairMass 2 p *
      (oddHeadConstant-a*(if Nat.Coprime P p then 0 else 1))^2/2 := by
  by_cases hp : coprimePairIndex 2 p
  · have hp3 := hp.1
    have hpo := hp.2.1
    have hi : p-2+2=p := by omega
    have ho : ¬ 2 ∣ p-2+2 := by omega
    rw [sieveMobiusNormalizedTail_odd_pairContrast P (p-2) a hP (by omega) ho, hi]
  · simp [coprimePairMass, hp]

/-- Summability of this actual vector's whole contrast series is proved. -/
theorem sieveMobiusNormalizedTail_contrast_hasSum (P : ℕ) (a : ℝ) (hP : P ≠ 0) :
    HasSum (fun p => coprimePairMass 2 p *
      (inner ℝ (differenceCertificate (p-2)) (sieveMobiusNormalizedTail P a))^2/2)
      (((oddHeadConstant-a)^2/2)*(∑' p, coprimePairMass 2 p) +
        ((oddHeadConstant^2-(oddHeadConstant-a)^2)/2)*
          (∑' p, coprimePairMass (2*P) p)) := by
  simpa only [sieveMobiusNormalizedTail_contrast_summand P _ a hP] using
    sieve_contrast_mask_hasSum P a

theorem sieveMobiusNormalizedTail_contrast_exact (P : ℕ) (a : ℝ) (hP : P ≠ 0) :
    fullOddPairContrastEnergy (sieveMobiusNormalizedTail P a) =
      (((oddHeadConstant-a)^2/2)*(∑' p, coprimePairMass 2 p) +
        ((oddHeadConstant^2-(oddHeadConstant-a)^2)/2)*
          (∑' p, coprimePairMass (2*P) p)) :=
  (sieveMobiusNormalizedTail_contrast_hasSum P a hP).tsum_eq

theorem sieveMobiusNormalizedTail_unitMoment_contrast_exact (P : ℕ)
    (hP : P ≠ 0) (h3 : 3 ∣ P) :
    fullOddPairContrastEnergy
      (sieveMobiusNormalizedTail P (1/sieveMobiusOddMoment P 1)) =
    ((∑' p, coprimePairMass 2 p)+1)^2 * (∑' p, coprimePairMass (2*P) p) /
      (2*(∑' p, coprimePairMass 2 p)*
        ((∑' p, coprimePairMass 2 p)-(∑' p, coprimePairMass (2*P) p))) := by
  let S : ℝ := ∑' p, coprimePairMass 2 p
  let R : ℝ := ∑' p, coprimePairMass (2*P) p
  let M : ℝ := sieveMobiusOddMoment P 1
  have hS : 0 < S := coprimePairMass_tsum_pos 2 (by decide) (by decide)
  have hM : 0 < M := sieveMobiusOddMoment_pos P hP h3
  have hMS : (S+1)*M=S-R := by
    simpa only [coprimeReciprocalSquareMass, add_comm] using
      sieveMobiusOddMoment_mass_identity P hP
  have hSR : S-R ≠ 0 := by nlinarith
  have ha : 1/M=(S+1)/(S-R) := by
    apply (div_eq_div_iff (ne_of_gt hM) hSR).mpr
    nlinarith
  rw [sieveMobiusNormalizedTail_contrast_exact P _ hP, oddHeadConstant_eq_mass_quotient]
  change ((S+1)/S-1/M)^2/2*S +
    (((S+1)/S)^2-((S+1)/S-1/M)^2)/2*R = (S+1)^2*R/(2*S*(S-R))
  rw [ha]
  convert sieveContrast_variance_exact S R (ne_of_gt hS) hSR using 1 <;> ring

theorem coprimePairMass_twice_even (P p : ℕ) (h2 : 2 ∣ P) :
    coprimePairMass (2*P) p = coprimePairMass P p := by
  have hc : Nat.Coprime p 2 ∧ Nat.Coprime p P ↔ Nat.Coprime p P := by
    constructor
    · exact And.right
    · intro h
      exact ⟨h.of_dvd_right h2, h⟩
  simp only [coprimePairMass, coprimePairIndex, Nat.coprime_mul_iff_right, hc]

/-- Genuine finite legal sieve vectors, normalized to odd moment one,
solve the entire odd-pair contrast component unconditionally. The rest
of their full Hilbert norm remains outside this conclusion. -/
theorem factorial_sieve_fullOddPairContrast_tendsto_zero :
    Tendsto (fun n : ℕ => fullOddPairContrastEnergy
      (sieveMobiusNormalizedTail (n+2).factorial
        (1/sieveMobiusOddMoment (n+2).factorial 1))) atTop (𝓝 0) := by
  apply factorial_sieveContrast_variance_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h2 : 2 ∣ (n+2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h3 : 3 ∣ (n+2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have he := sieveMobiusNormalizedTail_unitMoment_contrast_exact
    (n+2).factorial (Nat.factorial_ne_zero _) h3
  simpa only [coprimePairMass_twice_even _ _ h2] using he.symm

end RiemannResearch.RH.Pareto

import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.ParetoParityContrast

/-!
Finite genuine Möbius coefficients with an exact coprimality mask.
All positive non-unit divisors are used; even coefficients may subsequently
be corrected. No infinite full-norm approximation is asserted.
Source: independently derived from the user's Pareto head-normalization
handoff, 21 September 2026; no novelty claim is made.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open CoefficientStabilization.TailCapacity

theorem sieve_divisor_filter_eq_gcd (P p : ℕ) (hP : P ≠ 0) :
    P.divisors.filter (fun d => d ∣ p) = (Nat.gcd P p).divisors := by
  have hg : Nat.gcd P p ≠ 0 := by
    intro hz
    have hd := Nat.gcd_dvd_left P p
    rw [hz, zero_dvd_iff] at hd
    exact hP hd
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hdP, _⟩, hdp⟩
    exact ⟨⟨hdP, hdp⟩, hg⟩
  · rintro ⟨⟨hdP, hdp⟩, _⟩
    exact ⟨⟨hdP, hP⟩, hdp⟩

theorem sieve_moebius_full_divisor_mask (P p : ℕ) (hP : P ≠ 0) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) =
      if Nat.Coprime P p then 1 else 0 := by
  simp only [divisorIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, sieve_divisor_filter_eq_gcd P p hP,
    moebius_real_divisor_sum]

theorem sieve_moebius_nonunit_mask (P p : ℕ) (hP : P ≠ 0) :
    (∑ d ∈ P.divisors.erase 1,
      -(ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) =
      if Nat.Coprime P p then 0 else 1 := by
  have h1 : 1 ∈ P.divisors := Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩
  have he := Finset.sum_erase_add P.divisors
    (fun d => (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) h1
  rw [sieve_moebius_full_divisor_mask P p hP] at he
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one,
    divisorIndicator, one_dvd, if_true, mul_one] at he
  rw [show (∑ d ∈ P.divisors.erase 1,
      -(ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) =
      -(∑ d ∈ P.divisors.erase 1,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) by
      simp only [neg_mul, Finset.sum_neg_distrib]]
  simp only [divisorIndicator]
  split_ifs at he ⊢ <;> linarith

def sieveMobiusTail (P : ℕ) (a : ℝ) : ThresholdHilbert :=
  ∑ d ∈ P.divisors.erase 1,
    (-a * (ArithmeticFunction.moebius d : ℝ)) • tailAtom (d-2)

def sieveMobiusHead (P : ℕ) (a : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, (-a * (ArithmeticFunction.moebius d : ℝ)) / (d : ℝ)

theorem sieveMobiusTail_mem_tailSpan (P : ℕ) (a : ℝ) :
    sieveMobiusTail P a ∈ Submodule.span ℝ (Set.range tailAtom) := by
  unfold sieveMobiusTail
  apply Submodule.sum_mem
  intro d hd
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d-2, rfl⟩)

theorem sieve_nonunit_divisor_ge_two (P d : ℕ) (hd : d ∈ P.divisors.erase 1) :
    2 ≤ d := by
  have hdpos := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
  have hdne := (Finset.mem_erase.mp hd).1
  omega

/-- The actual Hilbert vector has the exact finite sieve contrast at every tail pair. -/
theorem sieveMobiusTail_pairContrast (P k : ℕ) (a : ℝ) (hP : P ≠ 0) (hk : 0 < k) :
    inner ℝ (differenceCertificate k) (sieveMobiusTail P a) =
      sieveMobiusHead P a - a * (if Nat.Coprime P (k+2) then 0 else 1) := by
  have ht : (∑ d ∈ P.divisors.erase 1,
      (-a * (ArithmeticFunction.moebius d : ℝ)) *
        inner ℝ (differenceCertificate k) (tailAtom (d-2))) =
      sieveMobiusHead P a - a *
        (∑ d ∈ P.divisors.erase 1,
          -(ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k+2)) := by
    unfold sieveMobiusHead
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd2 := sieve_nonunit_divisor_ge_two P d hd
    rw [differenceCertificate_inner_tailAtom k (d-2) hk,
      Nat.sub_add_cancel hd2]
    ring
  rw [sieveMobiusTail, inner_sum]
  simp only [inner_sum, inner_smul_right]
  rw [ht, sieve_moebius_nonunit_mask P (k+2) hP]

def sieveMobiusNormalizedTail (P : ℕ) (a : ℝ) : ThresholdHilbert :=
  sieveMobiusTail P a + (2*(oddHeadConstant-sieveMobiusHead P a)) • tailAtom 0

theorem sieveMobiusNormalizedTail_mem_tailSpan (P : ℕ) (a : ℝ) :
    sieveMobiusNormalizedTail P a ∈ Submodule.span ℝ (Set.range tailAtom) := by
  apply Submodule.add_mem _ (sieveMobiusTail_mem_tailSpan P a)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- The independent modulus-two correction imposes the exact desired
head. At an odd site, its divisor indicator is zero. -/
theorem sieveMobiusNormalizedTail_odd_pairContrast (P k : ℕ) (a : ℝ)
    (hP : P ≠ 0) (hk : 0 < k) (hodd : ¬ 2 ∣ k+2) :
    inner ℝ (differenceCertificate k) (sieveMobiusNormalizedTail P a) =
      oddHeadConstant - a * (if Nat.Coprime P (k+2) then 0 else 1) := by
  rw [sieveMobiusNormalizedTail, inner_add_right, inner_smul_right,
    sieveMobiusTail_pairContrast P k a hP hk,
    differenceCertificate_inner_tailAtom k 0 hk]
  norm_num [divisorIndicator, hodd]
  ring

/-- The odd moment of the finite sieve coefficients, stated using coprimality
with two to match the existing exact divisible-mass theorem. -/
def sieveMobiusOddMoment (P : ℕ) (a : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.erase 1, (-a * (ArithmeticFunction.moebius d : ℝ)) *
    (if Nat.Coprime d 2 then 1/(d : ℝ)^2 else 0)

theorem sieveMobiusOddMoment_scale (P : ℕ) (a : ℝ) :
    sieveMobiusOddMoment P a = a * sieveMobiusOddMoment P 1 := by
  unfold sieveMobiusOddMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem sieveMobiusOddMoment_normalized (P : ℕ)
    (hM : sieveMobiusOddMoment P 1 ≠ 0) :
    sieveMobiusOddMoment P (1/sieveMobiusOddMoment P 1) = 1 := by
  rw [sieveMobiusOddMoment_scale]
  field_simp

theorem coprimePairMass_mul_two_mask (P p : ℕ) :
    coprimePairMass (2*P) p =
      if Nat.Coprime P p then coprimePairMass 2 p else 0 := by
  have hidx : coprimePairIndex (2*P) p ↔ coprimePairIndex 2 p ∧ Nat.Coprime P p := by
    constructor
    · rintro ⟨h3, ho, hcop⟩
      have ht := Nat.coprime_mul_iff_right.mp hcop
      exact ⟨⟨h3, ho, ht.1⟩, ht.2.symm⟩
    · rintro ⟨⟨h3, ho, hcop⟩, hcP⟩
      exact ⟨h3, ho, Nat.coprime_mul_iff_right.mpr ⟨hcop, hcP.symm⟩⟩
  change (if coprimePairIndex (2*P) p then 1/(p : ℝ)^2 else 0) =
    (if Nat.Coprime P p then (if coprimePairIndex 2 p then 1/(p : ℝ)^2 else 0) else 0)
  by_cases hb : coprimePairIndex 2 p
  · by_cases hc : Nat.Coprime P p
    · rw [if_pos (hidx.mpr ⟨hb, hc⟩), if_pos hc, if_pos hb]
    · have hn : ¬ coprimePairIndex (2*P) p := fun h => hc (hidx.mp h).2
      rw [if_neg hn, if_neg hc]
  · have hn : ¬ coprimePairIndex (2*P) p := fun h => hb (hidx.mp h).1
    rw [if_neg hn]
    by_cases hc : Nat.Coprime P p
    · rw [if_pos hc, if_neg hb]
    · rw [if_neg hc]

/-- Genuine finite Möbius coefficients recover the exact excluded odd-site
mass. Both infinite sums come from already proved summable arithmetic masses. -/
theorem sieveMobiusOddMoment_mass_identity (P : ℕ) (hP : P ≠ 0) :
    coprimeReciprocalSquareMass 2 * sieveMobiusOddMoment P 1 =
      (∑' p, coprimePairMass 2 p) - (∑' p, coprimePairMass (2*P) p) := by
  have hs := hasSum_sum (s := P.divisors.erase 1) (fun d hd =>
    (coprimePairMass_divisible_hasSum 2 d (by decide) (by decide)
      (sieve_nonunit_divisor_ge_two P d hd)).mul_left
        (-(ArithmeticFunction.moebius d : ℝ)))
  have hfun : (fun p => ∑ d ∈ P.divisors.erase 1,
      -(ArithmeticFunction.moebius d : ℝ) *
        (if d ∣ p then coprimePairMass 2 p else 0)) =
      (fun p => coprimePairMass 2 p - coprimePairMass (2*P) p) := by
    funext p
    have he : (∑ d ∈ P.divisors.erase 1,
        -(ArithmeticFunction.moebius d : ℝ) *
          (if d ∣ p then coprimePairMass 2 p else 0)) =
        coprimePairMass 2 p * (∑ d ∈ P.divisors.erase 1,
          -(ArithmeticFunction.moebius d : ℝ) * divisorIndicator d p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdp : d ∣ p <;> simp [divisorIndicator, hdp] <;> ring
    rw [he, sieve_moebius_nonunit_mask P p hP, coprimePairMass_mul_two_mask]
    split_ifs <;> ring
  have hval : (∑ d ∈ P.divisors.erase 1,
      -(ArithmeticFunction.moebius d : ℝ) *
        (if Nat.Coprime d 2 then coprimeReciprocalSquareMass 2 / (d : ℝ)^2 else 0)) =
      coprimeReciprocalSquareMass 2 * sieveMobiusOddMoment P 1 := by
    unfold sieveMobiusOddMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d 2 <;> simp [hc] <;> ring
  rw [hfun, hval] at hs
  exact hs.unique ((coprimePairMass_summable 2).hasSum.sub
    (coprimePairMass_summable (2*P)).hasSum)

theorem sieveMobiusOddMoment_pos (P : ℕ) (hP : P ≠ 0) (h3 : 3 ∣ P) :
    0 < sieveMobiusOddMoment P 1 := by
  have hnc : ¬ Nat.Coprime P 3 := by
    intro hc
    have hd : 3 ∣ 1 := by
      simpa only [show Nat.gcd P 3 = 1 from hc] using Nat.dvd_gcd h3 (dvd_refl 3)
    norm_num at hd
  have hnonneg (p : ℕ) : 0 ≤ coprimePairMass 2 p - coprimePairMass (2*P) p := by
    rw [coprimePairMass_mul_two_mask]
    split_ifs
    · simp
    · simpa only [sub_zero] using coprimePairMass_nonneg 2 p
  have hle := ((coprimePairMass_summable 2).sub
    (coprimePairMass_summable (2*P))).le_tsum 3 (fun p hp => hnonneg p)
  rw [(coprimePairMass_summable 2).tsum_sub (coprimePairMass_summable (2*P)),
    ← sieveMobiusOddMoment_mass_identity P hP,
    coprimePairMass_mul_two_mask P 3, if_neg hnc] at hle
  norm_num [coprimePairMass, coprimePairIndex] at hle
  have hZ := coprimeReciprocalSquareMass_pos 2
  nlinarith

theorem sieveMobiusNormalizedTail_finite_contrast_energy (P : ℕ) (a : ℝ)
    (hP : P ≠ 0) (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k)
    (ho : ∀ k ∈ s, ¬ 2 ∣ k+2) :
    parityContrastEnergy s (sieveMobiusNormalizedTail P a) =
      ∑ k ∈ s, (oddHeadConstant - a *
        (if Nat.Coprime P (k+2) then 0 else 1))^2 / (2*((k : ℝ)+2)^2) := by
  unfold parityContrastEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [sieveMobiusNormalizedTail_odd_pairContrast P k a hP (hs k hk) (ho k hk)]

end RiemannResearch.RH.Pareto

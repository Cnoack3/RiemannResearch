/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
# Canonical prime CRT carries and their complete-Q conditional means

Source: squarefree profinite lattice agenda, 16 October 2026, Target 5.
The canonical inverse coefficients and their bounds are constructed for
squarefree conductors, and their full modular certificate is proved. The
floor carry has a literal finite legal Q representative and an exact conditional
mean at the old modulus. Auxiliary certificate lemmas allow signed integer
coefficients and any positive divisors.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries
open RiemannResearch.RH.ArithmeticCumulative

variable {ι : Type*} [Fintype ι]

/-- A cleared integer CRT certificate gives the exact reciprocal charge. -/
theorem reciprocal_charge (d : ℕ) (hd : 0 < d) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d) (a : ι → ℤ) (k : ℤ)
    (hcert : (∑ i, ((d / p i : ℕ) : ℤ) * a i) = 1 + (d : ℤ) * k) :
    (∑ i, (a i : ℝ) / (p i : ℝ)) = 1 / (d : ℝ) + (k : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have ht (i : ι) : (d : ℝ) * ((a i : ℝ) / (p i : ℝ)) =
      ((d / p i : ℕ) : ℝ) * (a i : ℝ) := by
    have hpR : (p i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hp i))
    have hmul : ((d / p i : ℕ) : ℝ) * (p i : ℝ) = (d : ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel (hpd i))
    rw [← hmul]
    field_simp [hpR]
  have hs : (d : ℝ) * (∑ i, (a i : ℝ) / (p i : ℝ)) =
      1 + (d : ℝ) * (k : ℝ) := by
    rw [Finset.mul_sum]
    simp_rw [ht]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_one,
      Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hcert
  apply mul_left_cancel₀ hdR
  rw [hs]
  field_simp

/-- The exact source carry is the floor of the prime/divisor residue sum. -/
def carry (p : ι → ℕ) (a : ι → ℤ) (n : ℕ) : ℤ :=
  ⌊∑ i, (a i : ℝ) * residueFraction (p i) n⌋

theorem residue_eq_sum_sub_carry_of_reciprocal (d : ℕ) (hd : 0 < d)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (a : ι → ℤ) (k : ℤ)
    (hrec : (∑ i, (a i : ℝ) / (p i : ℝ)) = 1 / (d : ℝ) + (k : ℝ)) (n : ℕ) :
    residueFraction d n =
      (∑ i, (a i : ℝ) * residueFraction (p i) n) - (carry p a n : ℝ) := by
  let m : ℤ := ((n / d : ℕ) : ℤ) + (n : ℤ) * k -
    ∑ i, a i * ((n / p i : ℕ) : ℤ)
  have he : (∑ i, (a i : ℝ) * residueFraction (p i) n) - residueFraction d n = (m : ℝ) := by
    simp_rw [RiemannResearch.RH.Pareto.residueFraction_eq_div_sub_floor (p _) n (hp _)]
    rw [RiemannResearch.RH.Pareto.residueFraction_eq_div_sub_floor d n hd]
    have hsum : (∑ i, (a i : ℝ) *
        ((n : ℝ) / (p i : ℝ) - ((n / p i : ℕ) : ℝ))) =
        (n : ℝ) * (∑ i, (a i : ℝ) / (p i : ℝ)) -
          ∑ i, (a i : ℝ) * ((n / p i : ℕ) : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum, hrec]
    simp only [m, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
    ring
  have hr0 : 0 ≤ residueFraction d n := by unfold residueFraction; positivity
  have hr1 : residueFraction d n < 1 := by
    unfold residueFraction
    apply (div_lt_one (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    exact_mod_cast Nat.mod_lt n hd
  have hf := (Int.fract_eq_iff).mpr ⟨hr0, hr1, m, he⟩
  simpa only [Int.fract, carry] using hf.symm

/-- Every certified finite CRT reciprocal decomposition has the stated floor carry. -/
theorem residue_eq_sum_sub_carry (d : ℕ) (hd : 0 < d)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d)
    (a : ι → ℤ) (k : ℤ)
    (hcert : (∑ i, ((d / p i : ℕ) : ℤ) * a i) = 1 + (d : ℤ) * k) (n : ℕ) :
    residueFraction d n =
      (∑ i, (a i : ℝ) * residueFraction (p i) n) - (carry p a n : ℝ) :=
  residue_eq_sum_sub_carry_of_reciprocal d hd p hp a k
    (reciprocal_charge d hd p hp hpd a k hcert) n

/-- A literal finite modular certificate suffices, so concrete CRT tables can
be checked directly without an assumed integer offset. -/
theorem residue_eq_sum_sub_carry_of_modular (d : ℕ) (hd : 0 < d)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d)
    (a : ι → ℤ)
    (hcert : ((∑ i, ((d / p i : ℕ) : ℤ) * a i : ℤ) : ZMod d) = 1) (n : ℕ) :
    residueFraction d n =
      (∑ i, (a i : ℝ) * residueFraction (p i) n) - (carry p a n : ℝ) := by
  have hmod : (((∑ i, ((d / p i : ℕ) : ℤ) * a i) - 1 : ℤ) : ZMod d) = 0 := by
    simpa only [Int.cast_sub, Int.cast_one] using sub_eq_zero.mpr hcert
  obtain ⟨k, hk⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hmod
  apply residue_eq_sum_sub_carry d hd p hp hpd a k ?_ n
  linarith

end RiemannResearch.RH.QPrimeCRTCarries

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries

/-- The agenda's actual canonical inverse coefficient, in `[1,p)` for p|d. -/
def canonicalCoefficient (d p : ℕ) : ℕ := (((d / p : ℕ) : ZMod p)⁻¹).val

theorem canonicalCoefficient_inverse (d p : ℕ) (hsf : Squarefree d)
    (hp : p.Prime) (hpd : p ∣ d) :
    ((d / p : ℕ) : ZMod p) * (canonicalCoefficient d p : ZMod p) = 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hc : (d / p).Coprime p := by
    simpa only [Nat.gcd_eq_right hpd] using
      Nat.coprime_div_gcd_of_squarefree hsf hp.ne_zero
  have hu := (ZMod.isUnit_iff_coprime (d / p) p).mpr hc
  simpa only [canonicalCoefficient, ZMod.natCast_zmod_val] using
    ZMod.mul_inv_of_unit ((d / p : ℕ) : ZMod p) hu

theorem canonicalCoefficient_bounds (d p : ℕ) (hsf : Squarefree d)
    (hp : p.Prime) (hpd : p ∣ d) :
    1 ≤ canonicalCoefficient d p ∧ canonicalCoefficient d p < p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, ZMod.val_lt _⟩
  intro hz
  have hi := canonicalCoefficient_inverse d p hsf hp hpd
  simp [hz] at hi

/-- The canonical inverse table supplies the complete cleared CRT certificate. -/
theorem canonical_modular_certificate (d : ℕ) (hsf : Squarefree d) :
    ((∑ p ∈ d.primeFactors,
      ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ) : ℤ) : ZMod d) = 1 := by
  classical
  let S : ℤ := ∑ p ∈ d.primeFactors,
    ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ)
  have hprime (p : ℕ) (hp : p ∈ d.primeFactors) : (p : ℤ) ∣ S - 1 := by
    have hpP := (Nat.mem_primeFactors.mp hp).1
    have hpD := (Nat.mem_primeFactors.mp hp).2.1
    have hs : (S : ZMod p) = 1 := by
      simp only [S, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      rw [Finset.sum_eq_single p]
      · exact canonicalCoefficient_inverse d p hsf hpP hpD
      · intro q hq hqp
        have hqP := (Nat.mem_primeFactors.mp hq).1
        have hqD := (Nat.mem_primeFactors.mp hq).2.1
        have hc : p.Coprime q := (Nat.coprime_primes hpP hqP).mpr hqp.symm
        have hpq : p ∣ d / q := by
          apply hc.dvd_mul_left.mp
          have he : q * (d / q) = d := by
            simpa only [Nat.mul_comm] using Nat.div_mul_cancel hqD
          rw [he]
          exact hpD
        have hz : ((d / q : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff (d / q) p).mpr hpq
        simp only [hz, zero_mul]
      · intro hn
        exact (hn hp).elim
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (S - 1) p).mp
    simp only [Int.cast_sub, Int.cast_one, hs, sub_self]
  have hcop : (d.primeFactors : Set ℕ).Pairwise
      (fun p q => IsCoprime (p : ℤ) (q : ℤ)) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
      (Nat.mem_primeFactors.mp hq).1).mpr hpq).isCoprime
  have hdiv : (∏ p ∈ d.primeFactors, (p : ℤ)) ∣ S - 1 :=
    Finset.prod_dvd_of_coprime hcop hprime
  have hprod : (∏ p ∈ d.primeFactors, (p : ℤ)) = (d : ℤ) := by
    have hn := congrArg (fun x : ℕ => (x : ℤ)) (Nat.prod_primeFactors_of_squarefree hsf)
    simpa only [Nat.cast_prod] using hn
  rw [hprod] at hdiv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (S - 1) d).mpr hdiv
  simp only [Int.cast_sub, Int.cast_one] at hz
  exact sub_eq_zero.mp hz

/-- The exact source-specific prime carry, with coefficients constructed and
the modular certificate proved from squarefreeness. -/
theorem canonical_prime_carry (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (n : ℕ) :
    RiemannResearch.RH.ArithmeticCumulative.residueFraction d n =
      (∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ) *
        RiemannResearch.RH.ArithmeticCumulative.residueFraction p n) -
      (⌊∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ) *
        RiemannResearch.RH.ArithmeticCumulative.residueFraction p n⌋ : ℝ) := by
  have hsumZ : (∑ p : d.primeFactors, ((d / p.val : ℕ) : ℤ) *
      (canonicalCoefficient d p.val : ℤ)) =
      ∑ p ∈ d.primeFactors, ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ))
  have hsumR : (∑ p : d.primeFactors, (canonicalCoefficient d p.val : ℝ) *
      RiemannResearch.RH.ArithmeticCumulative.residueFraction p.val n) =
      ∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ) *
        RiemannResearch.RH.ArithmeticCumulative.residueFraction p n :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => (canonicalCoefficient d p : ℝ) *
        RiemannResearch.RH.ArithmeticCumulative.residueFraction p n)
  have hc : ((∑ p : d.primeFactors, ((d / p.val : ℕ) : ℤ) *
      (canonicalCoefficient d p.val : ℤ) : ℤ) : ZMod d) = 1 := by
    rw [hsumZ]
    exact canonical_modular_certificate d hsf
  have h := residue_eq_sum_sub_carry_of_modular d hd
    (fun p : d.primeFactors => p.val)
    (fun p => (Nat.mem_primeFactors.mp p.property).1.pos)
    (fun p => (Nat.mem_primeFactors.mp p.property).2.1)
    (fun p => (canonicalCoefficient d p.val : ℤ)) hc n
  simpa only [carry, Int.cast_natCast, hsumR] using h

end RiemannResearch.RH.QPrimeCRTCarries

/-! Exact complete-Q conditioning of the CRT certificate's literal floor carry. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries
open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability

variable {ι : Type*} [Fintype ι]

theorem carry_bound (d : ℕ) (hd : 0 < d) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d) (a : ι → ℤ)
    (hcert : ((∑ i, ((d / p i : ℕ) : ℤ) * a i : ℤ) : ZMod d) = 1)
    (n : ℕ) : |(carry p a n : ℝ)| ≤ (∑ i, |(a i : ℝ)|) + 1 := by
  have he := residue_eq_sum_sub_carry_of_modular d hd p hp hpd a hcert n
  have hs : |∑ i, (a i : ℝ) * residueFraction (p i) n| ≤
      ∑ i, |(a i : ℝ)| := by
    calc
      _ ≤ ∑ i, |(a i : ℝ) * residueFraction (p i) n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (Pareto.residueFraction_abs_le_one (p i) n (hp i)) (abs_nonneg (a i : ℝ))
  calc
    _ = |(∑ i, (a i : ℝ) * residueFraction (p i) n) - residueFraction d n| := by
      congr 1
      linarith
    _ ≤ |∑ i, (a i : ℝ) * residueFraction (p i) n| + |residueFraction d n| :=
      abs_sub _ _
    _ ≤ _ := add_le_add hs (Pareto.residueFraction_abs_le_one d n hd)

theorem carry_periodic (p : ι → ℕ) (a : ι → ℤ) (K : ℕ)
    (hpK : ∀ i, p i ∣ K) (n : ℕ) : carry p a (n + K) = carry p a n := by
  unfold carry
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd (hpK i)]

/-- The old L-fiber uses its actual Q weights on the new L*r residues. -/
theorem conditionalValue_carry_finite (d : ℕ) (hd : 0 < d) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d) (a : ι → ℤ)
    (hcert : ((∑ i, ((d / p i : ℕ) : ℤ) * a i : ℤ) : ZMod d) = 1)
    (L r b : ℕ) (hL : 0 < L) (hr : 0 < r) (hb : 0 < b) (hdLr : d ∣ L * r) :
    QResidueConditional.conditionalValue L b (fun n => (carry p a n : ℝ)) =
      ∑ k : Fin r, QResidueConditional.alpha L r b k *
        (carry p a (b + L * k.val) : ℝ) := by
  apply QResidueConditional.conditionalValue_eq_alpha L r b hL hr hb _
    (carry_bound d hd p hp hpd a hcert)
  intro n
  rw [carry_periodic p a (L * r) (fun i => (hpd i).trans hdLr)]

/-- The floor carry has a literal finite legal representative in complete Q. -/
def carryVector (d : ℕ) (p : ι → ℕ) (a : ι → ℤ) : QHilbert :=
  (∑ i, (a i : ℝ) • qResidue (p i)) - qResidue d

theorem carryVector_sequence (d : ℕ) (hd : 0 < d) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d) (a : ι → ℤ)
    (hcert : ((∑ i, ((d / p i : ℕ) : ℤ) * a i : ℤ) : ZMod d) = 1) (n : ℕ) :
    qSequence (carryVector d p a) n = (carry p a n : ℝ) := by
  change qSequenceLinear ((∑ i, (a i : ℝ) • qResidue (p i)) - qResidue d) n = _
  simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  change (∑ i, (a i : ℝ) * qSequence (qResidue (p i)) n) -
    qSequence (qResidue d) n = _
  simp only [qSequence_qResidue]
  have he := residue_eq_sum_sub_carry_of_modular d hd p hp hpd a hcert n
  linarith

theorem carryVector_mem_divisorStage (d : ℕ) (p : ι → ℕ)
    (hpd : ∀ i, p i ∣ d) (a : ι → ℤ) :
    carryVector d p a ∈ QSquarefreeLatticePackets.divisorStage d := by
  apply (QSquarefreeLatticePackets.divisorStage d).sub_mem
  · apply (QSquarefreeLatticePackets.divisorStage d).sum_mem
    intro i _
    exact (QSquarefreeLatticePackets.divisorStage d).smul_mem _
      (Submodule.subset_span ⟨p i, hpd i, rfl⟩)
  · exact Submodule.subset_span ⟨d, dvd_refl d, rfl⟩

theorem carryVector_mem_squarefreeSpan (d : ℕ) (hd : 0 < d) (hsf : Squarefree d)
    (p : ι → ℕ) (hpd : ∀ i, p i ∣ d) (a : ι → ℤ) :
    carryVector d p a ∈ qSquarefreeCRTSpan :=
  QSquarefreeLatticePackets.divisorStage_le_squarefreeSpan d hd hsf
    (carryVector_mem_divisorStage d p hpd a)

end RiemannResearch.RH.QPrimeCRTCarries

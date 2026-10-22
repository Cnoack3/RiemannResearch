/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.Analysis.FiniteWeightedTailCharge
import RiemannResearch.NumberTheory.DivisorIncidence
import RiemannResearch.Analysis.FiniteIncidenceTailCharge
import RiemannResearch.Analysis.FiniteSignedVariance
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# All gcd-class charges of the actual rational-weight minimum

Source: user-provided CRT carry memorandum and
CRTCarryVerificationResearch20261019.md, all-gcd-class finite argument.
The normal equations are those of the existing attained divisor minimum.
The actual divisor-Möbius inverse and exact gcd-class cardinalities are used.
Signed fluctuations, including the zero-residue endpoint, are retained.
No asymptotic one-sided signed-tail estimate is proved here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open ArithmeticCumulative
open RiemannResearch.Analysis.FiniteWeightedTailCharge
open RiemannResearch.Analysis.FiniteIncidenceTailCharge
open RiemannResearch.NumberTheory.DivisorIncidence

/-- The actual signed weighted residual tail, including k=L. -/
def residualTail (L : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  tail (sites L) (weight L) (fun a => 1 - f a) k

def commonAverage (L : ℕ) : ℝ := 5 / (3 * (L : ℝ)^2)

def multipleSites (L d : ℕ) : Finset ℕ :=
  (sites L).filter (fun k => d ∣ k)

theorem multiple_prefix (L a d : ℕ) (ha : a ≤ L) (hd : 0 < d) :
    countPrefix (multipleSites L d) a = ((a/d : ℕ) : ℝ) := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 L := by
    intro k hk
    obtain ⟨hk1, hka⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk1, hka.trans ha⟩
  calc
    countPrefix (multipleSites L d) a =
        ∑ k ∈ Finset.Icc 1 L,
          if d ∣ k then (if k ≤ a then (1 : ℝ) else 0) else 0 := by
      simp only [countPrefix, multipleSites, sites, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 a, if d ∣ k then (1 : ℝ) else 0 := by
      have hs := Finset.sum_subset hsub
        (f := fun k => if d ∣ k then (if k ≤ a then (1 : ℝ) else 0) else 0)
        (by
          intro k hk hka
          have hk1 := (Finset.mem_Icc.mp hk).1
          have hnot : ¬ k ≤ a := by
            intro h
            exact hka (Finset.mem_Icc.mpr ⟨hk1, h⟩)
          simp [hnot])
      rw [← hs]
      apply Finset.sum_congr rfl
      intro k hk
      simp [(Finset.mem_Icc.mp hk).2]
    _ = cumulative (divisorIndicator d) a := by
      rw [sum_Icc_one]
      rfl
    _ = _ := cumulative_divisorIndicator d a hd

/-- Each actual divisor normal equation fixes its full incidence charge. -/
theorem multiple_tail_charge (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (d : ℕ) (hd : d ∈ L.divisors) :
    (∑ k ∈ sites L, if d ∣ k then residualTail L f k else 0) =
      5 / (3 * (L : ℝ) * (d : ℝ)) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hn : (∑ a ∈ sites L, weight L a * (1 - f a) *
      (countPrefix (multipleSites L d) a - (1 / (d : ℝ)) * (a : ℝ))) = 0 := by
    calc
      _ = -(∑ a ∈ sites L,
          weight L a * (1 - f a) * residueFraction d a) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [multiple_prefix L a d (Finset.mem_Icc.mp ha).2 hdpos,
          Pareto.residueFraction_eq_div_sub_floor d a hdpos]
        ring
      _ = 0 := by rw [hdiv d hd, neg_zero]
  have h := total_charge (sites L) (multipleSites L d) (weight L)
    (fun a => 1 - f a) (1/(d : ℝ)) hn
  rw [residual_moment L hL f hfL
    (hdiv L (Nat.mem_divisors.mpr ⟨dvd_refl L, ne_of_gt hL⟩))] at h
  simpa only [multipleSites, Finset.sum_filter, residualTail, div_eq_mul_inv,
    mul_inv_rev, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- The concrete Möbius reciprocal sum on the multiples of e. -/
theorem divisor_moebius_reciprocal (L e : ℕ) (he : e ∈ L.divisors) :
    (∑ d ∈ L.divisors,
      if e ∣ d then (ArithmeticFunction.moebius (d/e) : ℝ) / (d : ℝ) else 0) =
      (Nat.totient (L/e) : ℝ) / (L : ℝ) := by
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  have heL : e ∣ L := Nat.dvd_of_mem_divisors he
  have hL : L ≠ 0 := (Nat.mem_divisors.mp he).2
  have hn : L/e ≠ 0 := ne_of_gt (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) heL) hepos)
  have hprod : (e : ℝ) * ((L/e : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' heL
  calc
    _ = ∑ d ∈ L.divisors.filter (fun d => e ∣ d ∧ d ∣ L),
        (ArithmeticFunction.moebius (d/e) : ℝ) / ((e : ℝ) * ((d/e : ℕ) : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      have hdL := Nat.dvd_of_mem_divisors hd
      by_cases hed : e ∣ d
      · have hm : (e : ℝ) * ((d/e : ℕ) : ℝ) = (d : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' hed
        rw [if_pos hed, if_pos ⟨hed, hdL⟩, hm]
      · simp [hed]
    _ = ∑ j ∈ (L/e).divisors,
        (ArithmeticFunction.moebius j : ℝ) / ((e : ℝ) * (j : ℝ)) :=
      sum_divisor_interval L e L hL (dvd_refl L) hL heL
        (fun j => (ArithmeticFunction.moebius j : ℝ) / ((e : ℝ) * (j : ℝ)))
    _ = (1/(e : ℝ)) * QPrimeSieve.divisorDensity (L/e) := by
      unfold QPrimeSieve.divisorDensity
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [QMobiusPrimePacket.divisorDensity_eq_totient (L/e) hn]
      rw [← hprod]
      ring

/-- Every gcd class, including e=L, has the same mean signed tail. -/
theorem gcd_class_charge (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ gcdClass L e, residualTail L f k) =
      5 * (Nat.totient (L/e) : ℝ) / (3 * (L : ℝ)^2) := by
  have h := gcd_class_charge_moebius L (ne_of_gt hL) (sites L)
    (residualTail L f) (fun d => 5 / (3 * (L : ℝ) * (d : ℝ)))
    (multiple_tail_charge L hL f hfL hdiv) e he
  change (∑ k ∈ gcdClass L e, residualTail L f k) = _ at h
  rw [h]
  calc
    _ = (5 / (3 * (L : ℝ))) *
        ∑ d ∈ L.divisors,
          if e ∣ d then (ArithmeticFunction.moebius (d/e) : ℝ) / (d : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
    _ = _ := by
      rw [divisor_moebius_reciprocal L e he]
      ring

theorem gcd_class_mean (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ gcdClass L e, residualTail L f k) =
      ((gcdClass L e).card : ℝ) * commonAverage L := by
  rw [gcd_class_charge L hL f hfL hdiv e he, gcd_class_card L e he]
  unfold commonAverage
  ring

theorem gcd_class_centered_zero (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ gcdClass L e, (residualTail L f k - commonAverage L)) = 0 :=
  centered_charge_zero _ _ _ (gcd_class_mean L hL f hfL hdiv e he)

/-- Exact finite square decomposition; no individual sign is assumed. -/
theorem gcd_class_square_decomposition (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ gcdClass L e, (residualTail L f k)^2) =
      (Nat.totient (L/e) : ℝ) * (commonAverage L)^2 +
        ∑ k ∈ gcdClass L e, (residualTail L f k - commonAverage L)^2 := by
  have h := sum_sq_eq_mean_sq_add_centered_sq _ _ _
    (gcd_class_mean L hL f hfL hdiv e he)
  simpa only [gcd_class_card L e he] using h

theorem residualTail_endpoint (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0) :
    residualTail L f L = commonAverage L := by
  have hs : (∑ a ∈ sites L,
      if L ≤ a then weight L a * (1 - f a) else 0) =
      weight L L * (1 - f L) := by
    simpa only [le_refl, ite_true] using
      (Finset.sum_eq_single L (s := sites L)
        (f := fun a => if L ≤ a then weight L a * (1 - f a) else 0)
        (by
          intro a ha hne
          have haL := (Finset.mem_Icc.mp ha).2
          have hn : ¬ L ≤ a := by omega
          simp [hn])
        (by
          intro hnot
          exact (hnot (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)).elim))
  change (∑ a ∈ sites L,
    if L ≤ a then weight L a * (1 - f a) else 0) = _
  rw [hs, hfL, sub_zero, mul_one, weight_endpoint L hL]
  rfl

/-- Attained global minimum with all gcd-class charges and centered squares.
There are no unproved normal equations in this existence theorem. -/
theorem exists_all_class_minimum (L : ℕ) (hL : 0 < L) :
    ∃ c : ℕ → ℝ,
      (∀ d ∈ L.divisors,
        (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
          residueFraction d a) = 0) ∧
      (∀ b : ℕ → ℝ, rationalError L (divisorFit L c) ≤
        rationalError L (divisorFit L b)) ∧
      (∀ e ∈ L.divisors,
        (gcdClass L e).card = Nat.totient (L/e) ∧
        (∑ k ∈ gcdClass L e, residualTail L (divisorFit L c) k) =
          5 * (Nat.totient (L/e) : ℝ) / (3 * (L : ℝ)^2) ∧
        (∑ k ∈ gcdClass L e,
          (residualTail L (divisorFit L c) k - commonAverage L)) = 0 ∧
        (∑ k ∈ gcdClass L e, (residualTail L (divisorFit L c) k)^2) =
          (Nat.totient (L/e) : ℝ) * (commonAverage L)^2 +
            ∑ k ∈ gcdClass L e,
              (residualTail L (divisorFit L c) k - commonAverage L)^2) ∧
      residualTail L (divisorFit L c) L = commonAverage L := by
  obtain ⟨c, hc, _hsigned, hmin⟩ := exists_signed_minimum L hL
  have hfL := divisor_synthesis_endpoint L (divisorFit L c) c (fun _ => rfl)
  refine ⟨c, hc, hmin, ?_, residualTail_endpoint L hL _ hfL⟩
  intro e he
  exact ⟨gcd_class_card L e he, gcd_class_charge L hL _ hfL hc e he,
    gcd_class_centered_zero L hL _ hfL hc e he,
    gcd_class_square_decomposition L hL _ hfL hc e he⟩


/-- The literal average is defined and equals the same constant on every class. -/
theorem gcd_class_average (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ gcdClass L e, residualTail L f k) / ((gcdClass L e).card : ℝ) =
      commonAverage L := by
  have hemem : e ∈ gcdClass L e := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he,
      Nat.le_of_dvd hL (Nat.dvd_of_mem_divisors he)⟩,
      Nat.gcd_eq_left (Nat.dvd_of_mem_divisors he)⟩
  have hn : ((gcdClass L e).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨e, hemem⟩))
  rw [gcd_class_mean L hL f hfL hdiv e he]
  field_simp

theorem period_mean (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    (∑ k ∈ sites L, residualTail L f k) =
      ((sites L).card : ℝ) * commonAverage L := by
  have h := multiple_tail_charge L hL f hfL hdiv 1
    (Nat.mem_divisors.mpr ⟨one_dvd L, ne_of_gt hL⟩)
  simp only [one_dvd, ite_true, Nat.cast_one, mul_one] at h
  rw [h]
  have hc : (sites L).card = L := by simp [sites, Nat.card_Icc]
  rw [hc]
  unfold commonAverage
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  field_simp

/-- The full-period square identity also retains every within-class fluctuation. -/
theorem period_square_decomposition (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ)
    (hfL : f L = 0)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - f a) * residueFraction d a) = 0) :
    (∑ k ∈ sites L, (residualTail L f k)^2) =
      (L : ℝ) * (commonAverage L)^2 +
        ∑ k ∈ sites L, (residualTail L f k - commonAverage L)^2 := by
  have h := sum_sq_eq_mean_sq_add_centered_sq _ _ _ (period_mean L hL f hfL hdiv)
  have hc : (sites L).card = L := by simp [sites, Nat.card_Icc]
  simpa only [hc] using h

theorem gcd_class_one (L : ℕ) : gcdClass L 1 = coprimeSites L := by
  simp only [gcdClass, coprimeSites, sites, Nat.coprime_iff_gcd_eq_one]

theorem residualTail_one_eq_error (L : ℕ) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) = 0) :
    residualTail L (divisorFit L c) 1 = rationalError L (divisorFit L c) := by
  rw [residualTail, tail_one (sites L) (weight L) _
    (fun a ha => (Finset.mem_Icc.mp ha).1)]
  exact (energy_eq_mass (sites L) (weight L) (divisorFit L c)
    (fitted_normal_of_divisor_synthesis L _ c (fun _ => rfl) hdiv)).symm

def coprimeNegativeMass (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  negativeCharge ((coprimeSites L).erase 1) (residualTail L f)

def coprimePositiveMass (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  positiveCharge ((coprimeSites L).erase 1) (residualTail L f)

def coprimeCenteredSquares (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ coprimeSites L, (residualTail L f k - commonAverage L)^2

/-- Exact negative-mass identity for the attained divisor normal solution. -/
theorem coprime_negative_mass_exact (L : ℕ) (hL : 0 < L) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) = 0) :
    coprimeNegativeMass L (divisorFit L c) =
      rationalError L (divisorFit L c) -
        (Nat.totient L : ℝ) * commonAverage L +
          coprimePositiveMass L (divisorFit L c) := by
  have hmean := gcd_class_mean L hL (divisorFit L c)
    (divisor_synthesis_endpoint L _ c (fun _ => rfl)) hdiv 1
    (Nat.mem_divisors.mpr ⟨one_dvd L, ne_of_gt hL⟩)
  rw [gcd_class_one] at hmean
  have hc : (coprimeSites L).card = Nat.totient L := coprime_Icc_card L
  rw [hc] at hmean
  exact negative_charge_after_erase _ _ 1
    (by simp [coprimeSites, sites, Nat.succ_le_iff.mpr hL])
    _ _ (residualTail_one_eq_error L c hdiv) hmean

/-- A newly formalized finite variance budget, not an asymptotic exhaustion
estimate. N is the actual negative mass away from the initial energy site. -/
theorem coprime_negative_mass_quadratic_budget
    (L : ℕ) (hL : 0 < L) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        residueFraction d a) = 0) :
    4 * coprimeNegativeMass L (divisorFit L c) *
        (coprimeNegativeMass L (divisorFit L c) +
          (Nat.totient L : ℝ) * commonAverage L) ≤
      (Nat.totient L : ℝ) * coprimeCenteredSquares L (divisorFit L c) := by
  have hmean := gcd_class_mean L hL (divisorFit L c)
    (divisor_synthesis_endpoint L _ c (fun _ => rfl)) hdiv 1
    (Nat.mem_divisors.mpr ⟨one_dvd L, ne_of_gt hL⟩)
  rw [gcd_class_one] at hmean
  have h := negative_charge_quadratic_budget _ _ _ hmean
  have hnonneg : 0 ≤ residualTail L (divisorFit L c) 1 := by
    rw [residualTail_one_eq_error L c hdiv]
    unfold rationalError energy
    exact Finset.sum_nonneg (fun a ha =>
      mul_nonneg (weight_nonneg L a) (sq_nonneg (1 - divisorFit L c a)))
  have hn := negative_charge_eq_erase_of_nonneg (coprimeSites L)
    (residualTail L (divisorFit L c)) 1
    (by simp [coprimeSites, sites, Nat.succ_le_iff.mpr hL]) hnonneg
  have hc : (coprimeSites L).card = Nat.totient L := coprime_Icc_card L
  rw [hn, hc] at h
  exact h

end RiemannResearch.RH.QRationalCoprimeTail

import RiemannResearch.RH.ParetoDilationLogMoments
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.ParetoResidueLogMean
import Mathlib.Data.Nat.PrimeFin

/-!
# Exact ordinary moments of integrated Ramanujan packets

Source: the user-provided Ramanujan--Laguerre continuation, Sections 3--7.
This proves RamanujanOrdinaryMomentsTarget using bounded-packet integrability,
the exact dilation law, and prime-factor induction. Repeated prime factors
preserve the first surviving moment; each new prime contributes a finite
difference and raises its order. No Mellin differentiation input is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

theorem ordinaryMoment_sub {F G : ℕ → ℝ}
    (hF : AllMomentsIntegrable F) (hG : AllMomentsIntegrable G) (j : ℕ) :
    ordinaryMoment (fun k => F k - G k) j = ordinaryMoment F j - ordinaryMoment G j := by
  have heq : (fun t => exponentialLift (fun k => F k - G k) t * t ^ j * Real.exp (-t)) =
      (fun t => exponentialLift F t * t ^ j * Real.exp (-t) -
        exponentialLift G t * t ^ j * Real.exp (-t)) := by
    funext t
    simp only [exponentialLift]
    ring
  unfold ordinaryMoment
  rw [heq, integral_sub (hF j) (hG j)]

theorem ordinaryMoment_dilation_eq_of_vanishing {F : ℕ → ℝ} (hF : F 0 = 0)
    (hI : AllMomentsIntegrable F) (q : ℕ) (hq : 0 < q) {r : ℕ}
    (hzero : ∀ j, j < r → ordinaryMoment F j = 0) (j : ℕ) (hj : j ≤ r) :
    ordinaryMoment (dilation q F) j = ordinaryMoment F j := by
  rw [ordinaryMoment_dilation hF hI q hq j]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hir : j - i < r := by
      have hi' := Finset.mem_range.mp hi
      omega
    rw [hzero _ hir]
    simp
  · simp

theorem ordinaryMoment_dilation_succ_of_vanishing {F : ℕ → ℝ} (hF : F 0 = 0)
    (hI : AllMomentsIntegrable F) (q : ℕ) (hq : 0 < q) (r : ℕ)
    (hzero : ∀ j, j < r → ordinaryMoment F j = 0) :
    ordinaryMoment (dilation q F) (r + 1) = ordinaryMoment F (r + 1) +
      ((r + 1 : ℕ) : ℝ) * Real.log q * ordinaryMoment F r := by
  rw [ordinaryMoment_dilation hF hI q hq (r + 1), Finset.sum_range_succ']
  have htail : (∑ i ∈ Finset.range (r + 1),
      ((r + 1).choose (i + 1) : ℝ) * Real.log q ^ (i + 1) *
        ordinaryMoment F (r + 1 - (i + 1))) =
      ((r + 1 : ℕ) : ℝ) * Real.log q * ordinaryMoment F r := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      have hir : r + 1 - (i + 1) < r := by
        have hi' := Finset.mem_range.mp hi
        omega
      rw [hzero _ hir]
      simp
    · simp
  rw [htail]
  simp; ring

theorem ramanujanPacket_allMomentsIntegrable (d : ℕ) :
    AllMomentsIntegrable (ramanujanPacket d) :=
  allMomentsIntegrable_of_bounded (fun k => ramanujanPacket_abs_le d k)

private theorem ramanujanPacket_at_zero (d : ℕ) : ramanujanPacket d 0 = 0 := by
  simp [ramanujanPacket, residue]

private def RamanujanMomentProfile (d : ℕ) : Prop :=
  (∀ j : ℕ, j < d.primeFactors.card - 1 → ordinaryMoment (ramanujanPacket d) j = 0) ∧
  ordinaryMoment (ramanujanPacket d) (d.primeFactors.card - 1) =
    ((d.primeFactors.card - 1).factorial : ℝ) * ∏ p ∈ d.primeFactors, Real.log (p : ℝ)

private theorem ramanujanMomentProfile_prime (p : ℕ) (hp : p.Prime) :
    RamanujanMomentProfile p := by
  constructor
  · intro j hj
    simp [hp.primeFactors] at hj
  · have hmean : ordinaryMoment (ramanujanPacket p) 0 = Real.log p := by
      rw [ramanujanPacket_prime_eq_residue p hp,
        ordinaryMoment_zero_of_bounded (fun k => residue_abs_le p k hp.pos),
        paretoMean_residue p hp.pos]
    simpa [hp.primeFactors] using hmean

private theorem ramanujanMomentProfile_repeat_prime (p q : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hpq : p ∣ q) (hQ : RamanujanMomentProfile q) :
    RamanujanMomentProfile (p * q) := by
  have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
  have hfac : (p * q).primeFactors = q.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors,
      Finset.singleton_union, Finset.insert_eq_of_mem hmem]
  have hpacket : ramanujanPacket (p * q) = dilation p (ramanujanPacket q) := by
    funext k
    exact ramanujanPacket_mul_prime_of_dvd p q k hp hq hpq
  have hI := ramanujanPacket_allMomentsIntegrable q
  have h0 := ramanujanPacket_at_zero q
  unfold RamanujanMomentProfile at hQ ⊢
  rw [hfac, hpacket]
  constructor
  · intro j hj
    rw [ordinaryMoment_dilation_eq_of_vanishing h0 hI p hp.pos hQ.1 j hj.le]
    exact hQ.1 j hj
  · rw [ordinaryMoment_dilation_eq_of_vanishing h0 hI p hp.pos hQ.1 _ le_rfl]
    exact hQ.2

private theorem ramanujanMomentProfile_new_prime (p q : ℕ)
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) (hQ : RamanujanMomentProfile q) :
    RamanujanMomentProfile (p * q) := by
  have hnot : p ∉ q.primeFactors := fun h => hpq (Nat.mem_primeFactors.mp h).2.1
  have hfac : (p * q).primeFactors = insert p q.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors, Finset.singleton_union]
  have hcpos : 0 < q.primeFactors.card := by
    obtain ⟨a, ha, haq⟩ := Nat.exists_prime_and_dvd (by omega : q ≠ 1)
    exact Finset.card_pos.mpr ⟨a, Nat.mem_primeFactors.mpr ⟨ha, haq, by omega⟩⟩
  let r := q.primeFactors.card - 1
  have hcard : (p * q).primeFactors.card - 1 = r + 1 := by
    rw [hfac, Finset.card_insert_of_notMem hnot]
    dsimp [r]
    omega
  have hpacket : ramanujanPacket (p * q) =
      fun k => dilation p (ramanujanPacket q) k - ramanujanPacket q k := by
    funext k
    exact ramanujanPacket_mul_prime_of_not_dvd p q k hp hq hpq
  have hI := ramanujanPacket_allMomentsIntegrable q
  have hDI : AllMomentsIntegrable (dilation p (ramanujanPacket q)) :=
    allMomentsIntegrable_of_bounded (dilation_abs_le (fun k => ramanujanPacket_abs_le q k) p)
  have h0 := ramanujanPacket_at_zero q
  have hzero : ∀ j, j < r → ordinaryMoment (ramanujanPacket q) j = 0 := hQ.1
  have hlead : ordinaryMoment (ramanujanPacket q) r =
      (r.factorial : ℝ) * ∏ a ∈ q.primeFactors, Real.log (a : ℝ) := hQ.2
  unfold RamanujanMomentProfile
  constructor
  · intro j hj
    have hjr : j ≤ r := by rw [hcard] at hj; omega
    rw [hpacket, ordinaryMoment_sub hDI hI,
      ordinaryMoment_dilation_eq_of_vanishing h0 hI p hp.pos hzero j hjr, sub_self]
  · rw [hcard, hpacket, ordinaryMoment_sub hDI hI,
      ordinaryMoment_dilation_succ_of_vanishing h0 hI p hp.pos r hzero, hlead]
    rw [hfac, Finset.prod_insert hnot, Nat.factorial_succ, Nat.cast_mul]
    ring

private theorem ramanujanMomentProfile_all (d : ℕ) :
    1 < d → RamanujanMomentProfile d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
    obtain ⟨q, rfl⟩ := hpd
    have hqpos : 0 < q := by
      by_contra h
      have hq0 : q = 0 := by omega
      simp [hq0] at hd
    by_cases hq1 : q = 1
    · subst q
      simpa using ramanujanMomentProfile_prime p hp
    · have hq : 1 < q := by omega
      have hqlt : q < p * q := by nlinarith [hp.one_lt]
      have hQ := ih q hqlt hq
      by_cases hpq : p ∣ q
      · exact ramanujanMomentProfile_repeat_prime p q hp hq hpq hQ
      · exact ramanujanMomentProfile_new_prime p q hp hq hpq hQ

theorem ramanujanOrdinaryMomentsTarget : RamanujanOrdinaryMomentsTarget := by
  intro d hd
  exact ⟨ramanujanPacket_allMomentsIntegrable d, ramanujanMomentProfile_all d hd⟩

/-- Actual integrated Laguerre coefficients have the exact arithmetic
triangular cancellation, with the signed leading prime-log product. -/
theorem ramanujanLaguerreCancellationTarget : RamanujanLaguerreCancellationTarget :=
  cancellationTarget_of_ordinaryMomentsTarget ramanujanOrdinaryMomentsTarget

end RiemannResearch.RH.Pareto.RamanujanLaguerre

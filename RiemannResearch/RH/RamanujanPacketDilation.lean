import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# Integer dilations of integrated Ramanujan packets

Section 2 of the user-provided Mixed Conductor CRT Research Handoff supplies the formula.
The proof uses the divisor incidence `t / gcd(t,m) ∣ q` iff `t ∣ m*q`
and the existing Möbius inversion. All divisors and repeated factors are retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

private theorem reducedConductor_dvd_iff {t m n : ℕ} (ht : 0 < t) :
    t / t.gcd m ∣ n ↔ t ∣ m * n := by
  have hg : 0 < t.gcd m := Nat.gcd_pos_of_pos_left _ ht
  have hc := Nat.coprime_div_gcd_div_gcd hg
  calc
    t / t.gcd m ∣ n ↔ t / t.gcd m ∣ (m / t.gcd m) * n := hc.dvd_mul_left.symm
    _ ↔ t.gcd m * (t / t.gcd m) ∣ t.gcd m * ((m / t.gcd m) * n) :=
      (Nat.mul_dvd_mul_iff_left hg).symm
    _ ↔ t ∣ m * n := by
      rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left t m),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right t m)]

/-- The output conductors are precisely the fibers of the reduced conductor. -/
theorem dilation_ramanujanPacket_fiber (m q k : ℕ) (hm : 0 < m) (hq : 1 < q) :
    dilation m (ramanujanPacket q) k =
      ∑ t ∈ (m * q).divisors.filter (fun t => t / t.gcd m = q), ramanujanPacket t k := by
  let f : ℕ → ℝ := fun a =>
    ∑ t ∈ (m * a).divisors.filter (fun t => t / t.gcd m = a), ramanujanPacket t k
  have hsum (a : ℕ) (ha : 0 < a) :
      ∑ b ∈ a.divisors, f b = residue (m * a) k := by
    have hmap (t : ℕ) (ht : t ∈ (m * a).divisors) :
        t / t.gcd m ∈ a.divisors :=
      Nat.mem_divisors.mpr ⟨(reducedConductor_dvd_iff (Nat.pos_of_mem_divisors ht)).mpr
        (Nat.dvd_of_mem_divisors ht), ha.ne'⟩
    rw [← ramanujanPacket_divisor_sum _ _ (Nat.mul_pos hm ha),
      ← Finset.sum_fiberwise_of_maps_to hmap (fun t => ramanujanPacket t k)]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [f]
    congr 1
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, he⟩
      exact ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors ht).trans
        (Nat.mul_dvd_mul_left m (Nat.dvd_of_mem_divisors hb)), (Nat.mul_pos hm ha).ne'⟩, he⟩
    · rintro ⟨ht, he⟩
      have hd := (reducedConductor_dvd_iff (m := m) (n := b)
        (Nat.pos_of_mem_divisors ht)).mp (by rw [he])
      exact ⟨Nat.mem_divisors.mpr ⟨hd,
        (Nat.mul_pos hm (Nat.pos_of_mem_divisors hb)).ne'⟩, he⟩
  have hf := (mobius_inversion f (fun a => residue (m * a) k)).mp hsum q (by omega)
  change dilation m (ramanujanPacket q) k = f q
  rw [← hf]
  have hr (d : ℕ) : residue (m * d) k = dilation m (residue d) k + residue m k := by
    rw [residue_mul_floor]
    ring
  simp_rw [hr, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_moebius_div q hq, zero_mul, add_zero]
  unfold dilation ramanujanPacket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Dilation keeps a factor (d) of (m) precisely when the remaining part of
(m) is coprime to the input conductor. -/
theorem dilation_ramanujanPacket_divisors (m q k : ℕ) (hm : 0 < m) (hq : 1 < q) :
    dilation m (ramanujanPacket q) k =
      ∑ d ∈ m.divisors.filter (fun d => q.Coprime (m / d)), ramanujanPacket (q * d) k := by
  rw [dilation_ramanujanPacket_fiber m q k hm hq]
  symm
  apply Finset.sum_bij (fun d _ => q * d)
  · intro d hd
    obtain ⟨hd, hc⟩ := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hg : (q * d).gcd m = d := by
      calc
        _ = (d * q).gcd (d * (m / d)) :=
          congrArg₂ Nat.gcd (Nat.mul_comm _ _)
            (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
        _ = d := by rw [Nat.gcd_mul_left, hc.gcd_eq_one, Nat.mul_one]
    have hred : (q * d) / (q * d).gcd m = q := by
      rw [hg]
      exact Nat.div_eq_of_eq_mul_left hdpos rfl
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨?_, (Nat.mul_pos hm (by omega)).ne'⟩, hred⟩
    simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_divisors hd)
  · intro d _ e _ he
    exact Nat.eq_of_mul_eq_mul_left (by omega) he
  · intro t ht
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp ht
    have hg : 0 < t.gcd m := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_mem_divisors ht)
    have hc := Nat.coprime_div_gcd_div_gcd hg
    rw [he] at hc
    refine ⟨t.gcd m, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨Nat.gcd_dvd_right _ _, hm.ne'⟩, hc⟩, ?_⟩
    rw [← he, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  · intro d _
    rfl

/-- The divisor formula in the complete Pareto Hilbert space. -/
theorem hilbertDilation_ramanujanPacket_divisors (m q : ℕ) (hm : 0 < m) (hq : 1 < q) :
    hilbertDilation m hm (ramanujanPacketHilbert q) =
      ∑ d ∈ m.divisors.filter (fun d => q.Coprime (m / d)), ramanujanPacketHilbert (q * d) := by
  apply hilbertSequence_injective
  funext k
  rw [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert,
    ← anchoredEvaluationCLM_apply]
  simp only [map_sum, anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert]
  exact dilation_ramanujanPacket_divisors m q k hm hq

end RiemannResearch.RH.Pareto

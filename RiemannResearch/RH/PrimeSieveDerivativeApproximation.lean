import RiemannResearch.RH.PrimeSievePointEnergy
import RiemannResearch.RH.ParetoPrimitiveEnergy
import RiemannResearch.RH.NearbyDilationGram

/-!
# Actual finite-sieve approximation of the derivative target

Source: the paper derivation in `CRTPrimitiveTransferAudit20260929.md`, §6.
The complete signed error polynomial is proved before the tail estimate.
The primitive is an actual finite legal residue sum. No RH hypothesis occurs.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative PrimitiveEnergy

/-- The negative finite Möbius residue sieve on factorial divisors. -/
def derivativeSievePrimitive (Y n : ℕ) : ℝ := -sieveResidue Y.factorial 1 n

theorem derivativeSievePrimitive_mem_legal (Y : ℕ) :
    derivativeSievePrimitive Y ∈ legalSeedSpan allPositiveSeeds := by
  exact (legalSeedSpan allPositiveSeeds).neg_mem
    (sieveResidue_mem_legal Y.factorial 1 (by decide))

@[simp] theorem derivativeSievePrimitive_zero (Y : ℕ) :
    derivativeSievePrimitive Y 0 = 0 := by
  simp [derivativeSievePrimitive, sieveResidue, residueFraction]

/-- Actual arithmetic derivative, with the zero coordinate handled separately below. -/
theorem derivativeSievePrimitive_difference_succ (Y n : ℕ) :
    difference (derivativeSievePrimitive Y) (n + 1) =
      (if Nat.gcd Y.factorial (n + 1) = 1 then 1 else 0) -
        sieveReciprocal Y.factorial := by
  have h₁ := sieveResidue_exact Y.factorial 1 (n + 1) (Nat.factorial_pos Y) (by decide)
  have h₀ := sieveResidue_exact Y.factorial 1 n (Nat.factorial_pos Y) (by decide)
  simp only [Nat.cast_one, Nat.div_one, div_one] at h₁ h₀
  simp only [difference, backwardShift, Nat.add_sub_cancel, derivativeSievePrimitive,
    h₁, h₀]
  simp only [sieveRoughCount, cumulative_succ]
  push_cast
  ring

/-- The full rough-number tail indicator after removing the target point at one. -/
def derivativeSieveTailIndicator (Y n : ℕ) : ℝ :=
  if 1 < n ∧ Nat.gcd Y.factorial n = 1 then 1 else 0

def derivativeSieveTailMass (Y : ℕ) : ℝ :=
  ∑' n : ℕ, positiveWeight n * derivativeSieveTailIndicator Y n

def derivativeSieveError (Y : ℕ) : ℝ :=
  energy (fun n => (if n = 1 then 1 else 0) -
    difference (derivativeSievePrimitive Y) n)

theorem derivativeSieveTailIndicator_bounds (Y n : ℕ) :
    0 ≤ derivativeSieveTailIndicator Y n ∧ derivativeSieveTailIndicator Y n ≤ 1 := by
  unfold derivativeSieveTailIndicator
  split_ifs <;> norm_num

theorem derivativeSieveTailMass_summable (Y : ℕ) :
    Summable (fun n : ℕ => positiveWeight n * derivativeSieveTailIndicator Y n) := by
  apply weighted_summable_of_bounded
  intro n
  rw [abs_of_nonneg (derivativeSieveTailIndicator_bounds Y n).1]
  exact (derivativeSieveTailIndicator_bounds Y n).2

theorem derivativeSieveTailIndicator_head (Y n : ℕ) (hnY : n ≤ Y) :
    derivativeSieveTailIndicator Y n = 0 := by
  unfold derivativeSieveTailIndicator
  split_ifs with h
  · have hd : n ∣ Y.factorial := Nat.dvd_factorial (by omega) hnY
    have he : Nat.gcd Y.factorial n = n := Nat.gcd_eq_right hd
    omega
  · rfl

/-- Full tail mass bound; every positive mass after the head is retained. -/
theorem derivativeSieveTailMass_bounds (Y : ℕ) :
    0 ≤ derivativeSieveTailMass Y ∧
      derivativeSieveTailMass Y ≤ 1 / ((Y : ℝ) + 1) := by
  constructor
  · exact tsum_nonneg fun n => mul_nonneg (positiveWeight_nonneg n)
      (derivativeSieveTailIndicator_bounds Y n).1
  · have hsplit := (derivativeSieveTailMass_summable Y).sum_add_tsum_nat_add (Y + 1)
    have hhead : (∑ n ∈ Finset.range (Y + 1),
        positiveWeight n * derivativeSieveTailIndicator Y n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [derivativeSieveTailIndicator_head Y n (by
        have := Finset.mem_range.mp hn
        omega), mul_zero]
    rw [hhead, zero_add] at hsplit
    unfold derivativeSieveTailMass
    rw [← hsplit]
    calc
      _ ≤ ∑' n : ℕ, positiveWeight (n + (Y + 1)) := by
        have hs := (summable_nat_add_iff (Y + 1)).mpr
          (derivativeSieveTailMass_summable Y)
        have hw := (summable_nat_add_iff (Y + 1)).mpr positiveWeight_summable
        exact hs.tsum_le_tsum (fun n => by
          simpa using mul_le_mul_of_nonneg_left
            (derivativeSieveTailIndicator_bounds Y (n + (Y + 1))).2
            (positiveWeight_nonneg (n + (Y + 1)))) hw
      _ = _ := by simpa using positiveWeight_tail_tsum (Y + 1) (by omega)

/-- Coordinate-level complete error square, retaining its signed cross term. -/
theorem derivativeSieveError_coordinate (Y n : ℕ) :
    positiveWeight n * (((if n = 1 then 1 else 0) -
      difference (derivativeSievePrimitive Y) n) ^ 2) =
      positiveWeight n * (sieveReciprocal Y.factorial)^2 -
        2 * sieveReciprocal Y.factorial *
          (positiveWeight n * derivativeSieveTailIndicator Y n) +
        positiveWeight n * derivativeSieveTailIndicator Y n := by
  cases n with
  | zero => simp [positiveWeight]
  | succ n =>
      rw [derivativeSievePrimitive_difference_succ]
      by_cases hn : n = 0
      · subst n
        simp [derivativeSieveTailIndicator]
      · have hn1 : n + 1 ≠ 1 := by omega
        have hnlt : 1 < n + 1 := by omega
        simp only [if_neg hn1, derivativeSieveTailIndicator, hnlt, true_and]
        split_ifs <;> ring

/-- Exact full infinite derivative-error polynomial, with no discarded term. -/
theorem derivativeSieveError_exact (Y : ℕ) :
    derivativeSieveError Y = (sieveReciprocal Y.factorial)^2 -
      2 * sieveReciprocal Y.factorial * derivativeSieveTailMass Y +
      derivativeSieveTailMass Y := by
  have hc := positiveWeight_summable.mul_right ((sieveReciprocal Y.factorial)^2)
  have hj := derivativeSieveTailMass_summable Y
  have hcross := hj.mul_left (2 * sieveReciprocal Y.factorial)
  unfold derivativeSieveError energy paretoInner
  simp only [← pow_two, derivativeSieveError_coordinate]
  rw [(hc.sub hcross).tsum_add hj, hc.tsum_sub hcross,
    positiveWeight_summable.tsum_mul_right, hj.tsum_mul_left, positiveWeight_tsum, one_mul]
  rfl

theorem derivativeSieveError_bounds (Y : ℕ) :
    0 ≤ derivativeSieveError Y ∧
      derivativeSieveError Y ≤ (sieveReciprocal Y.factorial)^2 +
        1 / ((Y : ℝ) + 1) := by
  constructor
  · exact paretoInner_self_nonneg _
  · rw [derivativeSieveError_exact]
    have hc := sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)
    have hj := derivativeSieveTailMass_bounds Y
    nlinarith [mul_nonneg (le_of_lt hc) hj.1]

/-- Unconditional convergence for the complete derivative energy of actual legal sieves. -/
theorem derivativeSieveError_tendsto_zero :
    Tendsto derivativeSieveError atTop (𝓝 0) := by
  have hc := factorialSieveReciprocal_tendsto_zero.pow 2
  have hn : Tendsto (fun Y : ℕ => (Y : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun Y : ℕ => 1 / ((Y : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hn
  have hupper : Tendsto (fun Y : ℕ => (sieveReciprocal Y.factorial)^2 +
      1 / ((Y : ℝ) + 1)) atTop (𝓝 0) := by simpa using hc.add hi
  exact squeeze_zero (fun Y => (derivativeSieveError_bounds Y).1)
    (fun Y => (derivativeSieveError_bounds Y).2) hupper

/-- A direct legal-sequence approximation theorem, with no optimality assumption. -/
theorem exists_legal_small_derivative_error {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℕ → ℝ, f ∈ legalSeedSpan allPositiveSeeds ∧ f 0 = 0 ∧
      energy (fun n => (if n = 1 then 1 else 0) - difference f n) < ε := by
  have he : ∀ᶠ Y : ℕ in atTop, derivativeSieveError Y < ε :=
    derivativeSieveError_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨Y, hY⟩ := he.exists
  exact ⟨derivativeSievePrimitive Y, derivativeSievePrimitive_mem_legal Y,
    derivativeSievePrimitive_zero Y, hY⟩

end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.Pareto
noncomputable section
open Filter
open scoped Topology

/-- The full signed correction is at most one complete tail mass in absolute value. -/
theorem derivativeSieveError_mass_sq_error (Y : ℕ) :
    |derivativeSieveError Y - (sieveReciprocal Y.factorial)^2| ≤
      1 / ((Y : ℝ) + 1) := by
  rw [derivativeSieveError_exact]
  have hc0 := sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)
  have hc1 := sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
  have hj := derivativeSieveTailMass_bounds Y
  apply le_trans _ hj.2
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (le_of_lt hc0) hj.1,
    mul_nonneg (sub_nonneg.mpr hc1) hj.1]

/-- Quantitative relative error, retaining the complete exact quadratic upstream. -/
theorem derivativeSieveError_relative_error (Y : ℕ) :
    |derivativeSieveError Y / (sieveReciprocal Y.factorial)^2 - 1| ≤
      1 / (((Y : ℝ) + 1) * (sieveReciprocal Y.factorial)^2) := by
  have hc : 0 < (sieveReciprocal Y.factorial)^2 :=
    sq_pos_of_pos (sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y))
  have he : derivativeSieveError Y / (sieveReciprocal Y.factorial)^2 - 1 =
      (derivativeSieveError Y - (sieveReciprocal Y.factorial)^2) /
        (sieveReciprocal Y.factorial)^2 := by
    exact div_sub_one (ne_of_gt hc)
  rw [he, abs_div, abs_of_pos hc]
  calc
    _ ≤ (1 / ((Y : ℝ) + 1)) / (sieveReciprocal Y.factorial)^2 :=
      div_le_div_of_nonneg_right (derivativeSieveError_mass_sq_error Y) (le_of_lt hc)
    _ = _ := div_div _ _ _

/-- The derivative error has an unconditional exact leading scale, stronger than vanishing. -/
theorem derivativeSieveError_ratio_tendsto_one :
    Tendsto (fun Y : ℕ => derivativeSieveError Y /
      (sieveReciprocal Y.factorial)^2) atTop (𝓝 1) := by
  have hden : Tendsto (fun Y : ℕ => ((Y : ℝ) + 1) *
      (sieveReciprocal Y.factorial)^2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1
      factorialSieveReciprocal_square_mul_tendsto_atTop) b] with Y hY
    nlinarith [sq_nonneg (sieveReciprocal Y.factorial)]
  have hi : Tendsto (fun Y : ℕ =>
      1 / (((Y : ℝ) + 1) * (sieveReciprocal Y.factorial)^2)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hden
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hi.eventually (gt_mem_nhds (sub_pos.mpr ha))] with Y hY
    have h := abs_le.mp (derivativeSieveError_relative_error Y)
    linarith
  · intro b hb
    filter_upwards [hi.eventually (gt_mem_nhds (sub_pos.mpr hb))] with Y hY
    have h := abs_le.mp (derivativeSieveError_relative_error Y)
    linarith

end
end RiemannResearch.RH.Pareto

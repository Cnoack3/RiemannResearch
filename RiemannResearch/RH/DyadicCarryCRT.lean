import RiemannResearch.RH.DyadicCarryBlocks
import RiemannResearch.RH.OddCarryJointHead
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoLegalStructure

/-!
# Exact whole-dyadic-block CRT certificates

Source: user-provided `RH_Dyadic_Block_CRT_Energy_and_Mobius_Obstruction_2026-09-20.md`,
Sections 1 and 2, supporting the block simplification and the complete signed
CRT energy certificate. All head coordinates are repaired simultaneously; all
periodic returns remain in the progression weights. These finite identities do
not supply convergence of a growing family of energies.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Reciprocal residue reflection on every coordinate, including multiples
of the modulus. The divisible class contributes zero, rather than one. -/
theorem residueFraction_reverse_all (m n : ℕ) :
    residueFraction (m + 1) (m * n) =
      (if m + 1 ∣ n then (0 : ℝ) else 1) - residueFraction (m + 1) n := by
  by_cases h : m + 1 ∣ n
  · simp [residueFraction, h, Nat.mod_eq_zero_of_dvd h, Nat.mul_mod]
  · rw [if_neg h]
    have hn : 0 < n % (m + 1) := by
      have hne : n % (m + 1) ≠ 0 := by
        intro hz
        exact h (Nat.dvd_iff_mod_eq_zero.mpr hz)
      omega
    have he : residueFraction (m + 1) (m * n) =
        residueFraction (m + 1) (m * (n % (m + 1))) := by
      simp only [residueFraction, Nat.mul_mod, Nat.mod_mod]
    rw [he]
    simpa only [residueFraction] using
      reverseResidue_head m (n % (m + 1)) hn (Nat.mod_lt _ (by omega))

/-- The explicit anchored arithmetic sequence of the whole dyadic carry. -/
def dyadicCarryBlockSequence (k : ℕ) : ℕ → ℝ := fun n =>
  residue (2 ^ k + 1) n - (if 2 ^ k + 1 ∣ n then 0 else 1)

/-- The pointwise simplification is an identity for the actual Hilbert block,
with the repository's normalized residue convention. -/
theorem dyadicCarryBlock_sequence (k : ℕ) :
    hilbertSequence (dyadicCarryBlock k (2 ^ k + 1) (by positivity)) =
      dyadicCarryBlockSequence k := by
  unfold dyadicCarryBlock
  change hilbertSequenceLinear (_ - _) = _
  rw [map_sub]
  change hilbertSequence ((2 : ℝ) ^ k •
    normalizedResidueHilbert (2 ^ k + 1) (by positivity)) -
    hilbertSequence (argumentDoublingIterate k
      (normalizedResidueHilbert (2 ^ k + 1) (by positivity))) = _
  simp only [hilbertSequence_smul,
    argumentDoublingIterate_sequence, normalizedResidueHilbert_sequence]
  funext n
  change (2 : ℝ) ^ k * residueFraction (2 ^ k + 1) n -
    residueFraction (2 ^ k + 1) (2 ^ k * n) = _
  rw [residueFraction_reverse_all]
  unfold dyadicCarryBlockSequence residueFraction residue
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hd : (2 : ℝ) ^ k + 1 ≠ 0 := by positivity
  field_simp [hd]
  ring

@[simp] theorem dyadicCarryBlockSequence_zero (k : ℕ) :
    dyadicCarryBlockSequence k 0 = 0 := by
  simp [dyadicCarryBlockSequence, residue]

theorem dyadicCarryBlockSequence_period (k P : ℕ)
    (hP : 2 ^ k + 1 ∣ P) (n : ℕ) :
    dyadicCarryBlockSequence k (n + P) = dyadicCarryBlockSequence k n := by
  simp [dyadicCarryBlockSequence, residue, Nat.dvd_iff_mod_eq_zero,
    Nat.add_mod, Nat.mod_eq_zero_of_dvd hP]

theorem dyadicCarryBlockSequence_bounded (k : ℕ) :
    ∀ n, |dyadicCarryBlockSequence k n| ≤ ((2 ^ k + 1 : ℕ) : ℝ) + 1 := by
  have hr : ∀ n, |residue (2 ^ k + 1) n| ≤ ((2 ^ k + 1 : ℕ) : ℝ) := by
    intro n
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.mod_lt n (by positivity : 0 < 2 ^ k + 1)).le
  have hi : ∀ n, |if 2 ^ k + 1 ∣ n then (0 : ℝ) else 1| ≤ 1 := by
    intro n
    split_ifs <;> norm_num
  exact bounded_sub hr hi

/-- Every common multiple of the finite legal moduli is a period of the
explicit Möbius interpolant; no property of the target is assumed. -/
theorem mobiusJointHead_period (f : ℕ → ℝ) (N P : ℕ)
    (hP : ∀ m, 0 < m → m ≤ N + 1 → m ∣ P) (n : ℕ) :
    mobiusJointHead f N (n + P) = mobiusJointHead f N n := by
  unfold mobiusJointHead
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  rw [residue_period_of_dvd (hP (N + 1) (by omega) le_rfl),
    residue_period_of_dvd (hP m (by omega) (by omega))]

/-- The actual signed error for simultaneous repair of a whole dyadic block. -/
def dyadicCarryJointError (k N : ℕ) : ℕ → ℝ := fun n =>
  dyadicCarryBlockSequence k n - mobiusJointHead (dyadicCarryBlockSequence k) N n

theorem dyadicCarryJointError_head (k N n : ℕ) (hn : n ≤ N) :
    dyadicCarryJointError k N n = 0 := by
  unfold dyadicCarryJointError
  rw [mobiusJointHead_exact _ _ (dyadicCarryBlockSequence_zero k) n hn, sub_self]

theorem dyadicCarryJointError_bounded (k N : ℕ) :
    ∃ C : ℝ, ∀ n, |dyadicCarryJointError k N n| ≤ C := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded (Set.Ici 1)
    (by intro a ha; change 1 ≤ a at ha; omega)
    (finiteResidueSubspace_le_full_legal (N + 1) (mobiusJointHead_mem _ _))
  exact ⟨_, bounded_sub (dyadicCarryBlockSequence_bounded k) hC⟩

theorem dyadicCarryJointError_period (k N P : ℕ)
    (hdP : 2 ^ k + 1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N + 1 → m ∣ P) (n : ℕ) :
    dyadicCarryJointError k N (n + P) = dyadicCarryJointError k N n := by
  simp only [dyadicCarryJointError, dyadicCarryBlockSequence_period k P hdP,
    mobiusJointHead_period _ N P hP]

/-- Full summability is discharged for the explicit repair, independently of
the common period chosen for its finite certificate. -/
theorem dyadicCarryJointError_summable (k N : ℕ) :
    Summable (fun n => positiveWeight n * (dyadicCarryJointError k N n) ^ 2) := by
  obtain ⟨C, hC⟩ := dyadicCarryJointError_bounded k N
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hC hC)

/-- Exact CRT certificate at every common positive period. This is the full
infinite Pareto energy, with every residue-class return and every mixed term. -/
theorem dyadicCarryJointError_energy_crt (k N P : ℕ) (hP0 : 0 < P)
    (hdP : 2 ^ k + 1 ∣ P)
    (hP : ∀ m, 0 < m → m ≤ N + 1 → m ∣ P) :
    (∑' n, positiveWeight n * (dyadicCarryJointError k N n) ^ 2) =
      ∑ r : Fin P, progressionWeight P (r.val + 1) *
        (dyadicCarryJointError k N (r.val + 1)) ^ 2 := by
  obtain ⟨C, hC⟩ := dyadicCarryJointError_bounded k N
  simpa only [paretoInner, pow_two] using
    periodic_paretoInner P hP0 (dyadicCarryJointError k N) hC
      (dyadicCarryJointError_period k N P hdP hP)

/-- The certificate is entirely surviving tail energy: the prescribed finite
head contributes exactly zero. -/
theorem dyadicCarryJointError_energy_eq_tail (k N : ℕ) :
    (∑' n, positiveWeight n * (dyadicCarryJointError k N n) ^ 2) =
      ∑' n, if N < n then positiveWeight n * (dyadicCarryJointError k N n) ^ 2
        else 0 := by
  apply tsum_congr
  intro n
  by_cases hn : N < n
  · rw [if_pos hn]
  · rw [if_neg hn, dyadicCarryJointError_head k N n (by omega)]
    simp

end RiemannResearch.RH.Pareto

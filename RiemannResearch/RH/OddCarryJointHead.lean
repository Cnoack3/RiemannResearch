import RiemannResearch.RH.OddCarryArithmetic
import RiemannResearch.RH.FiniteResidueHeadSurjectivity
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.ThresholdLegalIntegrability
import RiemannResearch.RH.ParetoCovariance

/-!
# Simultaneous arithmetic boundary correction for odd carries

Source: user-provided `RH_DPP_Odd_Carry_Lean_2026-09-20_Continuation(1).md`,
Sections 3 and 5, which ask for joint correction of the surviving carry
boundaries while retaining the complete signed residual energy. The explicit
Möbius interpolation formula was derived in the September 20 continuation.

The finite construction below repairs every coordinate in the prescribed head.
Its coefficients are the actual divisor-inverted carry jumps. The full signed
tail formula is retained; no uniform energy bound or RH assertion is supplied.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

theorem mobiusDifference_sub_function (m : ℕ) (f g : ℕ → ℝ) :
    mobiusDifference m (fun n => f n - g n) =
      mobiusDifference m f - mobiusDifference m g := by
  unfold mobiusDifference
  simp_rw [show ∀ d : ℕ, (f d - g d) - (f (d-1) - g (d-1)) =
    (f d - f (d-1)) - (g d - g (d-1)) by intro d; ring]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The negative period-boundary progression inverts to one atom. -/
theorem mobius_sum_divisibility (m d : ℕ) (hm : 0 < m) :
    (∑ k ∈ m.divisors, (ArithmeticFunction.moebius (m / k) : ℝ) *
      (if d ∣ k then (1 : ℝ) else 0)) = if m = d then 1 else 0 := by
  have hs : ∀ k > 0,
      (∑ j ∈ k.divisors, if j = d then (1 : ℝ) else 0) =
        if d ∣ k then 1 else 0 := by
    intro k hk
    simp [Nat.mem_divisors, ne_of_gt hk]
  exact (mobius_inversion (fun j => if j = d then (1 : ℝ) else 0)
    (fun k => if d ∣ k then (1 : ℝ) else 0)).mp hs m hm

/-- Exact arithmetic coefficients for simultaneous carry-boundary correction. -/
theorem doublingCarry_mobiusDifference (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) :
    mobiusDifference m (doublingCarry d) =
      (∑ k ∈ m.divisors, (ArithmeticFunction.moebius (m / k) : ℝ) *
        (if k % d = (d + 1) / 2 then (1 : ℝ) else 0)) -
      (if m = d then 1 else 0) := by
  have hj (k : ℕ) (hk : 0 < k) :
      doublingCarry d k - doublingCarry d (k-1) =
        (if k % d = (d + 1) / 2 then (1 : ℝ) else 0) -
        (if d ∣ k then (1 : ℝ) else 0) := by
    have h := doublingCarry_succ_sub d (k-1) hd
    simpa only [Nat.sub_add_cancel hk, Nat.dvd_iff_mod_eq_zero] using h
  unfold mobiusDifference
  calc
    _ = ∑ k ∈ m.divisors, (ArithmeticFunction.moebius (m/k) : ℝ) *
        ((if k % d = (d+1)/2 then (1 : ℝ) else 0) -
          (if d ∣ k then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hj k (Nat.pos_of_mem_divisors hk)]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, mobius_sum_divisibility m d hm]

/-- A completely explicit finite legal interpolant for an anchored sequence. -/
def mobiusJointHead (f : ℕ → ℝ) (N : ℕ) : ℕ → ℝ := fun n =>
  ∑ k ∈ Finset.Icc 1 N, (mobiusDifference k f / (k : ℝ)) *
    (residue (N+1) n - residue k n)

theorem mobiusJointHead_mem (f : ℕ → ℝ) (N : ℕ) :
    mobiusJointHead f N ∈ finiteResidueSubspace (N+1) := by
  have he : mobiusJointHead f N =
      ∑ k ∈ Finset.Icc 1 N, (mobiusDifference k f / (k : ℝ)) •
        (residue (N+1) - residue k) := by
    funext n
    simp [mobiusJointHead, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply Submodule.sum_mem
  intro k hk
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact residue_mem_finiteResidueSubspace (by omega) le_rfl
  · exact residue_mem_finiteResidueSubspace (by omega) (by omega)

/-- The simultaneous correction preserves all prescribed finite Möbius charges. -/
theorem mobiusDifference_mobiusJointHead (f : ℕ → ℝ) (N m : ℕ)
    (hm : 0 < m) (hmN : m ≤ N) :
    mobiusDifference m (mobiusJointHead f N) = mobiusDifference m f := by
  unfold mobiusJointHead
  rw [mobiusDifference_sum]
  have hterm (k : ℕ) :
      mobiusDifference m (fun n => residue (N+1) n - residue k n) =
        if m = k then (k : ℝ) else 0 := by
    rw [mobiusDifference_sub_function,
      mobiusDifference_residue_initial m (N+1) hm,
      mobiusDifference_residue_initial m k hm]
    have hne : m ≠ N+1 := by omega
    simp only [if_neg hne, sub_zero]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_eq_single m]
  · simp only [if_pos rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast ne_of_gt hm)
  · intro k hk hkm
    simp [Ne.symm hkm]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨by omega, hmN⟩)).elim

/-- Finite divisor inversion reconstructs every repaired boundary jointly. -/
theorem mobiusJointHead_exact (f : ℕ → ℝ) (N : ℕ) (hf : f 0 = 0) :
    ∀ n, n ≤ N → mobiusJointHead f N n = f n := by
  intro n
  induction n with
  | zero => intro _; simp [mobiusJointHead, residue, hf]
  | succ n ih =>
    intro hn
    have hs : (∑ k ∈ (n+1).divisors,
        mobiusDifference k (mobiusJointHead f N)) =
        ∑ k ∈ (n+1).divisors, mobiusDifference k f := by
      apply Finset.sum_congr rfl
      intro k hk
      apply mobiusDifference_mobiusJointHead f N k (Nat.pos_of_mem_divisors hk)
      exact (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hk)).trans hn
    rw [sum_mobiusDifference _ (n+1) (by omega),
      sum_mobiusDifference _ (n+1) (by omega)] at hs
    simp only [Nat.add_sub_cancel] at hs
    have hi := ih (by omega)
    linarith

/-- Exact simultaneous head correction for every carry modulus at least two. -/
theorem doublingCarry_joint_head (d N : ℕ) (hd : 2 ≤ d) :
    mobiusJointHead (doublingCarry d) N ∈ finiteResidueSubspace (N+1) ∧
      ∀ n, n ≤ N → mobiusJointHead (doublingCarry d) N n = doublingCarry d n := by
  refine ⟨mobiusJointHead_mem _ _, mobiusJointHead_exact _ _ ?_⟩
  simp [doublingCarry, show ¬ d ≤ 0 by omega]

theorem residue_eq_floor_difference (d n : ℕ) :
    residue d n = (n : ℝ) - (d : ℝ) * (n / d : ℕ) := by
  have h := Nat.mod_add_div n d
  have hR : ((n % d : ℕ) : ℝ) + (d : ℝ) * (n / d : ℕ) = (n : ℝ) := by
    exact_mod_cast h
  unfold residue
  linarith

/-- Full signed residual, including the compensating tail floor. -/
theorem mobiusJointHead_signed_error (f : ℕ → ℝ) (N n : ℕ) :
    f n - mobiusJointHead f N n =
      f n - (∑ k ∈ Finset.Icc 1 N, mobiusDifference k f * (n / k : ℕ)) +
        ((N+1 : ℕ) : ℝ) *
          (∑ k ∈ Finset.Icc 1 N, mobiusDifference k f / (k : ℝ)) *
          (n / (N+1) : ℕ) := by
  have ht (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
      (mobiusDifference k f / (k : ℝ)) *
          (residue (N+1) n - residue k n) =
        mobiusDifference k f * (n / k : ℕ) -
          (mobiusDifference k f / (k : ℝ)) * ((N+1 : ℕ) : ℝ) *
            (n / (N+1) : ℕ) := by
    rw [residue_eq_floor_difference, residue_eq_floor_difference]
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
    field_simp [hk0]
    ring
  unfold mobiusJointHead
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]
  ring

/-- The complete carry-error energy is summable for every finite joint repair. -/
theorem doublingCarry_joint_error_summable (d N : ℕ) :
    Summable (fun n => positiveWeight n *
      (doublingCarry d n - mobiusJointHead (doublingCarry d) N n) ^ 2) := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded (Set.Ici 1)
    (by intro a ha; change 1 ≤ a at ha; omega)
    (finiteResidueSubspace_le_full_legal (N+1) (mobiusJointHead_mem _ _))
  have hb : ∀ n, |doublingCarry d n| ≤ (1 : ℝ) := by
    intro n
    unfold doublingCarry
    split_ifs <;> norm_num
  have he := bounded_sub hb hC
  simpa only [pow_two] using
    weighted_summable_of_bounded (bounded_product he he)

/-- All head energy is exactly zero. The surviving full tail retains the
signed arithmetic sum and the compensating floor term inside the square. -/
theorem doublingCarry_joint_energy_eq_tail (d N : ℕ) (hd : 2 ≤ d) :
    (∑' n, positiveWeight n *
      (doublingCarry d n - mobiusJointHead (doublingCarry d) N n) ^ 2) =
    ∑' n, if N < n then positiveWeight n *
      (doublingCarry d n -
          (∑ k ∈ Finset.Icc 1 N,
            mobiusDifference k (doublingCarry d) * (n / k : ℕ)) +
        ((N+1 : ℕ) : ℝ) *
          (∑ k ∈ Finset.Icc 1 N,
            mobiusDifference k (doublingCarry d) / (k : ℝ)) *
          (n / (N+1) : ℕ)) ^ 2 else 0 := by
  apply tsum_congr
  intro n
  by_cases hn : N < n
  · rw [if_pos hn, mobiusJointHead_signed_error]
  · rw [if_neg hn, (doublingCarry_joint_head d N hd).2 n (by omega)]
    simp

end RiemannResearch.RH.Pareto

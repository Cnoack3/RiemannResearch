import RiemannResearch.Analysis.DyadicBlockRigidity
import RiemannResearch.Analysis.SummableMultiples
import RiemannResearch.Analysis.DyadicTailRigidity
import RiemannResearch.Analysis.SummableDiscreteAbel
import RiemannResearch.RH.ParetoSignedTails
import RiemannResearch.RH.DyadicResidueJumps
/-!
# Actual Pareto annihilators with summable signed tails
Source: user-provided analytic research notes, September 11, 2026.

The exact summation-by-parts identity supplies the multiples equations from
actual legal orthogonality. Absolute tail summability then gives exact dyadic
scaling. The formerly missing Fourier/Sobolev implication is discharged by
DyadicBlockRigidity through exact discrete block averages. The final theorem
requires only summability of the signed tail; its weighted square summability
is proved from the actual difference energy, not assumed.
-/
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

theorem paretoInner_eq_signedTail_jump {h g : ℕ → ℝ} {C : ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    (hA : Summable (anchoredSignedTail h))
    (hg : ∀ n, |g n| ≤ C) (hgzero : g 0 = 0) :
    paretoInner h g =
      ∑' n, anchoredSignedTail h n*(g n-g (n-1)) := by
  calc
    _ = ∑' n, (anchoredSignedTail h n-anchoredSignedTail h (n+1))*g n := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        simp [hgzero]
      · rw [anchoredSignedTail_difference hs (Nat.pos_of_ne_zero hn)]
        unfold signedCoefficient
        ring
    _ = _ := summable_discrete_summation_by_parts hA
      (anchoredSignedTail_zero h) hg

private theorem summable_divisibility_mask {A : ℕ → ℝ} (hA : Summable A) (d : ℕ) :
    Summable (fun n => if d ∣ n then A n else 0) := by
  apply hA.abs.of_norm_bounded
  intro n
  split_ifs <;> simp [Real.norm_eq_abs]

theorem dyadic_pairing_eq_signedTail_multiples {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k*h k^2))
    (hA : Summable (anchoredSignedTail h)) (m : ℕ) :
    paretoInner h (dilation m (residue 2)) =
      (m : ℝ)*((∑' j, if m ∣ j then anchoredSignedTail h j else 0) -
        2*(∑' j, if 2*m ∣ j then anchoredSignedTail h j else 0)) := by
  rw [paretoInner_eq_signedTail_jump hs hA (dyadic_dilation_abs_le m)
    (by simp [dilation, residue])]
  have hp : ∀ n, anchoredSignedTail h n *
      (dilation m (residue 2) n-dilation m (residue 2) (n-1)) =
      (m : ℝ)*((if m ∣ n then anchoredSignedTail h n else 0) -
        2*(if 2*m ∣ n then anchoredSignedTail h n else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [anchoredSignedTail_zero]
    · rw [dilation_residue_difference m 2 n (Nat.pos_of_ne_zero hn)]
      simp only [Nat.mul_comm m 2, Nat.cast_mul, Nat.cast_ofNat]
      split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_mul_left,
    (summable_divisibility_mask hA m).tsum_sub
      ((summable_divisibility_mask hA (2*m)).mul_left 2), tsum_mul_left]

/-- Actual dyadic orthogonality and summable signed tails force exact scaling.
The summability premise is additional regularity, not a consequence of L2. -/
theorem LegalAnnihilator.signedTail_dyadic_scaling
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h)) :
    ∀ n, anchoredSignedTail h (2*n) = anchoredSignedTail h n / 2 := by
  apply dyadic_scaling_of_summable_multiples_equations hA (anchoredSignedTail_zero h)
  intro m hm
  have ho := hh.2 _ (dilation_generator_mem S hS hm)
  rw [dyadic_pairing_eq_signedTail_multiples hh.1 hA m,
    tsum_multiples_eq hm, tsum_multiples_eq (by omega : 0 < 2*m)] at ho
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have he := (mul_eq_zero.mp ho).resolve_left hmR
  linarith

/-- Restricted uniqueness with explicitly stronger weighted-tail regularity. -/
theorem legalAnnihilator_eq_zero_of_summable_weighted_tail
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h))
    (hweighted : Summable (fun n : ℕ => ((n : ℝ)*anchoredSignedTail h n)^2))
    {n : ℕ} (hn : 0 < n) : h n = 0 := by
  have hscale := hh.signedTail_dyadic_scaling hS hA
  have hz : anchoredSignedTail h = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      exact anchoredSignedTail_zero h
    · exact DyadicTailRigidity.eq_zero_of_dyadic_scaling_of_weighted_square_summable
        (anchoredSignedTail h) (fun j _ => hscale j) hweighted k
        (Nat.pos_of_ne_zero hk)
  exact eq_zero_of_anchoredSignedTail_eq_zero hh.1 hz hn
end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
/-- Restricted uniqueness from summable tails and n A(n) tending to zero. -/
theorem legalAnnihilator_eq_zero_of_weighted_tail_tendsto
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h))
    (hweighted : Filter.Tendsto (fun n : ℕ => (n : ℝ)*anchoredSignedTail h n)
      Filter.atTop (nhds 0)) {n : ℕ} (hn : 0 < n) : h n = 0 := by
  have hscale := hh.signedTail_dyadic_scaling hS hA
  have hz : anchoredSignedTail h = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      exact anchoredSignedTail_zero h
    · exact DyadicTailRigidity.eq_zero_of_dyadic_scaling_of_weighted_tendsto
        (anchoredSignedTail h) (fun j _ => hscale j) hweighted k
        (Nat.pos_of_ne_zero hk)
  exact eq_zero_of_anchoredSignedTail_eq_zero hh.1 hz hn
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
/-- Checked provider discharging the formerly missing Fourier/Sobolev upgrade. -/
theorem LegalAnnihilator.signedTail_weighted_square_summable
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h)) :
    Summable (fun n : ℕ => ((n : ℝ)*anchoredSignedTail h n)^2) :=
  RiemannResearch.Analysis.DyadicBlockRigidity.weighted_square_summable_of_difference_energy
    hA (anchoredSignedTail_energy_summable hh.1)
    (hh.signedTail_dyadic_scaling hS hA)

/-- Full summable-tail uniqueness. The finite difference energy is provided
by actual weighted L2 membership; no separate Sobolev premise is assumed. -/
theorem legalAnnihilator_eq_zero_of_summable_signedTail
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h)) {n : ℕ} (hn : 0 < n) : h n = 0 :=
  legalAnnihilator_eq_zero_of_summable_weighted_tail hS hh hA
    (hh.signedTail_weighted_square_summable hS hA) hn

theorem legalAnnihilator_anchored_eq_zero_of_summable_signedTail
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hA : Summable (anchoredSignedTail h)) (hzero : h 0 = 0) : h = 0 := by
  funext n
  cases n with
  | zero => exact hzero
  | succ n =>
    exact legalAnnihilator_eq_zero_of_summable_signedTail hS hh hA (Nat.succ_pos n)
end RiemannResearch.RH.Pareto

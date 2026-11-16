import RiemannResearch.RH.ExactHeadGreenProfile
import RiemannResearch.RH.MobiusAffineProfile
import RiemannResearch.RH.ParetoArithmeticRepair
import Mathlib.Data.Nat.Totient

/-!
# Primitive integrated-Ramanujan coordinates of Green profile errors
Source: the attached exact-head Green memorandum, sections 5 and 10.
The repository's actual integrated Ramanujan packets give the centered-residue
decomposition for every positive modulus, not only squarefree ones. Pairing
and square-function identities allow arbitrary finite weights. Uniform control
of the resulting moving-conductor square function is not asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadGreenPrimitive
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.Pareto

def primitiveScore (s : Finset ℕ) (w R : ℕ → ℝ) (a : ℕ) : ℝ :=
  pairing s w R (fun r => ramanujanPacket a r - (Nat.totient a : ℝ) / 2)

theorem totient_divisors_gt_one (d : ℕ) (hd : 0 < d) :
    (∑ a ∈ d.divisors.filter (fun a => 1 < a), (Nat.totient a : ℝ)) = (d : ℝ) - 1 := by
  have h1 : 1 ∈ d.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩
  have hf : d.divisors.filter (fun a => 1 < a) = d.divisors.erase 1 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨ha,ha1⟩
      exact ⟨by omega,ha⟩
    · rintro ⟨ha1,ha⟩
      have hap := Nat.pos_of_mem_divisors ha
      exact ⟨ha,by omega⟩
  have hs : (∑ a ∈ d.divisors, (Nat.totient a : ℝ)) = (d : ℝ) := by
    exact_mod_cast Nat.sum_totient d
  have he := Finset.sum_erase_add d.divisors (fun a => (Nat.totient a : ℝ)) h1
  rw [hs] at he
  norm_num at he
  rw [hf]
  linarith

/-- Exact arithmetic centering; no Haar or Pareto orthogonality is presumed. -/
theorem centeredResidue_eq_primitive_sum (d r : ℕ) (hd : 0 < d) :
    ExactHeadGreenProfile.centeredResidue d r =
      ∑ a ∈ d.divisors.filter (fun a => 1 < a),
        (ramanujanPacket a r - (Nat.totient a : ℝ) / 2) := by
  rw [Finset.sum_sub_distrib, ramanujanPacket_divisor_sum_gt_one d r hd]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, totient_divisors_gt_one d hd]
  rfl

theorem centered_score_eq_primitive_sum (s : Finset ℕ) (w R : ℕ → ℝ)
    (d : ℕ) (hd : 0 < d) :
    pairing s w R (ExactHeadGreenProfile.centeredResidue d) =
      ∑ a ∈ d.divisors.filter (fun a => 1 < a), primitiveScore s w R a := by
  unfold primitiveScore pairing
  simp_rw [centeredResidue_eq_primitive_sum d _ hd, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The moving-conductor square function is exactly the canonical affine loss.
This is an identity, not a bound on the actual residual direction. -/
theorem canonical_energy_eq_primitive_square (s : Finset ℕ) (w R : ℕ → ℝ) (x : ℕ) :
    (∑ d ∈ Finset.Icc 1 x, MobiusAffineProfile.weight d *
      ((d : ℝ) * score s w R d -
        (pairing s w R (fun r => (r : ℝ)) + pairing s w R (fun _ => 1) / 2 -
          (d : ℝ) * pairing s w R (fun _ => 1) / 2)) ^ 2) =
    ∑ d ∈ Finset.Icc 1 x, MobiusAffineProfile.weight d *
      (∑ a ∈ d.divisors.filter (fun a => 1 < a), primitiveScore s w R a) ^ 2 := by
  apply Finset.sum_congr rfl
  intro d hd
  rw [canonical_profile_identity, centered_score_eq_primitive_sum s w R d (Finset.mem_Icc.mp hd).1]
  ring

end RiemannResearch.RH.ExactHeadGreenPrimitive

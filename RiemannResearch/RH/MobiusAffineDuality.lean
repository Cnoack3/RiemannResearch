import RiemannResearch.Analysis.FiniteAffineResidualDuality
import RiemannResearch.RH.MobiusAffineProfile
import RiemannResearch.NumberTheory.DivisorIncidence
import Mathlib.Tactic

/-!
# Removing affine directions from the Mobius dispersion budget

The exact-head affine fit has two normal equations. They let us replace the
full squarefree mass by the squared distance of the Mobius vector from any
affine observer. Choosing its own normal fit never increases the budget.
This is a finite Hilbert projection improvement of the user's R4 agenda,
not an unconditional cofinal estimate.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence

theorem profile_error_sq_le_affine_mobius_loss (x : ℕ) (b : ℕ → ℝ)
    (c0 c1 a0 a1 : ℝ)
    (h0 : (∑ d ∈ Finset.Icc 1 x, weight d * (b d - c0 - c1 * ((d : ℝ) / x))) = 0)
    (h1 : (∑ d ∈ Finset.Icc 1 x,
      weight d * ((d : ℝ) / x) * (b d - c0 - c1 * ((d : ℝ) / x))) = 0) :
    (signedSum x b - signedSum x (fun d => c0 + c1 * ((d : ℝ) / x))) ^ 2 ≤
      affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
        (fun d => (ArithmeticFunction.moebius d : ℝ)) a0 a1 *
      affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x) b c0 c1 := by
  have he : signedSum x b - signedSum x (fun d => c0 + c1 * ((d : ℝ) / x)) =
      pairing (Finset.Icc 1 x) weight (fun d => (ArithmeticFunction.moebius d : ℝ))
        (fun d => b d - c0 - c1 * ((d : ℝ) / x)) := by
    rw [pairing_eq_signedSum]
    unfold signedSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  exact affine_residual_pairing_sq_le _ _ _ _ _ a0 a1
    (fun d _ => weight_nonneg d) h0 h1

theorem mobius_energy_eq_mass (x : ℕ) :
    energy (Finset.Icc 1 x) weight (fun d => (ArithmeticFunction.moebius d : ℝ)) =
      mass (Finset.Icc 1 x) weight := by
  apply Finset.sum_congr rfl
  intro d hd
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [weight, h]

/-- The best affine observer budget exists at every cutoff x >= 2. -/
theorem exists_normal_mobius_budget (x : ℕ) (hx : 2 ≤ x) :
    ∃ a0 a1 : ℝ,
      (∑ d ∈ Finset.Icc 1 x,
        weight d * ((ArithmeticFunction.moebius d : ℝ) - a0 - a1 * ((d : ℝ) / x))) = 0 ∧
      (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x) *
        ((ArithmeticFunction.moebius d : ℝ) - a0 - a1 * ((d : ℝ) / x))) = 0 ∧
      0 ≤ affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
        (fun d => (ArithmeticFunction.moebius d : ℝ)) a0 a1 ∧
      affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
        (fun d => (ArithmeticFunction.moebius d : ℝ)) a0 a1 ≤
          mass (Finset.Icc 1 x) weight := by
  obtain ⟨a0, a1, h0, h1⟩ := exists_affine_normal (Finset.Icc 1 x) weight
    (fun d => (d : ℝ) / x) (fun d => (ArithmeticFunction.moebius d : ℝ))
    (affine_determinant_pos x hx).ne'
  refine ⟨a0, a1, h0, h1, energy_nonneg _ _ _ (fun d _ => weight_nonneg d), ?_⟩
  simpa only [mobius_energy_eq_mass] using affine_normal_loss_le_energy
    (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
    (fun d => (ArithmeticFunction.moebius d : ℝ)) a0 a1
    (fun d _ => weight_nonneg d) h0 h1

/-- Exact best-observer data: the dispersion factor drops from 61/30 to 160/191. -/
theorem mobius_five_normal_loss :
    (∑ d ∈ Finset.Icc 1 5, weight d *
      ((ArithmeticFunction.moebius d : ℝ) - 229 / 191 - (-590 / 191) * ((d : ℝ) / 5))) = 0 ∧
    (∑ d ∈ Finset.Icc 1 5, weight d * ((d : ℝ) / 5) *
      ((ArithmeticFunction.moebius d : ℝ) - 229 / 191 - (-590 / 191) * ((d : ℝ) / 5))) = 0 ∧
    affineLoss (Finset.Icc 1 5) weight (fun d => (d : ℝ) / 5)
      (fun d => (ArithmeticFunction.moebius d : ℝ)) (229 / 191) (-590 / 191) = 160 / 191 ∧
    mass (Finset.Icc 1 5) weight = 61 / 30 := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  norm_num [affineLoss, energy, mass, weight, sum_Icc_one, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_apply_prime (show Nat.Prime 5 by norm_num), h4]

end RiemannResearch.RH.MobiusAffineProfile

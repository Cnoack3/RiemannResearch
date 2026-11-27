import RiemannResearch.Analysis.RationalLandauInghamTangent
import RiemannResearch.Analysis.ActualZeroTriangularIntegral
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroCountUpper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reconstruction of physical gap tests at arbitrary bandwidth

The signed Taylor head is the one in `RationalLandauInghamTangent`.
Bounding the comparison cosh by the full zero count on the critical strip
gives an explicit order for any physical frequency and coefficient mass.
The reflected Landau sum and its signed horizontal moments still occur on
the arithmetic side. No evaluation of these moments is assumed here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- At any real frequency the indicated order achieves absolute amplitude
error at most `exp (-b)`. The comparison uses only the actual critical strip. -/
theorem ordinate_reconstruction_exp_error (T u b : ℝ) (J : ℕ)
    (hJ : Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + |u| + 1 + b ≤
      ((2 * (J + 1) : ℕ) : ℝ) * Real.log 2) :
    ‖ordinateSum T u - reconstructedOrdinateSum T u J‖ ≤ Real.exp (-b) := by
  let N : ℝ := Zeta23.Ncount 0 T
  let n := 2 * (J + 1)
  let v := 2 * (|u| + 1)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hN1 : 0 < N + 1 := by linarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hu : |u| ≤ v := by dsimp [v]; linarith [abs_nonneg u]
  have hratio : |u| / v ≤ 1 / 2 := by
    apply (div_le_iff₀ hv).mpr
    dsimp [v]
    linarith
  have he : Real.cosh (v / 2) - 1 ≤ Real.exp (|u| + 1) := by
    have hn : Real.exp (-(|u| + 1)) ≤ Real.exp (|u| + 1) :=
      Real.exp_le_exp.mpr (by linarith [abs_nonneg u])
    rw [show v / 2 = |u| + 1 by dsimp [v]; ring, Real.cosh_eq]
    linarith
  have hsum : badWeightedSum T 0 (fun t => Real.cosh (v*t)-1) ≤
      (N+1) * Real.exp (|u|+1) := by
    apply (badCoshSum_le_count T 0 v hv.le).trans
    change N * _ ≤ _
    calc
      _ ≤ N * Real.exp (|u|+1) := mul_le_mul_of_nonneg_left he hN
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have htwo : (1/2:ℝ)^n = Real.exp (-(n:ℝ)*Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    simp [one_div]
  rw [ordinate_sub_reconstructed]
  calc
    _ ≤ (|u|/v)^n * badWeightedSum T 0 (fun t => Real.cosh (v*t)-1) :=
      horizontalTaylorError_le_coshSum T u v J hv hu
    _ ≤ (|u|/v)^n * ((N+1)*Real.exp (|u|+1)) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (div_nonneg (abs_nonneg u) hv.le) _)
    _ ≤ (1/2:ℝ)^n * ((N+1)*Real.exp (|u|+1)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg (abs_nonneg u) hv.le) hratio n)
        (by positivity)
    _ = Real.exp (-(n:ℝ)*Real.log 2 + Real.log (N+1) + (|u|+1)) := by
      rw [Real.exp_add (-(n:ℝ)*Real.log 2 + Real.log (N+1)) (|u|+1),
        Real.exp_add (-(n:ℝ)*Real.log 2) (Real.log (N+1)), Real.exp_log hN1, htwo]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change Real.log (N + 1) + |u| + 1 + b ≤ (n : ℝ) * Real.log 2 at hJ
      linarith)

/-- All pairs of copies contribute, including those at equal ordinates.
The bound is absolute after division by the number of copies. -/
theorem gap_reconstruction_exp_error (T u b : ℝ) (J : ℕ) (hb : 0 ≤ b)
    (hJ : Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + |u| + 1 + b ≤
      ((2 * (J + 1) : ℕ) : ℝ) * Real.log 2) :
    |((∑ p : Copies T, ∑ q : Copies T,
        Real.cos ((copyOrdinate T p - copyOrdinate T q)*u)) -
        ‖reconstructedOrdinateSum T u J‖^2) / (Zeta23.Ncount 0 T : ℝ)| ≤
      3 * Real.exp (-b) := by
  by_cases hN : Zeta23.Ncount 0 T = 0
  · simp [hN, (Real.exp_pos (-b)).le]
  let N : ℝ := Zeta23.Ncount 0 T
  let x := ‖ordinateSum T u‖
  let y := ‖reconstructedOrdinateSum T u J‖
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : 0 < N := by linarith
  have he : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd : |x-y| ≤ Real.exp (-b) :=
    (abs_norm_sub_norm_le _ _).trans (ordinate_reconstruction_exp_error T u b J hJ)
  have hx : x ≤ N := norm_ordinateSum_le_count T u
  have hxy : 0 ≤ x+y := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs : x+y ≤ 3*N := by linarith only [(abs_le.mp hd).1, hx, hN1, he]
  rw [← OrdinateCollisionCertificate.occurrenceAmplitude_normSq,
    ActualZeroCollisionCertificate.actual_occurrenceAmplitude, Complex.normSq_eq_norm_sq]
  change |(x^2-y^2)/N| ≤ _
  rw [sq_sub_sq, abs_div, abs_mul, abs_of_nonneg hxy, abs_of_pos hN0]
  calc
    _ ≤ ((3*N)*Real.exp (-b))/N := div_le_div_of_nonneg_right
      (mul_le_mul hs hd (abs_nonneg _) (by positivity)) hN0.le
    _ = _ := by field_simp [hN0.ne']

/-- A logarithmic allowance for the total coefficient mass makes the
error uniform over all tests within the supplied radius and mass. -/
theorem weighted_gap_reconstruction_exp_error {ι : Type*} (s : Finset ι)
    (a u : ι → ℝ) (T U M b : ℝ) (J : ℕ)
    (hu : ∀ i ∈ s, |u i| ≤ U) (hM : ∑ i ∈ s, |a i| ≤ M) (hb : 0 ≤ b)
    (hJ : Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + U + 1 +
      Real.log (M + 1) + b ≤ ((2 * (J + 1) : ℕ) : ℝ) * Real.log 2) :
    |∑ i ∈ s, a i *
      (((∑ p : Copies T, ∑ q : Copies T,
          Real.cos ((copyOrdinate T p - copyOrdinate T q)*u i)) -
          ‖reconstructedOrdinateSum T (u i) J‖^2) / (Zeta23.Ncount 0 T : ℝ))| ≤
      3 * Real.exp (-b) := by
  have h0 : 0 ≤ M := (Finset.sum_nonneg fun i _ => abs_nonneg (a i)).trans hM
  have h1 : 0 < M+1 := by linarith
  let d := Real.log (M + 1) + b
  have hd : 0 ≤ d := add_nonneg (Real.log_nonneg (by linarith)) hb
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ s, |a i| * (3 * Real.exp (-d)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply gap_reconstruction_exp_error _ _ _ _ hd
      dsimp [d]
      linarith only [hu i hi,hJ]
    _ ≤ M * (3 * Real.exp (-d)) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hM (by positivity)
    _ ≤ _ := by
      have hfrac : M / (M + 1) ≤ 1 := (div_le_one h1).mpr (by linarith)
      calc
        _ = (M / (M + 1)) * (3 * Real.exp (-b)) := by
          dsimp [d]
          rw [neg_add_rev, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log h1]
          ring
        _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac
                      (show 0 ≤ 3*Real.exp (-b) by positivity)

/-- A Borel choice of Taylor order, valid over the whole frequency line. -/
def gapReconstructionOrder (T u b : ℝ) : ℕ :=
  ⌈(Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + |u| + 1 + b) / (2 * Real.log 2)⌉₊

theorem gapReconstructionOrder_sufficient (T u b : ℝ) :
    Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + |u| + 1 + b ≤
      ((2 * (gapReconstructionOrder T u b + 1) : ℕ) : ℝ) * Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 2 * Real.log 2 := by positivity
  have hh := (div_le_iff₀ hd).mp (Nat.le_ceil
    ((Real.log ((Zeta23.Ncount 0 T : ℝ) + 1) + |u| + 1 + b) / (2 * Real.log 2)))
  change _ ≤ (gapReconstructionOrder T u b : ℝ) * (2 * Real.log 2) at hh
  push_cast
  linarith only [hh, hl]

#print axioms weighted_gap_reconstruction_exp_error
end RiemannResearch.Analysis.ActualZeroOrdinate

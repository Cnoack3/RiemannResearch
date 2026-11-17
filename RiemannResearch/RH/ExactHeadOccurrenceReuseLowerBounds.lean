import RiemannResearch.RH.ExactHeadOccurrenceReuseCertificates
import Mathlib.Tactic.Linarith

/-!
# Quantitative rational certificates for positive reuse cost

Source: actual coefficient stability and complete-weight rational enclosures.
A separated pair of coefficients in one gcd fiber gives an explicit rational
lower bound for the true compression cost, without solving an atom system.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open ExactHeadAtomOptimizer

/-- A discrepancy within one gcd fiber forces quantitative compression cost. -/
theorem occurrence_fiber_gap_sq_le_reuse (P x : ℕ) (hP : 0 < P)
    (n m : ℕ) (hn : n ∈ freePositions P x) (hm : m ∈ freePositions P x)
    (hg : Nat.gcd n P = Nat.gcd m P) :
    (occurrenceCoefficients P x n - occurrenceCoefficients P x m)^2 ≤
      4 * ((progressionWeight P n)⁻¹ + (progressionWeight P (n-1))⁻¹ +
        (progressionWeight P m)⁻¹ + (progressionWeight P (m-1))⁻¹) * reuseEnergy P x := by
  have h1 := occurrence_atom_coefficient_error_sq_le P x hP n hn
  have h2 := occurrence_atom_coefficient_error_sq_le P x hP m hm
  rw [hg] at h1
  nlinarith [sq_nonneg (occurrenceCoefficients P x n + occurrenceCoefficients P x m -
    2 * atomNormalCoefficients P x (Nat.gcd m P))]

def rationalReuseFactor (P K n m : ℕ) : ℚ :=
  4 * ((elementaryProgressionInterval P n K).lo⁻¹ +
    (elementaryProgressionInterval P (n-1) K).lo⁻¹ +
    (elementaryProgressionInterval P m K).lo⁻¹ +
    (elementaryProgressionInterval P (m-1) K).lo⁻¹)

theorem rationalReuseFactor_pos (P K n m : ℕ) (hP : 0 < P)
    (hn : 1 < n) (hm : 1 < m) : 0 < rationalReuseFactor P K n m := by
  have h1 := elementaryProgressionInterval_lower_pos P n K hP (by omega)
  have h2 := elementaryProgressionInterval_lower_pos P (n-1) K hP (by omega)
  have h3 := elementaryProgressionInterval_lower_pos P m K hP (by omega)
  have h4 := elementaryProgressionInterval_lower_pos P (m-1) K hP (by omega)
  unfold rationalReuseFactor
  positivity

theorem rationalReuseFactor_bounds_actual (P K n m : ℕ) (hP : 0 < P)
    (hn : 1 < n) (hm : 1 < m) :
    4 * ((progressionWeight P n)⁻¹ + (progressionWeight P (n-1))⁻¹ +
      (progressionWeight P m)⁻¹ + (progressionWeight P (m-1))⁻¹) ≤
        (rationalReuseFactor P K n m : ℝ) := by
  have hw (r : ℕ) (hr : 0 < r) :
      (progressionWeight P r)⁻¹ ≤
        ((elementaryProgressionInterval P r K).lo : ℝ)⁻¹ := by
    have hlo : (0 : ℝ) < ((elementaryProgressionInterval P r K).lo : ℝ) :=
      (Rat.cast_pos (K := ℝ)).2 (elementaryProgressionInterval_lower_pos P r K hP hr)
    exact (inv_le_inv₀ (progressionWeight_pos P r hP hr) hlo).mpr
      (elementaryProgressionInterval_contains P r K hP hr).1
  simp only [rationalReuseFactor, Rat.cast_mul, Rat.cast_add, Rat.cast_inv, Rat.cast_ofNat]
  linarith [hw n (by omega), hw (n-1) (by omega),
    hw m (by omega), hw (m-1) (by omega)]

/-- Any nonnegative certified gap yields an explicit lower bound for actual reuse energy. -/
theorem reuseEnergy_lower_of_fiber_gap (P x K n m : ℕ) (hP : 0 < P)
    (hn : n ∈ freePositions P x) (hm : m ∈ freePositions P x)
    (hn1 : 1 < n) (hm1 : 1 < m) (hg : Nat.gcd n P = Nat.gcd m P)
    (delta : ℝ) (hd : 0 ≤ delta)
    (hgap : delta ≤ occurrenceCoefficients P x m - occurrenceCoefficients P x n) :
    delta^2 / (rationalReuseFactor P K n m : ℝ) ≤ reuseEnergy P x := by
  have hC : (0 : ℝ) < (rationalReuseFactor P K n m : ℝ) :=
    (Rat.cast_pos (K := ℝ)).2 (rationalReuseFactor_pos P K n m hP hn1 hm1)
  apply (div_le_iff₀ hC).mpr
  have hsq : delta^2 ≤
      (occurrenceCoefficients P x n - occurrenceCoefficients P x m)^2 := by
    nlinarith
  have hb := occurrence_fiber_gap_sq_le_reuse P x hP n m hn hm hg
  have hC' := mul_le_mul_of_nonneg_right
    (rationalReuseFactor_bounds_actual P K n m hP hn1 hm1) (reuseEnergy_nonneg P x)
  calc
    delta^2 ≤ _ := hsq
    _ ≤ _ := hb
    _ ≤ _ := hC'
    _ = _ := mul_comm _ _

/-- Rational coefficient separation produces a rational, certified reuse-energy lower bound. -/
theorem rational_reuse_lower_certificate (P x K i j : ℕ)
    (hP : 0 < P) (hK : 1 ≤ K) (hi : i < (freePositions P x).card)
    (hj : j < (freePositions P x).card)
    (hin : 1 < occurrenceBoundary P x i) (hjn : 1 < occurrenceBoundary P x j)
    (hg : Nat.gcd (occurrenceBoundary P x i) P = Nat.gcd (occurrenceBoundary P x j) P)
    (hsep : (rationalOccurrenceCoefficientInterval P x K i).hi ≤
      (rationalOccurrenceCoefficientInterval P x K j).lo) :
    ((((rationalOccurrenceCoefficientInterval P x K j).lo -
        (rationalOccurrenceCoefficientInterval P x K i).hi)^2 /
      rationalReuseFactor P K (occurrenceBoundary P x i) (occurrenceBoundary P x j) : ℚ) : ℝ) ≤
        reuseEnergy P x := by
  have hI := rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi
  have hJ := rationalOccurrenceCoefficientInterval_contains P x K j hP hK hj
  have hs := (Rat.cast_le (K := ℝ)).2 hsep
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub]
  apply reuseEnergy_lower_of_fiber_gap P x K _ _ hP
    (occurrenceBoundary_mem P x i hi) (occurrenceBoundary_mem P x j hj) hin hjn hg
  · linarith
  · linarith [hI.2, hJ.1]

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

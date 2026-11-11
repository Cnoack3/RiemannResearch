import RiemannResearch.Analysis.PrimeProbeMicroscopic
import RiemannResearch.Analysis.ActualRationalFMZDomination
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute FMZ budgets and microscopic probe degeneracy

Source: user-provided V_vector_space_RH.pdf, Sections 3--5 and 9.
The squared logarithmic-height budget is the explicit sufficient condition
in ActualRationalFMZRate.tendsto_moving_rational_fourier_remainder, motivated
by Ford--Meng--Zaharescu, https://arxiv.org/abs/1511.06814.
The variance/repulsion deduction below is elementary; no novelty is asserted.

For normalized nonnegative spectral weights, either the single-mode budget
or the complete budget for the Fourier expansion of |H|^2 dominates spectral
variance. If that budget is o(log T), the probe two-site determinant tends
to zero at displacement u/log T. The pair-budget theorem records the stronger
inequality 2*variance <= budget.

This is a limitation of this sufficient absolute Wiener-budget route to a
nondegenerate microscopic probe, not an impossibility theorem for FMZ,
signed cancellation, or Montgomery's conjecture. No assertion that an actual
arithmetic family satisfies the small-budget hypothesis is made, and no
Selberg-density or RH hypothesis is required for the obstruction itself.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate
variable {κ : Type*} [Fintype κ]

theorem spectralVariance_eq_secondMoment_sub (q b : κ → ℝ)
    (hb : ∑ p, b p = 1) :
    spectralVariance q b =
      (∑ p, b p * q p ^ 2) - (∑ p, b p * q p)^2 := by
  have he (p r : κ) : b p * b r * (q p - q r)^2 =
      (b p * q p ^ 2) * b r + b p * (b r * q r ^ 2) -
        ((b p * q p) * 2) * (b r * q r) := by ring
  unfold spectralVariance
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hb, mul_one, ← Finset.sum_mul, hb, one_mul]
  ring

theorem spectralVariance_le_secondMoment (q b : κ → ℝ)
    (hb : ∑ p, b p = 1) :
    spectralVariance q b ≤ ∑ p, b p * q p ^ 2 := by
  rw [spectralVariance_eq_secondMoment_sub q b hb]
  exact sub_le_self _ (sq_nonneg _)

theorem spectralVariance_nonneg (q b : κ → ℝ)
    (hb0 : ∀ p, 0 ≤ b p) (hb : ∑ p, b p = 1) :
    0 ≤ spectralVariance q b := by
  rw [spectralVariance_eq_centered q b hb]
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hb0 p) (sq_nonneg _))

/-- A second moment or any larger nonnegative budget which is small compared
with a diverging scale forces vanishing variance on the squared scale. -/
theorem variance_div_sq_tendsto_of_budget
    {α : Type*} {l : Filter α} (I : α → Type*) [∀ a, Fintype (I a)]
    (q b : ∀ a, I a → ℝ) (budget scale : α → ℝ)
    (hb0 : ∀ a p, 0 ≤ b a p) (hb : ∀ a, ∑ p, b a p = 1)
    (hbudget : ∀ a, spectralVariance (q a) (b a) ≤ budget a)
    (hscale : Tendsto scale l atTop)
    (hsmall : Tendsto (fun a => budget a / scale a) l (𝓝 0)) :
    Tendsto (fun a => spectralVariance (q a) (b a) / scale a ^ 2) l (𝓝 0) := by
  have hi : Tendsto (fun a => (scale a)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  have hlim := hsmall.mul hi
  simp only [mul_zero] at hlim
  have he (a : α) : budget a / scale a * (scale a)⁻¹ =
      budget a / scale a ^ 2 := by ring
  simp only [he] at hlim
  apply squeeze_zero (fun a => div_nonneg
    (spectralVariance_nonneg _ _ (hb0 a) (hb a)) (sq_nonneg _)) _ hlim
  intro a
  exact div_le_div_of_nonneg_right (hbudget a) (sq_nonneg _)

theorem microscopic_repulsion_tendsto_zero_of_budget
    {α : Type*} {l : Filter α} (I : α → Type*) [∀ a, Fintype (I a)]
    (q b : ∀ a, I a → ℝ) (budget scale : α → ℝ)
    (hb0 : ∀ a p, 0 ≤ b a p) (hb : ∀ a, ∑ p, b a p = 1)
    (hbudget : ∀ a, spectralVariance (q a) (b a) ≤ budget a)
    (hscale : Tendsto scale l atTop)
    (hsmall : Tendsto (fun a => budget a / scale a) l (𝓝 0)) (u : ℝ) :
    Tendsto (fun a => probeRepulsion (q a) (b a) (u / scale a)) l (𝓝 0) :=
  microscopic_repulsion_tendsto_zero I q b scale hb0 hb
    (variance_div_sq_tendsto_of_budget I q b budget scale hb0 hb hbudget hscale hsmall) u

theorem rational_frequency_sq_le_weight (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (Real.log ((n : ℝ) / (m : ℝ))) ^ 2 ≤ rationalModeWeight n m ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have ha : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hb : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  rw [Real.log_div hn0 hm0]
  unfold rationalModeWeight
  rw [abs_of_nonneg (add_nonneg ha hb)]
  nlinarith [mul_nonneg ha hb]

theorem spectralVariance_le_rational_budget (n m : κ → ℕ) (b : κ → ℝ)
    (hn : ∀ p, 1 ≤ n p) (hm : ∀ p, 1 ≤ m p)
    (hb0 : ∀ p, 0 ≤ b p) (hb : ∑ p, b p = 1) :
    spectralVariance (fun p => Real.log ((n p : ℝ) / (m p : ℝ))) b ≤
      ∑ p, b p * rationalModeWeight (n p) (m p) ^ 2 := by
  apply (spectralVariance_le_secondMoment _ b hb).trans
  exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
    (rational_frequency_sq_le_weight (n p) (m p) (hn p) (hm p)) (hb0 p))

theorem rational_budget_microscopic_repulsion_tendsto_zero
    (I : ℝ → Type*) [∀ T, Fintype (I T)] (n m : ∀ T, I T → ℕ)
    (b : ∀ T, I T → ℝ)
    (hn : ∀ T p, 1 ≤ n T p) (hm : ∀ T p, 1 ≤ m T p)
    (hb0 : ∀ T p, 0 ≤ b T p) (hb : ∀ T, ∑ p, b T p = 1)
    (hsmall : Tendsto (fun T : ℝ =>
      (∑ p, b T p * rationalModeWeight (n T p) (m T p) ^ 2) / Real.log T)
      atTop (𝓝 0)) (u : ℝ) :
    Tendsto (fun T : ℝ => probeRepulsion
      (fun p => Real.log ((n T p : ℝ) / (m T p : ℝ))) (b T) (u / Real.log T))
      atTop (𝓝 0) := by
  apply microscopic_repulsion_tendsto_zero_of_budget I
    (fun T p => Real.log ((n T p : ℝ) / (m T p : ℝ))) b
    (fun T => ∑ p, b T p * rationalModeWeight (n T p) (m T p) ^ 2)
    Real.log hb0 hb
  · exact fun T => spectralVariance_le_rational_budget (n T) (m T) (b T)
      (hn T) (hm T) (hb0 T) (hb T)
  · exact Real.tendsto_log_atTop
  · exact hsmall


/-- The exact rational frequency occurring in an off-diagonal probe pair. -/
theorem rational_frequency_sub (n m a d : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    Real.log ((n : ℝ) / (m : ℝ)) - Real.log ((a : ℝ) / (d : ℝ)) =
      Real.log (((n * d : ℕ) : ℝ) / ((m * a : ℕ) : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul]
  rw [Real.log_div hn0 hm0, Real.log_div ha0 hd0,
    Real.log_div (mul_ne_zero hn0 hd0) (mul_ne_zero hm0 ha0),
    Real.log_mul hn0 hd0, Real.log_mul hm0 ha0]
  ring

/-- The complete squared-height Wiener mass of the Fourier expansion of
|H|^2, using coefficients b_p b_r and rational modes n_p m_r/(m_p n_r). -/
def rationalPairBudget (n m : κ → ℕ) (b : κ → ℝ) : ℝ :=
  ∑ p, ∑ r, b p * b r * rationalModeWeight (n p * m r) (m p * n r) ^ 2

theorem two_mul_spectralVariance_le_rationalPairBudget
    (n m : κ → ℕ) (b : κ → ℝ)
    (hn : ∀ p, 1 ≤ n p) (hm : ∀ p, 1 ≤ m p)
    (hb0 : ∀ p, 0 ≤ b p) :
    2 * spectralVariance (fun p => Real.log ((n p : ℝ) / (m p : ℝ))) b ≤
      rationalPairBudget n m b := by
  have he : 2 * spectralVariance
      (fun p => Real.log ((n p : ℝ) / (m p : ℝ))) b =
      ∑ p, ∑ r, b p * b r *
        (Real.log ((n p : ℝ) / (m p : ℝ)) -
          Real.log ((n r : ℝ) / (m r : ℝ))) ^ 2 := by
    unfold spectralVariance
    ring
  rw [he]
  unfold rationalPairBudget
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hb0 p) (hb0 r))
  rw [rational_frequency_sub (n p) (m p) (n r) (m r) (hn p) (hm p) (hn r) (hm r)]
  exact rational_frequency_sq_le_weight (n p * m r) (m p * n r)
    (Nat.mul_pos (hn p) (hm r)) (Nat.mul_pos (hm p) (hn r))

/-- The FMZ sufficient absolute budget applied to the squared probe itself
also forces trivial microscopic repulsion. This does not rule out estimates
which retain signed cancellation beyond that sufficient budget. -/
theorem rational_pair_budget_microscopic_repulsion_tendsto_zero
    (I : ℝ → Type*) [∀ T, Fintype (I T)] (n m : ∀ T, I T → ℕ)
    (b : ∀ T, I T → ℝ)
    (hn : ∀ T p, 1 ≤ n T p) (hm : ∀ T p, 1 ≤ m T p)
    (hb0 : ∀ T p, 0 ≤ b T p) (hb : ∀ T, ∑ p, b T p = 1)
    (hsmall : Tendsto (fun T : ℝ =>
      rationalPairBudget (n T) (m T) (b T) / Real.log T) atTop (𝓝 0)) (u : ℝ) :
    Tendsto (fun T : ℝ => probeRepulsion
      (fun p => Real.log ((n T p : ℝ) / (m T p : ℝ))) (b T) (u / Real.log T))
      atTop (𝓝 0) := by
  apply microscopic_repulsion_tendsto_zero_of_budget I
    (fun T p => Real.log ((n T p : ℝ) / (m T p : ℝ))) b
    (fun T => rationalPairBudget (n T) (m T) (b T)) Real.log hb0 hb
  · intro T
    have htwo := two_mul_spectralVariance_le_rationalPairBudget
      (n T) (m T) (b T) (hn T) (hm T) (hb0 T)
    have hnonneg := spectralVariance_nonneg
      (fun p => Real.log ((n T p : ℝ) / (m T p : ℝ))) (b T) (hb0 T) (hb T)
    linarith
  · exact Real.tendsto_log_atTop
  · exact hsmall

end RiemannResearch.Analysis.MontgomeryFormFactor

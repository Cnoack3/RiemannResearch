import RiemannResearch.RH.RamanujanMeanOptimizer
import RiemannResearch.RH.ParetoArithmeticRepair

/-!
# Von Mangoldt scores in full Pareto Ramanujan orthogonalization

Source: user-provided 19 September 2026 route, "Ramanujan, orthogonal sums,
CRT, von Mangoldt, change back," and the finite inverse-Gram normal equations.
The actual Pareto mean is supplied by ParetoResidueMean. See Mathlib's
ArithmeticFunction.VonMangoldt for the underlying Mobius-log identity.

Every covariance below is the complete infinite Pareto inner product.
The old Gram inverse is constructed, and every pivot for an increasing
conductor enumeration is proved positive by a Mobius coordinate. A zero
raw von Mangoldt value is not assumed to give a zero orthogonal score.
The one-step gain does not assert exhaustion of the target norm.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanInnovation
open FiniteSchur RamanujanOptimizer
noncomputable section

/-- Full Gram solve projecting the new packet onto the old packet dictionary. -/
def fitCoefficients (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) : s → ℝ :=
  ramanujanGramSolve s hs (fun i => paretoInner (family s i) (ramanujanPacket q))

/-- The fitted component of the new packet, with the complete Pareto weights. -/
def fit (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) : ℕ → ℝ :=
  combination (family s) (fitCoefficients s hs q)

/-- Orthogonal remainder after regressing the new packet on the old ones. -/
def innovation (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) (k : ℕ) : ℝ :=
  ramanujanPacket q k - fit s hs q k

/-- Correlation of the innovation with the target constant one. -/
def score (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) : ℝ :=
  paretoMean (innovation s hs q)

/-- Actual squared innovation norm; positivity is proved below. -/
def pivot (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) : ℝ :=
  paretoInner (innovation s hs q) (innovation s hs q)

theorem fit_normal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) (i : s) :
    paretoInner (family s i) (fit s hs q) =
      paretoInner (family s i) (ramanujanPacket q) := by
  rw [fit, ← gramApply_eq_inner (family_bounded s)]
  exact congrFun (ramanujanGramSolve_normal_equations s hs
    (fun i => paretoInner (family s i) (ramanujanPacket q))) i

theorem innovation_bounded (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    ∃ C : ℝ, ∀ k, |innovation s hs q k| ≤ C := by
  exact ⟨_, bounded_sub (ramanujanPacket_abs_le q)
    (combination_bounded (family_bounded s) (fitCoefficients s hs q))⟩

theorem innovation_orthogonal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (b : s → ℝ) :
    paretoInner (innovation s hs q) (combination (family s) b) = 0 :=
  residual_orthogonal (family_bounded s) (ramanujanPacket_abs_le q)
    (fitCoefficients s hs q) (fit_normal s hs q) b

/-- The screened score retains every mixed-conductor correction. -/
theorem score_vonMangoldt (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    score s hs q = ArithmeticFunction.vonMangoldt q -
      ∑ i : s, fitCoefficients s hs q i * ArithmeticFunction.vonMangoldt i := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  unfold score innovation fit
  rw [paretoMean_sub (ramanujanPacket_abs_le q)
    (combination_bounded (family_bounded s) (fitCoefficients s hs q)),
    paretoMean_ramanujanPacket, ← paretoInner_one_right,
    inner_combination_left (family_bounded s) h1]
  simp only [paretoInner_one_right, family, paretoMean_ramanujanPacket]

/-- Scalar Schur complement of the full Gram matrix. -/
theorem pivot_schur (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    pivot s hs q = paretoInner (ramanujanPacket q) (ramanujanPacket q) -
      ∑ i : s, fitCoefficients s hs q i *
        paretoInner (family s i) (ramanujanPacket q) :=
  residual_schur_value (family_bounded s) (ramanujanPacket_abs_le q)
    (fitCoefficients s hs q) (fit_normal s hs q)

theorem innovation_mobiusDifference (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hmax : ∀ d ∈ s, d < q) :
    mobiusDifference q (innovation s hs q) = -(q : ℝ) := by
  have hfit : mobiusDifference q (fit s hs q) = 0 := by
    have hlin : mobiusDifference q (fit s hs q) =
        ∑ i : s, fitCoefficients s hs q i * mobiusDifference q (family s i) := by
      unfold fit combination mobiusDifference
      simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hlin]
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ¬ q ∣ i.val := by
      intro h
      exact (not_le_of_gt (hmax i i.property))
        (Nat.le_of_dvd (by have := hs i i.property; omega) h)
    simp [family, mobiusDifference_packet q i hq
      (by have := hs i i.property; omega), hnot]
  unfold innovation
  rw [mobiusDifference_sub_fn, hfit]
  simp [mobiusDifference_packet q q hq (by omega),
    Nat.div_self (show 0 < q by omega)]

/-- Increasing conductor order gives a positive pivot without a density assumption. -/
theorem pivot_pos (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hmax : ∀ d ∈ s, d < q) : 0 < pivot s hs q := by
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have hn : 0 ≤ pivot s hs q := paretoInner_self_nonneg _
  by_contra hpos
  have hz : pivot s hs q = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hvalues := (paretoInner_self_zero_iff_positive hC).mp hz
  have hzero : innovation s hs q = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [innovation, fit, combination, family, ramanujanPacket, residue]
    · exact hvalues k (Nat.pos_of_ne_zero hk)
  have hdual := innovation_mobiusDifference s hs q hq hmax
  rw [hzero] at hdual
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  simp [mobiusDifference] at hdual
  linarith

theorem residual_score (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    paretoInner (fun k => 1 - projection s hs k) (innovation s hs q) =
      score s hs q := by
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  change paretoInner (fun k => 1 - combination (family s) (coefficients s hs) k)
    (innovation s hs q) = _
  rw [paretoInner_sub_left h1
    (combination_bounded (family_bounded s) (coefficients s hs)) hC,
    paretoInner_one_left, paretoInner_comm (combination (family s) (coefficients s hs)),
    innovation_orthogonal, sub_zero]
  rfl

/-- Add the exact optimal scalar innovation to the old least-squares candidate. -/
def update (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) (k : ℕ) : ℝ :=
  projection s hs k + (score s hs q / pivot s hs q) * innovation s hs q k

/-- Exact one-step error reduction, retaining the complete infinite tail. -/
theorem update_error (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hmax : ∀ d ∈ s, d < q) :
    paretoError (update s hs q) =
      1 - mass s hs - (score s hs q)^2 / pivot s hs q := by
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have h := paretoInner_optimal_scalar_gain
    (r := fun k => 1 - projection s hs k) (g := innovation s hs q)
    (bounded_sub h1 (combination_bounded (family_bounded s) (coefficients s hs)))
    hC (ne_of_gt (pivot_pos s hs q hq hmax)) (score s hs q / pivot s hs q)
  rw [residual_score] at h
  change paretoInner
    (fun k => (1 - projection s hs k) - (score s hs q / pivot s hs q) * innovation s hs q k)
    (fun k => (1 - projection s hs k) - (score s hs q / pivot s hs q) * innovation s hs q k) =
      paretoError (projection s hs) - (score s hs q)^2 / pivot s hs q +
        pivot s hs q * (score s hs q / pivot s hs q - score s hs q / pivot s hs q)^2 at h
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    projection_error] at h
  simpa only [paretoError, update, sub_add_eq_sub_sub] using h


/-- Each exact gain is bounded by the remaining full Pareto error. -/
theorem gain_le_error (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hmax : ∀ d ∈ s, d < q) :
    (score s hs q)^2 / pivot s hs q ≤ 1 - mass s hs := by
  have h : 0 ≤ paretoError (update s hs q) := paretoInner_self_nonneg _
  rw [update_error s hs q hq hmax] at h
  linarith

/-- Allowed new conductors preserve the actual algebraic two-seed span. -/
theorem update_legal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (ha : ∀ d ∈ s, 2 ∣ d ∨ 3 ∣ d) (q : ℕ) (hq : 0 < q)
    (hqa : 2 ∣ q ∨ 3 ∣ q) :
    update s hs q ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  have hfit := combination_legal s hs ha (fitCoefficients s hs q)
  have hin : innovation s hs q ∈ legalSeedSpan ({2, 3} : Set ℕ) :=
    (legalSeedSpan ({2, 3} : Set ℕ)).sub_mem
      (ramanujanPacket_twoSeed_mem q hq hqa) hfit
  exact (legalSeedSpan ({2, 3} : Set ℕ)).add_mem
    (combination_legal s hs ha (coefficients s hs))
    ((legalSeedSpan ({2, 3} : Set ℕ)).smul_mem _ hin)

end
end RiemannResearch.RH.Pareto.RamanujanInnovation

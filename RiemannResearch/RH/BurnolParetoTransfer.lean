import RiemannResearch.RH.BaezDuarteNaturalApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
/-!
# Cutoff-preserving continuous-to-Pareto lower-bound transfer

Source: J.-F. Burnol, A lower bound in an approximation problem involving
the zeros of the Riemann zeta function, Advances in Mathematics 170 (2002),
56--70, Theorem 1.3; https://arxiv.org/pdf/math/0103058.
The source supports the external analytic input. Its proof is not formalized
here. The finite-function transfer uses the repository's exact centered
norm identity and complete-domain conductor-one correction, with no loss
of cutoff and no multiplicative error constant.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RiemannResearch.RH.Pareto.BurnolTransfer
open CoefficientStabilization BaezDuarte

/-- The finite-function conclusion furnished by Burnol at cutoff N.
This proposition is an explicit analytic input, not an asserted theorem. -/
def ContinuousCutoffLowerBound (N L : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (a θ : ℕ → ℝ),
    (∀ i ∈ s, 1 / N ≤ θ i ∧ θ i ≤ 1) →
    ENNReal.ofReal L ≤
      ∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal ((chi x - ∑ i ∈ s, a i * Int.fract (θ i / x)) ^ 2)

theorem naturalError_lower (N : ℕ) (L : ℝ)
    (h : ContinuousCutoffLowerBound N L)
    (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    ENNReal.ofReal L ≤ naturalError s a := by
  have hh := h s a (fun d => 1 / (d : ℝ)) (by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hs d hd).1
    have hdN : (d : ℝ) ≤ N := by exact_mod_cast (hs d hd).2
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (hs d hd).1
    constructor
    · exact one_div_le_one_div_of_le hd0 hdN
    · exact (div_le_one hd0).mpr hd1)
  simpa only [naturalError, naturalSum, one_div, div_eq_mul_inv, mul_inv_rev,
    mul_comm, mul_left_comm, mul_assoc] using hh

theorem finiteResidueSum_projection (n : ℕ) :
    finiteResidueSum ((Finset.range n).image (fun i => i + 2))
      (fun d => coefficient n d) = projection n := by
  classical
  rw [projection_expansion]
  unfold finiteResidueSum
  rw [Finset.sum_image]
  · apply Finset.sum_bij (fun i hi => (⟨i, Finset.mem_range.mp hi⟩ : Fin n))
    · intro i hi
      simp
    · intro i hi j hj he
      exact Fin.mk.inj he
    · intro j hj
      exact ⟨j.val, Finset.mem_range.mpr j.isLt, rfl⟩
    · intro i hi
      simp [residueVector, residueAtom]
  · intro i hi j hj hij
    dsimp only at hij
    omega

/-- Cutoff-preserving transfer, with exact squared-error normalization. -/
theorem energy_lower_of_continuous (n : ℕ) (L : ℝ)
    (h : ContinuousCutoffLowerBound (n + 1 : ℕ) L) :
    L ≤ energy n := by
  let s := (Finset.range n).image (fun i => i + 2)
  let a : ℕ → ℝ := fun d => coefficient n d
  have hs : ∀ d ∈ s, 0 < d ∧ d ≤ n + 1 := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have hi' := Finset.mem_range.mp hi
    omega
  have hs' : ∀ d ∈ insert 1 s, 0 < d ∧ d ≤ n + 1 := by
    intro d hd
    rcases Finset.mem_insert.mp hd with h1 | hd
    · subst d
      omega
    · exact hs d hd
  have hh := naturalError_lower (n+1) L h
    (insert 1 s) (correctedCoefficient s a) hs'
  rw [corrected_naturalError_eq s a (fun d hd => (hs d hd).1),
    centeredError_eq_hilbert_norm_sq s a (fun d hd => (hs d hd).1)] at hh
  have he : finiteResidueSum s a = projection n := finiteResidueSum_projection n
  rw [he] at hh
  have hn : 0 ≤ energy n := sq_nonneg _
  change ENNReal.ofReal L ≤ ENNReal.ofReal (energy n) at hh
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp hh

/-- The only remaining input is the published analytic lower envelope;
the passage to the repository's actual optimizer is proved. -/
theorem energy_log_envelope (c : ℝ) (K : ℕ)
    (h : ∀ N : ℕ, K ≤ N → 2 ≤ N →
      ContinuousCutoffLowerBound N (c / Real.log N)) :
    ∀ n : ℕ, K ≤ n + 1 → 2 ≤ n + 1 →
      c / Real.log (n + 1 : ℕ) ≤ energy n := by
  intro n hn hn2
  exact energy_lower_of_continuous n _ (h (n+1) hn hn2)
/-- Every finite legal candidate inherits the continuous cutoff bound.
The analytic lower bound is an explicit input; no estimate for it is asserted. -/
theorem finite_error_lower_of_continuous (N : ℕ) (hN : 1 ≤ N) (L : ℝ)
    (h : ContinuousCutoffLowerBound N L) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    L ≤ ‖hilbertOne - finiteResidueSum s a‖ ^ 2 := by
  have hs' : ∀ d ∈ insert 1 s, 0 < d ∧ d ≤ N := by
    intro d hd
    rcases Finset.mem_insert.mp hd with hd | hd
    · subst d
      exact ⟨Nat.zero_lt_one, hN⟩
    · exact hs d hd
  have hh := naturalError_lower N L h (insert 1 s) (correctedCoefficient s a) hs'
  rw [corrected_naturalError_eq s a (fun d hd => (hs d hd).1),
    centeredError_eq_hilbert_norm_sq s a (fun d hd => (hs d hd).1)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hh
end RiemannResearch.RH.Pareto.BurnolTransfer

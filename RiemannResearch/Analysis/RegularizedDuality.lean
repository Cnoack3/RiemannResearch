import RiemannResearch.Analysis.RegularizedDataGeometry
import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rank-free duality for finite penalized approximation

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The observation multiplier is constructed for arbitrary dependent rows.
The complete primal/dual gap consists of two squares. It proves strong
duality, a representer formula, and uniqueness of the dual optimizer even
at zero penalty and without independence of the observation functionals.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.RegularizedDuality
open FiniteHilbertGram FiniteRegularizedConstraints RegularizedDataGeometry
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def multiplier {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (j : κ) : ℝ :=
  ρ * (t j - observe B (coefficients hv B f t ρ) j)

/-- The dual value includes the complete signed source term and full source Gram. -/
def dualValue {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) : ℝ :=
  ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 +
    2 * ρ * (∑ j, z j * (t j - observe B (inverseCoeff hv f) j)) -
    ρ ^ 2 * ‖Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z‖ ^ 2 -
    ∑ j, (z j) ^ 2

theorem row_synthesis_pairing {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (z : κ → ℝ) (c : ι → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z)
      (Fintype.linearCombination ℝ v c) = ∑ j, z j * observe B c j := by
  rw [inner_synthesis_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteGramMultipleConstraint.sourceRows_pairing hv B c j]
  rfl

/-- Exact global primal/dual certificate for every primal and dual trial. -/
theorem primal_dual_gap {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ)
    (a : ι → ℝ) (z : κ → ℝ) :
    objective v B f t ρ a - dualValue hv B f t ρ z =
      ‖Fintype.linearCombination ℝ v (a - inverseCoeff hv f) -
        ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z‖ ^ 2 +
      ∑ j, (ρ * (observe B a j - t j) + z j) ^ 2 := by
  have hp : inner ℝ (Fintype.linearCombination ℝ v (a - inverseCoeff hv f))
      (Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z) =
      (∑ j, z j * (observe B a j - t j)) +
        ∑ j, z j * (t j - observe B (inverseCoeff hv f) j) := by
    rw [real_inner_comm, row_synthesis_pairing hv B z (a - inverseCoeff hv f),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [observe_sub]
    ring
  have hs : (∑ j, (ρ * (observe B a j - t j) + z j) ^ 2) =
      ρ ^ 2 * mismatchEnergy B t a +
        2 * ρ * (∑ j, z j * (observe B a j - t j)) + ∑ j, (z j) ^ 2 := by
    unfold mismatchEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hn : ‖ρ • Fintype.linearCombination ℝ
      (FiniteGramMultipleConstraint.sourceRows hv B) z‖ ^ 2 =
      ρ ^ 2 * ‖Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [objective, residual_completion hv f a, dualValue,
    norm_sub_sq_real (Fintype.linearCombination ℝ v (a - inverseCoeff hv f))
      (ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z),
    inner_smul_right, hp, hn, hs]
  ring

theorem weak_duality {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ)
    (a : ι → ℝ) (z : κ → ℝ) :
    dualValue hv B f t ρ z ≤ objective v B f t ρ a := by
  have h := primal_dual_gap hv B f t ρ a z
  have hsq := sq_nonneg ‖Fintype.linearCombination ℝ v (a - inverseCoeff hv f) -
    ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B) z‖
  have hsum := Finset.sum_nonneg (s := Finset.univ)
    (fun j _ => sq_nonneg (ρ * (observe B a j - t j) + z j))
  linarith only [h, hsq, hsum]

/-- The physical correction is exactly the observation representer synthesis. -/
theorem representer {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    Fintype.linearCombination ℝ v (coefficients hv B f t ρ - inverseCoeff hv f) =
      ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
        (multiplier hv B f t ρ) := by
  let d := coefficients hv B f t ρ - inverseCoeff hv f -
    ρ • FiniteGramMultipleConstraint.rowLift hv B (multiplier hv B f t ρ)
  have hr := residual_orthogonal hv f d
  have hs := normal_pairing hv B f t ρ d
  have hl : inner ℝ
      (ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
        (multiplier hv B f t ρ)) (Fintype.linearCombination ℝ v d) =
      -(ρ ^ 2 * ∑ j, (observe B (coefficients hv B f t ρ) j - t j) * observe B d j) := by
    rw [real_inner_smul_left, row_synthesis_pairing hv B (multiplier hv B f t ρ) d,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold multiplier
    ring
  have hd : Fintype.linearCombination ℝ v d =
      (f - Fintype.linearCombination ℝ v (inverseCoeff hv f)) -
      (f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ)) -
      ρ • Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
        (multiplier hv B f t ρ) := by
    dsimp only [d]
    rw [map_sub, map_sub, map_smul, FiniteGramMultipleConstraint.rowLift_synthesis hv B (multiplier hv B f t ρ)]
    abel
  have hz : ‖Fintype.linearCombination ℝ v d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => lhs; rw [hd]
    rw [inner_sub_left, inner_sub_left, hr, hs, hl]
    ring
  have he : Fintype.linearCombination ℝ v d = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  dsimp only [d] at he
  rw [map_sub, map_smul, FiniteGramMultipleConstraint.rowLift_synthesis hv B (multiplier hv B f t ρ)] at he
  exact sub_eq_zero.mp he

/-- The observation-space equation has identity plus the complete source Gram,
so it remains well posed when the source rows are dependent. -/
theorem multiplier_normal {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (j : κ) :
    multiplier hv B f t ρ j + ρ ^ 2 *
      inner ℝ (FiniteGramMultipleConstraint.sourceRows hv B j)
        (Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
          (multiplier hv B f t ρ)) =
      ρ * (t j - observe B (inverseCoeff hv f) j) := by
  have h := congrArg (fun x => inner ℝ (FiniteGramMultipleConstraint.sourceRows hv B j) x)
    (representer hv B f t ρ)
  rw [FiniteGramMultipleConstraint.sourceRows_pairing hv B
    (coefficients hv B f t ρ - inverseCoeff hv f) j, inner_smul_right] at h
  change observe B (coefficients hv B f t ρ - inverseCoeff hv f) j = _ at h
  rw [observe_sub] at h
  have hm := congrArg (fun x : ℝ => ρ * x) h
  change ρ * (t j - observe B (coefficients hv B f t ρ) j) + ρ ^ 2 * _ = _
  nlinarith only [hm]

/-- The actual multiplier attains the primal minimum, with no rank or nonzero-penalty hypothesis. -/
theorem strong_duality {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    objective v B f t ρ (coefficients hv B f t ρ) =
      dualValue hv B f t ρ (multiplier hv B f t ρ) := by
  have h := primal_dual_gap hv B f t ρ (coefficients hv B f t ρ) (multiplier hv B f t ρ)
  rw [representer hv B f t ρ, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  have hz : (∑ j, (ρ * (observe B (coefficients hv B f t ρ) j - t j) +
      multiplier hv B f t ρ j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [multiplier]
    ring
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- The whole dual deficit is the Euclidean multiplier error plus the full source-Gram error. -/
theorem dual_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) :
    dualValue hv B f t ρ (multiplier hv B f t ρ) - dualValue hv B f t ρ z =
      ρ ^ 2 * ‖Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
        (multiplier hv B f t ρ - z)‖ ^ 2 +
      ∑ j, (z j - multiplier hv B f t ρ j) ^ 2 := by
  rw [← strong_duality hv B f t ρ, primal_dual_gap hv B f t ρ,
    representer hv B f t ρ, ← smul_sub, ← map_sub, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold multiplier
  ring

theorem dual_maximizer_unique {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (z : κ → ℝ) :
    dualValue hv B f t ρ z = dualValue hv B f t ρ (multiplier hv B f t ρ) ↔
      z = multiplier hv B f t ρ := by
  constructor
  · intro he
    have h := dual_completion hv B f t ρ z
    rw [he, sub_self] at h
    have hp := mul_nonneg (sq_nonneg ρ)
      (sq_nonneg ‖Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
        (multiplier hv B f t ρ - z)‖)
    have hs := Finset.sum_nonneg (s := Finset.univ)
      (fun j _ => sq_nonneg (z j - multiplier hv B f t ρ j))
    have hz : (∑ j, (z j - multiplier hv B f t ρ j) ^ 2) = 0 := by linarith only [h, hp, hs]
    funext j
    have hj : (z j - multiplier hv B f t ρ j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
        (z k - multiplier hv B f t ρ k))).mp hz j (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hj)
  · intro he
    rw [he]

end RiemannResearch.Analysis.RegularizedDuality

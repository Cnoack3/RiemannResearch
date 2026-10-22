import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.Tactic.Ring

/-!
# Marked spectral mass and exact residual gains

Source: user-provided argument,
`RH_Controlled_Conductor_Schur_2026-09-10.md`, Sections 4 and 7.

The finite comparison retains every nonnegative spectral contribution. The
all-scale consumer is conditional: the spectral representation and marked
mass bounds must concern the actual residual, and nonsummability of the
marked lower bound is an explicit hypothesis. No arithmetic provider for
that hypothesis, and no proof of RH, is supplied here.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ResidualGain

/-- A marked set of eigenmodes with eigenvalue at least `α` supplies its exact
normalized mass times the contraction factor `α / (1 + α)` as a lower bound.
Here `m i` is the squared residual coefficient on the corresponding mode. -/
theorem marked_spectral_mass_lower_bound {ι : Type*} [Fintype ι]
    (s : Finset ι) (lam m : ι → ℝ) {E α θ : ℝ}
    (hE : 0 < E) (hα : 0 ≤ α)
    (hlam : ∀ i, 0 ≤ lam i) (hm : ∀ i, 0 ≤ m i)
    (hmarked : ∀ i ∈ s, α ≤ lam i)
    (hmass : θ * E ≤ ∑ i ∈ s, m i) :
    θ * α / (1 + α) ≤ (∑ i, lam i / (1 + lam i) * m i) / E := by
  classical
  have hαden : 0 < 1 + α := by linarith
  have hlamden (i : ι) : 0 < 1 + lam i := by linarith [hlam i]
  have hαfrac : 0 ≤ α / (1 + α) := div_nonneg hα hαden.le
  have hcompare (i : ι) (hi : i ∈ s) :
      α / (1 + α) ≤ lam i / (1 + lam i) := by
    apply (div_le_div_iff₀ hαden (hlamden i)).mpr
    nlinarith [hmarked i hi]
  have hterm (i : ι) : 0 ≤ lam i / (1 + lam i) * m i :=
    mul_nonneg (div_nonneg (hlam i) (hlamden i).le) (hm i)
  apply (le_div_iff₀ hE).mpr
  calc
    θ * α / (1 + α) * E = (α / (1 + α)) * (θ * E) := by ring
    _ ≤ (α / (1 + α)) * (∑ i ∈ s, m i) :=
      mul_le_mul_of_nonneg_left hmass hαfrac
    _ = ∑ i ∈ s, (α / (1 + α)) * m i := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, lam i / (1 + lam i) * m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hcompare i hi) (hm i)
    _ ≤ ∑ i, lam i / (1 + lam i) * m i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => hterm i)

/-- The finite contraction bound in Section 4.4, obtained from an exact
spectral update and the marked residual mass. -/
theorem marked_spectral_residual_upper_bound {ι : Type*} [Fintype ι]
    (s : Finset ι) (lam m : ι → ℝ) {E Enew α θ : ℝ}
    (hE : 0 < E) (hα : 0 ≤ α)
    (hlam : ∀ i, 0 ≤ lam i) (hm : ∀ i, 0 ≤ m i)
    (hmarked : ∀ i ∈ s, α ≤ lam i)
    (hmass : θ * E ≤ ∑ i ∈ s, m i)
    (hupdate : Enew = E - ∑ i, lam i / (1 + lam i) * m i) :
    Enew ≤ E * (1 - θ * α / (1 + α)) := by
  have hgain := (le_div_iff₀ hE).mp
    (marked_spectral_mass_lower_bound s lam m hE hα hlam hm hmarked hmass)
  rw [hupdate]
  nlinarith

/-- The precise sufficient condition from Section 7.4. Dimensions and marked
sets may change at every stage. The arithmetic nonsummability input remains
an explicit hypothesis; the theorem supplies its scalar analytic consequence. -/
theorem residual_tendsto_zero_of_marked_spectral_mass
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {d r α θ : ℕ → ℝ} (s : (n : ℕ) → Finset (ι n))
    (lam m : (n : ℕ) → ι n → ℝ)
    (hd : 0 < d 0) (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (hα : ∀ n, 0 ≤ α n) (hθ : ∀ n, 0 ≤ θ n)
    (hlam : ∀ n i, 0 ≤ lam n i) (hm : ∀ n i, 0 ≤ m n i)
    (hspectral : ∀ n, r n =
      (∑ i, lam n i / (1 + lam n i) * m n i) / d n)
    (hmarked : ∀ n i, i ∈ s n → α n ≤ lam n i)
    (hmass : ∀ n, θ n * d n ≤ ∑ i ∈ s n, m n i)
    (hdiv : ¬Summable (fun n => θ n * α n / (1 + α n))) :
    Tendsto d atTop (𝓝 0) := by
  have hdpos (n : ℕ) : 0 < d n := recurrence_pos hd h1 hrec n
  have h0 (n : ℕ) : 0 ≤ r n := by
    rw [hspectral n]
    apply div_nonneg _ (hdpos n).le
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg
      (div_nonneg (hlam n i) (by linarith [hlam n i])) (hm n i)
  have hlower (n : ℕ) : θ n * α n / (1 + α n) ≤ r n := by
    rw [hspectral n]
    exact marked_spectral_mass_lower_bound (s n) (lam n) (m n)
      (hdpos n) (hα n) (hlam n) (hm n) (hmarked n) (hmass n)
  have hnonsummable : ¬Summable r := by
    intro hs
    apply hdiv
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg (mul_nonneg (hθ n) (hα n))
        (by linarith [hα n])) hlower hs
  exact (residual_tendsto_zero_iff_not_summable hd h0 h1 hrec).mpr hnonsummable

end RiemannResearch.Analysis.ResidualGain

import Mathlib.Topology.Instances.Real.Lemmas
import RiemannResearch.LinearAlgebra.SourceSpectralMass
import Mathlib.Topology.Algebra.Order.Field

/-!
# Persistent source mass forces divergent inverse spectral energy

Source: user-provided stringent not-RH conditions, 2026-09-21, group 20.
This module proves finite-source and limit theorems on the actual spectral
sum definitions. The hypotheses are positive eigenvalues, nonnegative source
weights, positive limiting projection error, and vanishing polarization.
Identification of a concrete arithmetic compression with those limit
hypotheses is a separate research obligation; no RH assumption is concealed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.LinearAlgebra.SpectralCutoff

variable {ι : Type*}

/-- Full inverse first moment. Strictly positive eigenvalues must be supplied
when using it, so zero eigenvalues are never interpreted as harmless inverses. -/
def inverseSourceMoment (s : Finset ι) (lam mass : ι → ℝ) : ℝ :=
  ∑ i ∈ s, mass i / lam i

/-- Every unit of mass below the cutoff costs at least the reciprocal cutoff
in full interpolation energy. The complete inverse sum is retained. -/
theorem omittedMass_le_scaled_inverseSourceMoment
    (s : Finset ι) {τ : ℝ} (hτ : 0 < τ) (lam mass : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 < lam i) (hmass : ∀ i ∈ s, 0 ≤ mass i) :
    omittedMass s τ lam mass ≤ τ * inverseSourceMoment s lam mass := by
  unfold omittedMass inverseSourceMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  unfold omittedTerm
  split_ifs with h
  · exact mul_nonneg hτ.le (div_nonneg (hmass i hi) (hlam i hi).le)
  · have hlt : lam i < τ := lt_of_not_ge h
    have hmul := mul_le_mul_of_nonneg_right hlt.le
      (div_nonneg (hmass i hi) (hlam i hi).le)
    have he : lam i * (mass i / lam i) = mass i := by
      field_simp [(hlam i hi).ne']
    rwa [he] at hmul

/-- Exact fixed-cutoff limit: the omitted source mass converges to the same
positive defect even while spectral leakage tends to zero. -/
theorem omittedMass_tendsto_defect
    (s : ℕ → Finset ι) (lam mass : ℕ → ι → ℝ) {E τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hlam0 : ∀ N i, i ∈ s N → 0 ≤ lam N i)
    (hlam1 : ∀ N i, i ∈ s N → lam N i ≤ 1)
    (hmass : ∀ N i, i ∈ s N → 0 ≤ mass N i)
    (herr : Tendsto (fun N => optimalError (s N) (lam N) (mass N)) atTop (𝓝 E))
    (hpolar : Tendsto (fun N => polarization (s N) (lam N) (mass N)) atTop (𝓝 0)) :
    Tendsto (fun N => omittedMass (s N) τ (lam N) (mass N)) atTop (𝓝 E) := by
  have hlo := herr.sub (hpolar.div_const τ)
  have hhi := herr.add (hpolar.div_const (1 - τ))
  simp only [zero_div, sub_zero, add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro N
    exact (omittedMass_bounds (s N) (lam N) (mass N) hτ hτ1
      (hlam0 N) (hlam1 N) (hmass N)).1
  · intro N
    exact (omittedMass_bounds (s N) (lam N) (mass N) hτ hτ1
      (hlam0 N) (hlam1 N) (hmass N)).2

/-- A positive limiting defect and vanishing leakage force full inverse
source energy to diverge. Small leakage alone cannot certify bounded cost. -/
theorem inverseSourceMoment_tendsto_atTop_of_positive_defect
    (s : ℕ → Finset ι) (lam mass : ℕ → ι → ℝ) {E : ℝ} (hE : 0 < E)
    (hlam : ∀ N i, i ∈ s N → 0 < lam N i)
    (hlam1 : ∀ N i, i ∈ s N → lam N i ≤ 1)
    (hmass : ∀ N i, i ∈ s N → 0 ≤ mass N i)
    (herr : Tendsto (fun N => optimalError (s N) (lam N) (mass N)) atTop (𝓝 E))
    (hpolar : Tendsto (fun N => polarization (s N) (lam N) (mass N)) atTop (𝓝 0)) :
    Tendsto (fun N => inverseSourceMoment (s N) (lam N) (mass N)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let τ : ℝ := min (1 / 2) (E / (2 * (|B| + 1)))
  have hden : 0 < 2 * (|B| + 1) := by positivity
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hE hden)
  have hτ1 : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτbound : τ * (2 * (|B| + 1)) ≤ E :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hB : τ * B ≤ E / 2 := by
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self B) hτ.le
    nlinarith
  have hlim := omittedMass_tendsto_defect s lam mass hτ hτ1
    (fun N i hi => (hlam N i hi).le) hlam1 hmass herr hpolar
  have hev : ∀ᶠ N in atTop, E / 2 < omittedMass (s N) τ (lam N) (mass N) :=
    hlim.eventually (lt_mem_nhds (by linarith : E / 2 < E))
  filter_upwards [hev] with N hN
  have hcost := omittedMass_le_scaled_inverseSourceMoment
    (s N) hτ (lam N) (mass N) (hlam N) (hmass N)
  have hstrict : τ * B < τ * inverseSourceMoment (s N) (lam N) (mass N) :=
    lt_of_le_of_lt hB (lt_of_lt_of_le hN hcost)
  exact (lt_of_mul_lt_mul_left hstrict hτ.le).le

end RiemannResearch.LinearAlgebra.SpectralCutoff

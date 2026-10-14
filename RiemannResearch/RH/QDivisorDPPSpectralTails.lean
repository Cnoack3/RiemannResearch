/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QDivisorDPPArithmeticWindows
import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalCardinality
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Exact spectral laws, Parseval tails, and Q-DPP cardinality

Source: user-provided moving-window analysis, Sections 1, 2, and 4.
The auxiliary law is defined by the actual complete-basis coordinates.
Its cumulative distribution is the occupation kernel diagonal. This does
not construct an infinite independent-prime law or a coupling of DPP stages.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert QDivisorHilbert ZetaTwoProbability
open RiemannResearch.Probability.DPP
def basisEnumeration : ℕ ≃ ℕ+ :=
  Equiv.ofBijective basisIndex ⟨basisIndex_injective, basisIndex_surjective⟩
theorem basisFeatures_summable (i j : ℕ) :
    Summable (fun r : ℕ =>
      normalizedDivisorWavelet (basisIndex r) i * normalizedDivisorWavelet (basisIndex r) j) := by
  have hc (r : ℕ+) (k : ℕ) :
      inner ℝ (countingBasis k) (divisorHilbertBasis r) = normalizedDivisorWavelet r k := by
    simp [countingBasis, lp.inner_single_left]
  have hd (r : ℕ+) (k : ℕ) :
      inner ℝ (divisorHilbertBasis r) (countingBasis k) = normalizedDivisorWavelet r k := by
    rw [real_inner_comm]
    exact hc r k
  simpa only [hc, hd, Function.comp_def] using
    (divisorHilbertBasis.summable_inner_mul_inner
      (countingBasis i) (countingBasis j)).comp_injective basisIndex_injective
theorem basisFeatures_tsum (i j : ℕ) :
    (∑' r : ℕ, normalizedDivisorWavelet (basisIndex r) i *
      normalizedDivisorWavelet (basisIndex r) j) = if i = j then 1 else 0 := by
  have hc (r : ℕ+) (k : ℕ) :
      inner ℝ (countingBasis k) (divisorHilbertBasis r) = normalizedDivisorWavelet r k := by
    simp [countingBasis, lp.inner_single_left]
  have hd (r : ℕ+) (k : ℕ) :
      inner ℝ (divisorHilbertBasis r) (countingBasis k) = normalizedDivisorWavelet r k := by
    rw [real_inner_comm]
    exact hc r k
  have h := divisorHilbertBasis.tsum_inner_mul_inner (countingBasis i) (countingBasis j)
  simp only [hc, hd, countingBasis_inner] at h
  have hen (r : ℕ) : basisEnumeration r = basisIndex r := rfl
  simpa only [hen] using
    (basisEnumeration.tsum_eq (fun r : ℕ+ => normalizedDivisorWavelet r i *
      normalizedDivisorWavelet r j)).trans h
theorem basisKernel_eq_range_sum (N i j : ℕ) :
    basisKernel N i j = ∑ r ∈ Finset.range N,
      normalizedDivisorWavelet (basisIndex r) i * normalizedDivisorWavelet (basisIndex r) j := by
  rw [basisKernel_eq_sum]
  exact Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    normalizedDivisorWavelet (basisIndex r) i * normalizedDivisorWavelet (basisIndex r) j) N
theorem basisKernel_exact_tail (N i j : ℕ) :
    (if i = j then (1 : ℝ) else 0) - basisKernel N i j =
      ∑' r : ℕ, normalizedDivisorWavelet (basisIndex (r+N)) i *
        normalizedDivisorWavelet (basisIndex (r+N)) j := by
  have h := (basisFeatures_summable i j).sum_add_tsum_nat_add N
  rw [basisFeatures_tsum, ← basisKernel_eq_range_sum] at h
  linarith
theorem basisKernel_diagonal_summable (N : ℕ) : Summable (fun i => basisKernel N i i) := by
  have hs (r : Fin N) (_ : r ∈ Finset.univ) :
      Summable (fun i => normalizedDivisorWavelet (basisIndex r) i ^ 2) :=
    qCoordinate_square_summable _
  have he (i : ℕ) : basisKernel N i i =
      ∑ r : Fin N, normalizedDivisorWavelet (basisIndex r) i ^ 2 := by
    simp only [basisKernel_eq_sum, pow_two]
  simpa only [he] using (summable_sum hs)
theorem basisKernel_hole_cauchy (N i j : ℕ) (hij : i ≠ j) :
    basisKernel N i j ^ 2 ≤ (1 - basisKernel N i i) * (1 - basisKernel N j j) := by
  let u := countingBasis i - (basisSpace N).starProjection (countingBasis i)
  let v := countingBasis j - (basisSpace N).starProjection (countingBasis j)
  have h := inner_mul_inner_self_le (𝕜 := ℝ) u v
  have he : inner ℝ u v = -basisKernel N i j := by
    have ht := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
      (basisSpace N) countingBasis i j
    simpa [RiemannResearch.Analysis.ProjectionDPP.holeKernel, u, v,
      countingBasis_inner, hij, basisKernel] using ht
  have hc : inner ℝ v u = inner ℝ u v := real_inner_comm _ _
  rw [hc, he] at h
  simpa [Real.norm_eq_abs, ← pow_two, real_inner_self_eq_norm_sq,
    ← basisKernel_vacancy_energy, u, v] using h

def spectralMass (i r : ℕ) : ℝ := normalizedDivisorWavelet (basisIndex r) i ^ 2
theorem spectralMass_nonneg (i r : ℕ) : 0 ≤ spectralMass i r := sq_nonneg _
theorem spectralMass_summable (i : ℕ) : Summable (spectralMass i) := by
  change Summable (fun r : ℕ => normalizedDivisorWavelet (basisIndex r) i ^ 2)
  simpa only [pow_two] using basisFeatures_summable i i
theorem spectralMass_tsum (i : ℕ) : (∑' r, spectralMass i r) = 1 := by
  change (∑' r : ℕ, normalizedDivisorWavelet (basisIndex r) i ^ 2) = 1
  simpa [pow_two] using basisFeatures_tsum i i
theorem spectralMass_ennreal_tsum (i : ℕ) :
    (∑' r, ENNReal.ofReal (spectralMass i r)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (spectralMass_nonneg i) (spectralMass_summable i),
    spectralMass_tsum]
  norm_num
def spectralLaw (i : ℕ) : PMF ℕ :=
  PMF.normalize (fun r => ENNReal.ofReal (spectralMass i r))
    (by rw [spectralMass_ennreal_tsum]; exact one_ne_zero)
    (by rw [spectralMass_ennreal_tsum]; exact ENNReal.one_ne_top)
theorem spectralLaw_apply (i r : ℕ) :
    spectralLaw i r = ENNReal.ofReal (spectralMass i r) := by
  simp [spectralLaw, PMF.normalize_apply, spectralMass_ennreal_tsum]

theorem basisKernel_trace (N : ℕ) : (∑' i, basisKernel N i i) = N := by
  have he (i : ℕ) : basisKernel N i i =
      ∑ r : Fin N, normalizedDivisorWavelet (basisIndex r) i ^ 2 := by
    simp only [basisKernel_eq_sum, pow_two]
  have hn (r : Fin N) : (∑' i, normalizedDivisorWavelet (basisIndex r) i ^ 2) = 1 := by
    rw [← qNorm_sq, ← real_inner_self_eq_norm_sq]
    simpa using (orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal)
      (basisIndex r) (basisIndex r)
  calc
    (∑' i, basisKernel N i i) =
        ∑' i, ∑ r : Fin N, normalizedDivisorWavelet (basisIndex r) i ^ 2 :=
      tsum_congr he
    _ = ∑ r : Fin N, ∑' i, normalizedDivisorWavelet (basisIndex r) i ^ 2 :=
      Summable.tsum_finsetSum (s := (Finset.univ : Finset (Fin N)))
        (fun r _ => qCoordinate_square_summable (normalizedDivisorWavelet (basisIndex r)))
    _ = N := by simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
theorem basisLaw_cardinality (N : ℕ) :
    ∀ᵐ x ∂basisLaw N, setCount {i | x i = true} = N := by
  exact (basisLaw_isDPP N).setCount_eq_ae_of_rank_trace N
    (fun e => basisKernel_principal_det_eq_zero N (N+1) e (Nat.lt_succ_self N))
    (basisKernel_diagonal_summable N) (basisKernel_trace N)
theorem spectralLaw_cdf (N i : ℕ) :
    (spectralLaw i).toMeasure.real {r | r < N} = basisKernel N i i := by
  let e : Fin N ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have he : Set.range e = {r | r < N} := by
    ext r
    constructor
    · rintro ⟨a, rfl⟩
      exact a.isLt
    · intro hr
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← he, pmf_mass_range, basisKernel_eq_sum]
  apply Finset.sum_congr rfl
  intro r _
  change (spectralLaw i (r : ℕ)).toReal =
    normalizedDivisorWavelet (basisIndex r) i * normalizedDivisorWavelet (basisIndex r) i
  rw [spectralLaw_apply, ENNReal.toReal_ofReal (spectralMass_nonneg i r)]
  exact pow_two _
theorem spectralLaw_tail (N i : ℕ) :
    (spectralLaw i).toMeasure.real {r | N ≤ r} = 1 - basisKernel N i i := by
  have he : {r : ℕ | N ≤ r} = {r : ℕ | r < N}ᶜ := by ext r; simp
  rw [he, probReal_compl_eq_one_sub ((Set.to_countable _).measurableSet), spectralLaw_cdf]
/-- The auxiliary law uses the actual arithmetic wavelet masses. -/
theorem spectralMass_arithmetic (i r : ℕ) :
    spectralMass i r = qWeight i *
      qDivisorWavelet (basisIndex r : ℕ) (i + 1)^2 / qJordanTwo (basisIndex r : ℕ) := by
  unfold spectralMass
  rw [normalizedDivisorWavelet_coordinate]
  simp only [mul_pow, inv_pow, Real.sq_sqrt (qWeight_pos i).le,
    Real.sq_sqrt (qJordanTwo_pos _ (basisIndex r).pos).le, div_eq_mul_inv]
  ring

end RiemannResearch.RH.QDivisorDPP

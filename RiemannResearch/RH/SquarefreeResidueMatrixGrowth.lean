import RiemannResearch.RH.SquarefreeResidueMatrix
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.MatrixMaximalRayleigh
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Unbounded finite-section growth and an infinite-column domain obstruction

Source: user-directed Hilbert--Polya investigation, 14 October 2026.
The odd principal submatrices have a genuine largest eigenvalue tending to infinity.
The infinite first column does not belong to the counting l2 space. Thus no operator
with this literal matrix action has the first coordinate vector in its domain.
This does not exclude every possible smaller domain or selfadjoint realization;
none is constructed here. No identification with zeta-zero ordinates is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.SquarefreeResidueMatrix
open ZetaTwoProbability ZetaTwoHilbert

theorem odd_quadratic_lower (N : ℕ) :
    positiveQWeight 2 * (N : ℝ)^2 ≤ quadratic (oddMatrix N) (fun _ => 1) := by
  have h : (∑ _i : Fin N, ∑ _j : Fin N, positiveQWeight 2) ≤
      ∑ i : Fin N, ∑ j : Fin N, oddMatrix N i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact kernel_odd_lower i.val j.val
  simpa [quadratic, Matrix.mulVec, dotProduct, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using h

def oddRayleigh (N : ℕ) : ℝ := quadratic (oddMatrix N) (fun _ => 1) / N

theorem oddRayleigh_lower (N : ℕ) (hN : 0 < N) :
    positiveQWeight 2 * N ≤ oddRayleigh N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hNR).mpr
  simpa [pow_two, oddRayleigh, mul_assoc] using odd_quadratic_lower N

theorem oddRayleigh_tendsto_atTop : Tendsto oddRayleigh atTop atTop := by
  apply tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨1, fun N hN =>
    oddRayleigh_lower N (by omega)⟩)
  exact tendsto_natCast_atTop_atTop.const_mul_atTop weight_two_pos

theorem kernel_first_column_not_l2 :
    ¬ ∃ f : QHilbert, ∀ i : ℕ, f i = rawKernel (i+1) 1 := by
  rintro ⟨f,hf⟩
  have hs := (qCoordinate_square_summable f).comp_injective
    (show Function.Injective (fun k : ℕ => 2*k) by intro a b h; change 2*a = 2*b at h; omega)
  have hb (k : ℕ) : (positiveQWeight 2)^2 ≤ (f (2*k))^2 := by
    rw [hf]
    have hl := kernel_odd_lower k 0
    norm_num at hl
    nlinarith [weight_two_pos]
  have hc : Summable (fun _k : ℕ => (positiveQWeight 2)^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hs
  have hz := (summable_const_iff _).mp hc
  nlinarith [weight_two_pos]
theorem no_operator_on_first_basis
    (D : Submodule ℝ QHilbert) (T : D →ₗ[ℝ] QHilbert)
    (hD : lp.single 2 0 (1 : ℝ) ∈ D)
    (hT : ∀ i : ℕ,
      T ⟨lp.single 2 0 (1 : ℝ),hD⟩ i = rawKernel (i+1) 1) : False :=
  kernel_first_column_not_l2 ⟨T ⟨lp.single 2 0 (1 : ℝ),hD⟩,hT⟩

def truncatedFirstColumn (N k : ℕ) : ℝ :=
  if k < N then rawKernel (k+1) 1 else 0

theorem truncatedFirstColumn_tendsto (k : ℕ) :
    Tendsto (fun N => truncatedFirstColumn N k) atTop (𝓝 (rawKernel (k+1) 1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with N hN
  simp [truncatedFirstColumn, hN]

theorem no_l2_first_column_limit :
    ¬ ∃ f : QHilbert, ∀ k : ℕ,
      Tendsto (fun N => truncatedFirstColumn N k) atTop (𝓝 (f k)) := by
  rintro ⟨f,hf⟩
  apply kernel_first_column_not_l2
  refine ⟨f,fun k => ?_⟩
  exact tendsto_nhds_unique (hf k) (truncatedFirstColumn_tendsto k)

def largestOddEigenvalue (N : ℕ) : ℝ := Matrix.maximalRayleigh (oddMatrix N)

theorem largestOddEigenvalue_isEigenvalue (N : ℕ) [NeZero N] :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (oddMatrix N))
      (largestOddEigenvalue N) :=
  Matrix.maximalRayleigh_hasEigenvalue (oddMatrix_posSemidef N).isHermitian

theorem largestOddEigenvalue_lower (N : ℕ) (hN : 0 < N) :
    positiveQWeight 2 * N ≤ largestOddEigenvalue N := by
  let e : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hn : ‖e‖^2 = (N : ℝ) := by
    simp [EuclideanSpace.norm_sq_eq, e]
  have he : e ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hn
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hb := Matrix.rayleigh_le_maximalRayleigh (oddMatrix N) e he
  have hi : inner ℝ (Matrix.toEuclideanLin (oddMatrix N) e) e =
      quadratic (oddMatrix N) (fun _ => 1) := by
    change inner ℝ ((Matrix.toLpLin 2 2) (oddMatrix N) e) e = _
    simp [Matrix.toLpLin_apply, PiLp.inner_apply, e, quadratic, dotProduct]
  rw [hi, hn] at hb
  exact (oddRayleigh_lower N hN).trans hb

theorem largestOddEigenvalue_tendsto_atTop :
    Tendsto largestOddEigenvalue atTop atTop := by
  apply tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨1, fun N hN =>
    largestOddEigenvalue_lower N (by omega)⟩)
  exact tendsto_natCast_atTop_atTop.const_mul_atTop weight_two_pos

end RiemannResearch.RH.SquarefreeResidueMatrix

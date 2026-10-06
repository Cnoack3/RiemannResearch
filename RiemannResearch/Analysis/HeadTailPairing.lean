import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete signed head-tail pairing
Source: user-provided Green-Pareto-Schur continuation, Sections 12 and 13.8.
The finite normal-equation identity retains both correction squares and
the entire signed physical-tail cross term before applying Cauchy.
Arithmetic tail smallness is not asserted by this module.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.HeadTailPairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A symmetric idempotent physical cutoff splits every real inner product. -/
theorem orthogonal_cutoff_inner_split
    (Q : H →ₗ[ℝ] H)
    (hsym : ∀ x y : H, inner ℝ (Q x) y = inner ℝ x (Q y))
    (hidem : ∀ x : H, Q (Q x) = Q x) (x y : H) :
    inner ℝ x y = inner ℝ (Q x) (Q y) + inner ℝ (x-Q x) (y-Q y) := by
  have hxy : inner ℝ (Q x) (Q y) = inner ℝ x (Q y) := by
    rw [hsym, hidem]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hsym x y, hxy]
  ring

/-- Exact residual pairing with ANY legal trial, using only its two normal
equations and the actual head/tail inner-product decomposition. The signed
tail pairing survives intact before any estimate is taken. -/
theorem projection_residual_eq_head_tail_pairing
    (Q : H →ₗ[ℝ] H) (f u p : H) (hf : Q f = f)
    (hru : inner ℝ (f-p) u = 0)
    (hrp : inner ℝ (f-p) p = 0)
    (hgeometry : inner ℝ (f-p) (f-u) =
      inner ℝ (Q (f-p)) (Q (f-u)) +
      inner ℝ ((f-p)-Q (f-p)) ((f-u)-Q (f-u))) :
    ‖f-p‖^2 = inner ℝ (Q (f-p)) (f-Q u) +
      inner ℝ (p-Q p) (u-Q u) := by
  have hself : inner ℝ (f-p) (f-p) = inner ℝ (f-p) f := by
    rw [inner_sub_right, hrp, sub_zero]
  have hnorm : inner ℝ (f-p) (f-u) = ‖f-p‖^2 := by
    rw [inner_sub_right, hru, sub_zero, ← hself, real_inner_self_eq_norm_sq]
  have hQfu : Q (f-u) = f-Q u := by rw [map_sub, hf]
  have hrt : (f-p)-Q (f-p) = -(p-Q p) := by
    rw [map_sub, hf]
    abel
  have hut : (f-u)-Q (f-u) = -(u-Q u) := by
    rw [map_sub, hf]
    abel
  rw [hnorm, hrt, hut, hQfu] at hgeometry
  simpa only [inner_neg_left, inner_neg_right, neg_neg] using hgeometry

/-- Quantitative form for approximate head matching and bounded complete
trial tails. The residual need not tend to zero in any premise. -/
theorem projection_residual_le_head_error_add_tail_product
    (Q : H →ₗ[ℝ] H) (f u p : H) (hf : Q f = f)
    (hru : inner ℝ (f-p) u = 0)
    (hrp : inner ℝ (f-p) p = 0)
    (hgeometry : inner ℝ (f-p) (f-u) =
      inner ℝ (Q (f-p)) (Q (f-u)) +
      inner ℝ ((f-p)-Q (f-p)) ((f-u)-Q (f-u)))
    (hcontract : ‖Q (f-p)‖ ≤ ‖f-p‖) :
    ‖f-p‖^2 ≤ ‖f-p‖ * ‖f-Q u‖ + ‖p-Q p‖ * ‖u-Q u‖ := by
  rw [projection_residual_eq_head_tail_pairing Q f u p hf hru hrp hgeometry]
  apply add_le_add
  · exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hcontract (norm_nonneg _))
  · exact real_inner_le_norm _ _

/-- The true full correction pairs the explicit head lift's full tail with
the full optimizer's full tail. The premises are just the two actual normal
equations at u and p, the head normal equations, and physical cutoff geometry.
No tail or signed cross term has been discarded. -/
theorem correction_eq_tail_pairing
    (Q : H →ₗ[ℝ] H) (f u p : H)
    (hpyth : ‖p‖^2 = ‖Q p‖^2 + ‖p-Q p‖^2)
    (hpair : inner ℝ p u =
      inner ℝ (Q p) (Q u) + inner ℝ (p-Q p) (u-Q u))
    (hf_u : inner ℝ f u = inner ℝ f (Q u))
    (hf_p : inner ℝ f p = inner ℝ f (Q p))
    (hfull_u : inner ℝ (f-p) u = 0)
    (hfull_p : inner ℝ (f-p) p = 0)
    (hhead_u : inner ℝ (f-Q u) (Q u) = 0)
    (hhead_p : inner ℝ (f-Q u) (Q p) = 0) :
    ‖Q p-Q u‖^2 + ‖p-Q p‖^2 = inner ℝ (u-Q u) (p-Q p) := by
  rw [inner_sub_left, hf_u] at hfull_u
  rw [inner_sub_left, hf_p, real_inner_self_eq_norm_sq] at hfull_p
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hhead_u
  rw [inner_sub_left, ← real_inner_comm (Q u) (Q p)] at hhead_p
  rw [norm_sub_sq_real]
  have hc := real_inner_comm (u-Q u) (p-Q p)
  linarith

/-- Cauchy bounds the complete correction by the product of BOTH full tail
energies. In the Pareto application e is the head adjustment, b is the full
optimizer tail, and c is the explicit head optimizer's tail. -/
theorem correction_sq_le_tail_product (e b c : H)
    (hpair : ‖e‖^2 + ‖b‖^2 = inner ℝ c b) :
    (‖e‖^2 + ‖b‖^2)^2 ≤ ‖c‖^2 * ‖b‖^2 := by
  have hc := real_inner_mul_inner_self_le c b
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  rw [hpair]
  simpa only [pow_two] using hc

/-- Any positive surviving defect forces a reciprocal blow-up of the
explicit head-trial tail relative to the vanishing full-optimizer tail. -/
theorem tail_lower_of_positive_correction
    (T A S D : ℝ) (hD : 0 < D) (hDT : D ≤ T) (hS : 0 < S)
    (hbound : T^2 ≤ A*S) : D^2/S ≤ A := by
  apply (div_le_iff₀ hS).mpr
  nlinarith

/-- Product-smallness is enough; no separate head-trial tail vanishing is
assumed. Scalar form permits arbitrary signed construction of that trial. -/
theorem limit_eq_zero_of_product_tendsto_zero
    (T A S : ℕ → ℝ) (D : ℝ)
    (hT : Tendsto T atTop (𝓝 D))
    (hprod : Tendsto (fun n => A n*S n) atTop (𝓝 0))
    (hbound : ∀ n, (T n)^2 ≤ A n*S n) : D = 0 := by
  have hs : Tendsto (fun n => (T n)^2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg (T n)) hbound hprod
  have hD : D^2 = 0 := tendsto_nhds_unique (hT.pow 2) hs
  exact sq_eq_zero_iff.mp hD

/-- A bounded subsequence of explicit head-tail energies suffices when the
actual full optimizer tail already vanishes. The subsequence is cofinal. -/
theorem limit_eq_zero_of_cofinal_tail_bound
    (T A S : ℕ → ℝ) (D B : ℝ) (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop)
    (hT : Tendsto T atTop (𝓝 D))
    (hS : Tendsto S atTop (𝓝 0))
    (hSnonneg : ∀ n, 0 ≤ S n)
    (hbound : ∀ n, (T n)^2 ≤ A n*S n)
    (hA : ∀ n, A (k n) ≤ B) : D = 0 := by
  have hs : Tendsto (fun n => (T (k n))^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg (T (k n)))
    · intro n
      exact (hbound (k n)).trans
        (mul_le_mul_of_nonneg_right (hA n) (hSnonneg (k n)))
    · simpa only [Function.comp_apply, mul_zero] using (hS.comp hk).const_mul B
  have hD : D^2 = 0 := tendsto_nhds_unique ((hT.comp hk).pow 2) hs
  exact sq_eq_zero_iff.mp hD

end RiemannResearch.Analysis.HeadTailPairing

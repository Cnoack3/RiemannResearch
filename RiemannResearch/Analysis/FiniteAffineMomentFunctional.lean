import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Tactic

/-!
# The signed moment of an affine fit as one linear observation
The dual weights retain signed cancellation and depend only on the sampling
geometry. A square-root error budget also gives an explicit one-sided bound.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProfileEnergy
variable {ι κ : Type*}

def affineMomentDual (s : Finset ι) (w t a : ι → ℝ) (i : ι) : ℝ :=
  let W := mass s w
  let V := ∑ j ∈ s, w j * t j
  let U := energy s w t
  let m0 := ∑ j ∈ s, a j
  let m1 := ∑ j ∈ s, a j * t j
  w i * ((U * m0 - V * m1) + (W * m1 - V * m0) * t i) /
    (W * U - V ^ 2)

theorem affine_signed_moment_eq_dual (s : Finset ι) (w t a b : ι → ℝ)
    (c0 c1 : ℝ)
    (hdet : mass s w * energy s w t - (∑ i ∈ s, w i * t i) ^ 2 ≠ 0)
    (h0 : mass s w * c0 + (∑ i ∈ s, w i * t i) * c1 =
      ∑ i ∈ s, w i * b i)
    (h1 : (∑ i ∈ s, w i * t i) * c0 + energy s w t * c1 =
      ∑ i ∈ s, w i * t i * b i) :
    (∑ i ∈ s, a i * (c0 + c1 * t i)) =
      ∑ i ∈ s, affineMomentDual s w t a i * b i := by
  let W := mass s w
  let V := ∑ i ∈ s, w i * t i
  let U := energy s w t
  let m0 := ∑ i ∈ s, a i
  let m1 := ∑ i ∈ s, a i * t i
  let y0 := ∑ i ∈ s, w i * b i
  let y1 := ∑ i ∈ s, w i * t i * b i
  let D := W * U - V ^ 2
  let A := U * m0 - V * m1
  let B := W * m1 - V * m0
  have hm : D * (c0 * m0 + c1 * m1) = A * y0 + B * y1 :=
    affine_moment_numerator W V U y0 y1 m0 m1 c0 c1 h0 h1
  have hd : (∑ i ∈ s, affineMomentDual s w t a i * b i) =
      (A * y0 + B * y1) / D := by
    change (∑ i ∈ s, (w i * (A + B * t i) / D) * b i) =
      (A * y0 + B * y1) / D
    calc
      _ = (∑ i ∈ s, (A * (w i * b i) + B * (w i * t i * b i))) / D := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ = c0 * m0 + c1 * m1 := by
      dsimp only [m0,m1]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (A * y0 + B * y1) / D := (eq_div_iff hdet).2 (by nlinarith only [hm])
    _ = _ := hd.symm

theorem pairing_finite_combination (s : Finset ι) (D : Finset κ)
    (w f : ι → ℝ) (a : κ → ℝ) (phi : κ → ι → ℝ) :
    pairing s w f (fun i => ∑ d ∈ D, a d * phi d i) =
      ∑ d ∈ D, a d * pairing s w f (phi d) := by
  unfold pairing
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem one_sided_of_square_budget (y q M eps : ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (heps : 0 < eps) (hy : y ^ 2 ≤ q * M) :
    y ≤ eps * q + M / (4 * eps) := by
  have heq : q * M = 4 * (eps * q) * (M / (4 * eps)) := by
    field_simp [heps.ne']
  have hb : q * M ≤ (eps * q + M / (4 * eps)) ^ 2 := by
    rw [heq]
    nlinarith only [sq_nonneg (eps * q - M / (4 * eps))]
  have hn : 0 ≤ eps * q + M / (4 * eps) := by positivity
  have ha : |y| ≤ eps * q + M / (4 * eps) :=
    (sq_le_sq₀ (abs_nonneg y) hn).1 (by simpa only [sq_abs] using hy.trans hb)
  exact (le_abs_self y).trans ha

end RiemannResearch.Analysis.FiniteProfileEnergy

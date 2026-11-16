import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# Finite weighted orthogonality on a function span
Exact residual completion and uniqueness on the positive-weight coordinates.
No independence of the spanning functions is needed. These lemmas connect
the gcd-atom and floor descriptions of the exact-head Green optimizer.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProfileEnergy
variable {ι κ : Type*}

def pairingMap (s : Finset ι) (w R : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := pairing s w R
  map_add' f g := by simp [pairing, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem pairing_eq_zero_on_span (s : Finset ι) (w R : ι → ℝ)
    (D : Set κ) (a : κ → ι → ℝ)
    (hn : ∀ d ∈ D, pairing s w R (a d) = 0) :
    ∀ v ∈ Submodule.span ℝ (a '' D), pairing s w R v = 0 := by
  have hle : Submodule.span ℝ (a '' D) ≤ (pairingMap s w R).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d,hd,rfl⟩
    exact hn d hd
  exact fun v hv => hle hv

theorem energy_add_exact (s : Finset ι) (w R v : ι → ℝ) :
    energy s w (R + v) = energy s w R + energy s w v + 2 * pairing s w R v := by
  unfold energy pairing
  simp only [Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_eq_zero_on_support (s : Finset ι) (w R : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (he : energy s w R = 0) :
    ∀ i ∈ s, R i = 0 := by
  intro i hi
  have hle := Finset.single_le_sum
    (f := fun j => w j * R j ^ 2)
    (fun j hj => mul_nonneg (hw j hj).le (sq_nonneg _)) hi
  change w i * R i ^ 2 ≤ energy s w R at hle
  rw [he] at hle
  by_contra h
  exact (not_lt_of_ge hle) (mul_pos (hw i hi) (sq_pos_of_ne_zero h))

theorem normal_residual_unique (s : Finset ι) (w R T : ι → ℝ)
    (S : Submodule ℝ (ι → ℝ))
    (hw : ∀ i ∈ s, 0 < w i)
    (hR : ∀ v ∈ S, pairing s w R v = 0)
    (hT : ∀ v ∈ S, pairing s w T v = 0)
    (hRT : R - T ∈ S) :
    ∀ i ∈ s, R i = T i := by
  have h0 := hR (R - T) hRT
  have h1 := hT (R - T) hRT
  have he : energy s w (R - T) = 0 := by
    calc
      _ = pairing s w R (R - T) - pairing s w T (R - T) := by
        unfold energy pairing
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply]
        ring
      _ = 0 := by rw [h0,h1,sub_self]
  intro i hi
  exact sub_eq_zero.mp (energy_eq_zero_on_support s w (R - T) hw he i hi)

theorem normal_completion_on_span (s : Finset ι) (w R : ι → ℝ)
    (S : Submodule ℝ (ι → ℝ))
    (hR : ∀ v ∈ S, pairing s w R v = 0) (v : ι → ℝ) (hv : v ∈ S) :
    energy s w (R + v) = energy s w R + energy s w v := by
  rw [energy_add_exact,hR v hv,mul_zero,add_zero]

end RiemannResearch.Analysis.FiniteProfileEnergy

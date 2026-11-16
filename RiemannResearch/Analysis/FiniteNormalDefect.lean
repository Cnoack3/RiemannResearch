import RiemannResearch.Analysis.FiniteWeightedSpan
import Mathlib.Tactic

/-!
# Exact normal-defect identities and a posteriori energy certificates
The complete energy gap is retained before applying finite Cauchy--Schwarz.
A proved coefficient coercivity bound controls the gap without a Gram inverse.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProfileEnergy
variable {ι κ : Type*}

theorem pairing_synthesis (s : Finset ι) (D : Finset κ) (w R : ι → ℝ)
    (a : κ → ι → ℝ) (c : κ → ℝ) :
    pairing s w R (fun i => ∑ d ∈ D, c d * a d i) =
      ∑ d ∈ D, c d * pairing s w R (a d) := by
  have hf : (fun i => ∑ d ∈ D, c d * a d i) = ∑ d ∈ D, c d • a d := by
    funext i
    simp
  change (pairingMap s w R) _ = _
  rw [hf]
  simp [pairingMap, map_sum, map_smul]
  rfl

theorem normal_synthesis_completion (s : Finset ι) (D : Finset κ) (w R : ι → ℝ)
    (a : κ → ι → ℝ) (c : κ → ℝ)
    (hn : ∀ d ∈ D, pairing s w R (a d) = 0) :
    energy s w (R + fun i => ∑ d ∈ D, c d * a d i) =
      energy s w R + energy s w (fun i => ∑ d ∈ D, c d * a d i) := by
  rw [energy_add_exact, pairing_synthesis]
  have hz : (∑ d ∈ D, c d * pairing s w R (a d)) = 0 :=
    Finset.sum_eq_zero (fun d hd => by rw [hn d hd,mul_zero])
  rw [hz,mul_zero,add_zero]

/-- The energy error is exactly coefficient error paired with the measured
normal-equation defect of the approximate residual. -/
theorem normal_defect_energy_identity (s : Finset ι) (D : Finset κ) (w R : ι → ℝ)
    (a : κ → ι → ℝ) (c : κ → ℝ)
    (hn : ∀ d ∈ D, pairing s w R (a d) = 0) :
    energy s w (fun i => ∑ d ∈ D, c d * a d i) =
      ∑ d ∈ D, c d * pairing s w (R + fun i => ∑ e ∈ D, c e * a e i) (a d) := by
  rw [← pairing_synthesis]
  have hz : pairing s w R (fun i => ∑ d ∈ D, c d * a d i) = 0 := by
    rw [pairing_synthesis]
    exact Finset.sum_eq_zero (fun d hd => by rw [hn d hd,mul_zero])
  calc
    _ = pairing s w R (fun i => ∑ d ∈ D, c d * a d i) +
        energy s w (fun i => ∑ d ∈ D, c d * a d i) := by rw [hz,zero_add]
    _ = _ := by
      unfold energy pairing
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.add_apply]
      ring

theorem energy_le_of_dual_coercivity (D : Finset κ) (c b : κ → ℝ)
    (E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hdual : E = ∑ d ∈ D, c d * b d) (hcoef : (∑ d ∈ D, c d ^ 2) ≤ K * E) :
    E ≤ K * ∑ d ∈ D, b d ^ 2 := by
  have hb : 0 ≤ ∑ d ∈ D, b d ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs := pairing_sq_le D (fun _ => 1) c b (by intro i hi; norm_num)
  simp only [pairing, energy, one_mul] at hcs
  rw [← hdual] at hcs
  have hh := mul_le_mul_of_nonneg_right hcoef hb
  by_cases hz : E = 0
  · rw [hz]
    exact mul_nonneg hK hb
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    by_contra! h
    have hpos := mul_pos hp (sub_pos.mpr h)
    nlinarith

end RiemannResearch.Analysis.FiniteProfileEnergy

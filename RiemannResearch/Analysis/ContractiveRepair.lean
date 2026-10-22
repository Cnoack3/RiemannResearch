import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Contractive evolution with vanishing repair errors

Source: `RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md`,
Section 4. These are reusable perturbation theorems. In applications the
contraction on the mean-zero subspace and the existence of legal repairs
are separate hypotheses; no arithmetic repair theorem or spectral
identification is assumed as an axiom here.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ContractiveRepair

/-- The exact scalar convolution that bounds the propagated repair errors. -/
def geometricConvolution (q : ℝ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q ^ (n - 1 - j) * b j

@[simp] theorem geometricConvolution_zero (q : ℝ) (b : ℕ → ℝ) :
    geometricConvolution q b 0 = 0 := by simp [geometricConvolution]

theorem geometricConvolution_succ (q : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    geometricConvolution q b (n + 1) = q * geometricConvolution q b n + b n := by
  simp only [geometricConvolution, Finset.sum_range_succ, Nat.add_sub_cancel,
    Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have he : n - j = (n - 1 - j) + 1 := by omega
  rw [he, pow_succ']
  ring

/-- Scalar recurrence bound, retaining every propagated forcing term. -/
theorem recurrence_le_geometricConvolution {u b : ℕ → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hrec : ∀ n, u (n + 1) ≤ q * u n + b n) (n : ℕ) :
    u n ≤ q ^ n * u 0 + geometricConvolution q b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      u (n + 1) ≤ q * u n + b n := hrec n
      _ ≤ q * (q ^ n * u 0 + geometricConvolution q b n) + b n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
      _ = q ^ (n + 1) * u 0 + geometricConvolution q b (n + 1) := by
        rw [geometricConvolution_succ, pow_succ']
        ring

/-- For a strict contraction, forcing that merely tends to zero is sufficient;
there is no summability hypothesis. -/
theorem tendsto_zero_of_recurrence {u b : ℕ → ℝ} {q : ℝ}
    (hu : ∀ n, 0 ≤ u n) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n, u (n + 1) ≤ q * u n + b n)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha (hu n))
  · intro ε hε
    have hδ : 0 < (1 - q) * (ε / 2) :=
      mul_pos (sub_pos.mpr hq1) (half_pos hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hb.eventually_lt_const hδ)
    have hbound : ∀ n, u (N + n) ≤ q ^ n * u N + ε / 2 := by
      intro n
      induction n with
      | zero => simp only [Nat.add_zero, pow_zero, one_mul]; linarith
      | succ n ih =>
        have hn := hN (N + n) (Nat.le_add_right N n)
        have hr := hrec (N + n)
        have hm := mul_le_mul_of_nonneg_left ih hq0
        rw [pow_succ']
        have hi : N + (n + 1) = (N + n) + 1 := by omega
        rw [hi]
        nlinarith
    have hp : Tendsto (fun n : ℕ => q ^ n * u N) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
          (show |q| < 1 by rwa [abs_of_nonneg hq0])).mul_const (u N)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
      (hp.eventually_lt_const (half_pos hε))
    apply Filter.eventually_atTop.2
    refine ⟨N + M, ?_⟩
    intro n hn
    have hNn : N ≤ n := by omega
    have hMn : M ≤ n - N := by omega
    have hbnd := hbound (n - N)
    rw [Nat.add_sub_of_le hNn] at hbnd
    have hsmall := hM (n - N) hMn
    linarith

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- A normed-space orbit inherits the complete geometric convolution bound. -/
theorem norm_le_geometricConvolution {x e : ℕ → E} {q : ℝ}
    (hq : 0 ≤ q) (hrec : ∀ n, ‖x (n + 1)‖ ≤ q * ‖x n‖ + ‖e n‖)
    (n : ℕ) :
    ‖x n‖ ≤ q ^ n * ‖x 0‖ + geometricConvolution q (fun j => ‖e j‖) n :=
  recurrence_le_geometricConvolution (u := fun j => ‖x j‖)
    (b := fun j => ‖e j‖) hq hrec n

theorem tendsto_zero_of_norm_recurrence {x e : ℕ → E} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n, ‖x (n + 1)‖ ≤ q * ‖x n‖ + ‖e n‖)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  exact tendsto_zero_of_recurrence (fun n => norm_nonneg _) hq0 hq1 hrec
    (tendsto_zero_iff_norm_tendsto_zero.1 he)

/-- An explicit relative repair budget gives a geometric rate. -/
theorem norm_le_pow_of_relative_repair {x e : ℕ → E} {q η : ℝ}
    (h0 : 0 ≤ q + η)
    (hrec : ∀ n, ‖x (n + 1)‖ ≤ q * ‖x n‖ + ‖e n‖)
    (he : ∀ n, ‖e n‖ ≤ η * ‖x n‖) (n : ℕ) :
    ‖x n‖ ≤ (q + η) ^ n * ‖x 0‖ := by
  apply le_geom h0 n
  intro k _
  have h := hrec k
  have he' := he k
  nlinarith

theorem tendsto_zero_of_relative_repair {x e : ℕ → E} {q η : ℝ}
    (h0 : 0 ≤ q + η) (h1 : q + η < 1)
    (hrec : ∀ n, ‖x (n + 1)‖ ≤ q * ‖x n‖ + ‖e n‖)
    (he : ∀ n, ‖e n‖ ≤ η * ‖x n‖) : Tendsto x atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hp : Tendsto (fun n : ℕ => (q + η) ^ n * ‖x 0‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |q + η| < 1 by rwa [abs_of_nonneg h0])).mul_const ‖x 0‖
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp
    (fun n => norm_nonneg _) (norm_le_pow_of_relative_repair h0 hrec he)

end Normed

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual error of a repaired step, rather than a separately chosen error. -/
def repairError (P : E →ₗ[ℝ] E) (F : ℕ → E) (n : ℕ) : E :=
  F (n + 1) - P (F n)

theorem centered_recurrence (P : E →ₗ[ℝ] E) (F : ℕ → E)
    (z : E) (hz : P z = z) (n : ℕ) :
    F (n + 1) - z = P (F n - z) + repairError P F n := by
  rw [map_sub, hz, repairError]
  abel

theorem repairError_mean_zero (P : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ)
    (F : ℕ → E) (hmean : ∀ n, ℓ (F n) = 1)
    (hpres : ∀ x, ℓ (P x) = ℓ x) (n : ℕ) :
    ℓ (repairError P F n) = 0 := by
  simp [repairError, map_sub, hpres, hmean]

/-- Convergence to a fixed vector, with contraction required only on the
kernel of the mean functional. Existence of suitable repaired orbits remains
an explicit hypothesis. -/
theorem tendsto_fixedPoint_of_vanishing_repair
    (P : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) (F : ℕ → E) (z : E) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : P z = z) (hℓz : ℓ z = 1)
    (hmean : ∀ n, ℓ (F n) = 1)
    (hcontract : ∀ x, ℓ x = 0 → ‖P x‖ ≤ q * ‖x‖)
    (he : Tendsto (repairError P F) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 z) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply tendsto_zero_of_recurrence (fun n => norm_nonneg _) hq0 hq1
  · intro n
    rw [centered_recurrence P F z hz n]
    exact (norm_add_le _ _).trans
      (add_le_add (hcontract (F n - z) (by simp [map_sub, hmean, hℓz])) le_rfl)
  · exact tendsto_zero_iff_norm_tendsto_zero.1 he

/-- Quantitative bound for the centered orbit with every forcing term retained. -/
theorem fixedPoint_error_le_geometricConvolution
    (P : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) (F : ℕ → E) (z : E) {q : ℝ}
    (hq : 0 ≤ q) (hz : P z = z) (hℓz : ℓ z = 1)
    (hmean : ∀ n, ℓ (F n) = 1)
    (hcontract : ∀ x, ℓ x = 0 → ‖P x‖ ≤ q * ‖x‖) (n : ℕ) :
    ‖F n - z‖ ≤ q ^ n * ‖F 0 - z‖ +
      geometricConvolution q (fun j => ‖repairError P F j‖) n := by
  apply recurrence_le_geometricConvolution hq _ n
  intro j
  rw [centered_recurrence P F z hz j]
  exact (norm_add_le _ _).trans
    (add_le_add (hcontract (F j - z) (by simp [map_sub, hmean, hℓz])) le_rfl)

end Linear

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- The full one-step squared error, including the signed mixed term. -/
theorem exact_repaired_energy (x y e : E) (h : y = x + e) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * RCLike.re (inner 𝕜 x e) + ‖e‖ ^ 2 := by
  rw [h]
  exact norm_add_sq x e

end InnerProduct

end RiemannResearch.Analysis.ContractiveRepair

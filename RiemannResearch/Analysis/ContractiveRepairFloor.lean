import RiemannResearch.Analysis.ContractiveRepair
import Mathlib.Tactic.Positivity

/-!
# A quantitative floor for recurrent repair

Source: user-provided stringent-condition catalogue, condition 15, 2026-09-21.
This is a general norm-recurrence result. It gives the limsup lower bound in
its cofinal strict-threshold form, avoiding any boundedness assumption needed
to package a real-valued limsup. The proof is a finite descent contradiction.
-/

noncomputable section
namespace RiemannResearch.Analysis.ContractiveRepair

variable {E : Type*} [NormedAddCommGroup E]

/-- A positive error floor forces repairs of at least `(1-q)*a` in the cofinal
sense. No vanishing-repair assumption appears in this theorem. -/
theorem repair_cofinally_large_of_norm_floor (x e : ℕ → E) (q a b : ℝ)
    (hq : q < 1) (hfloor : ∀ n, a ≤ ‖x n‖)
    (hrec : ∀ n, ‖x (n + 1)‖ ≤ q * ‖x n‖ + ‖e n‖)
    (hb : b < (1 - q) * a) (N : ℕ) :
    ∃ n, N ≤ n ∧ b < ‖e n‖ := by
  by_contra! hsmall
  let ε : ℝ := (1 - q) * a - b
  have hε : 0 < ε := sub_pos.mpr hb
  have hstep (n : ℕ) (hn : N ≤ n) : ‖x (n + 1)‖ ≤ ‖x n‖ - ε := by
    have hf := mul_le_mul_of_nonneg_left (hfloor n) (sub_pos.mpr hq).le
    have hr := hrec n
    have he := hsmall n hn
    dsimp [ε]
    nlinarith
  have hbound (k : ℕ) : ‖x (N + k)‖ ≤ ‖x N‖ - (k : ℝ) * ε := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hstep (N + k) (Nat.le_add_right N k)
      simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
        (show ‖x (N + k + 1)‖ ≤ ‖x N‖ - ((k : ℝ) + 1) * ε by linarith)
  obtain ⟨k, hk⟩ := exists_nat_gt (‖x N‖ / ε)
  have hlarge : ‖x N‖ < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hn := hbound k
  nlinarith [norm_nonneg (x (N + k))]

variable [NormedSpace ℝ E]

/-- A fixed-point orbit inherits the same quantitative bound from contraction
on the kernel of its preserved mean. -/
theorem fixedPoint_repair_cofinally_large
    (P : E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ) (F : ℕ → E) (z : E)
    (q a b : ℝ) (hq : q < 1) (hz : P z = z) (hℓz : ℓ z = 1)
    (hmean : ∀ n, ℓ (F n) = 1)
    (hcontract : ∀ x, ℓ x = 0 → ‖P x‖ ≤ q * ‖x‖)
    (hfloor : ∀ n, a ≤ ‖F n - z‖) (hb : b < (1 - q) * a) (N : ℕ) :
    ∃ n, N ≤ n ∧ b < ‖repairError P F n‖ := by
  apply repair_cofinally_large_of_norm_floor
    (fun n => F n - z) (repairError P F) q a b hq hfloor
    (fun n => ?_) hb N
  rw [centered_recurrence P F z hz n]
  exact (norm_add_le _ _).trans
    (add_le_add (hcontract (F n - z) (by simp [map_sub, hmean, hℓz])) le_rfl)

end RiemannResearch.Analysis.ContractiveRepair

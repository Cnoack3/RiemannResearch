import RiemannResearch.RH.CommonScaleRepairObstruction
import RiemannResearch.RH.DyadicArithmeticResidueTelescoping

/-!
# Actual signed rough packets and their common-scale repair obstruction

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 11. Finite supports and all signed coefficients can vary with the
stage. Squarefreeness is unnecessary for the obstruction itself.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

def finiteRoughPacket (s : Finset ℕ+) (q : ℕ+ → ℝ) : ThresholdHilbert :=
  ∑ u ∈ s, q u • hilbertResidue u u.pos

def commonScaleRoughPacket (A : ℕ) (hA : 0 < A)
    (s : Finset ℕ+) (q : ℕ+ → ℝ) : ThresholdHilbert :=
  ∑ u ∈ s, q u • hilbertResidue (A * u) (Nat.mul_pos hA u.pos)

/-- The exact common-scale remainder identity, retaining every signed term. -/
theorem commonScaleRoughPacket_eq (A : ℕ) (hA : 0 < A)
    (s : Finset ℕ+) (q : ℕ+ → ℝ) :
    commonScaleRoughPacket A hA s q =
      hilbertDilation A hA (finiteRoughPacket s q) +
        (∑ u ∈ s, q u) • hilbertResidue A hA := by
  change (∑ u ∈ s, q u • hilbertResidue (A * u) (Nat.mul_pos hA u.pos)) =
    (hilbertDilationLinear A hA) (∑ u ∈ s, q u • hilbertResidue u u.pos) +
      (∑ u ∈ s, q u) • hilbertResidue A hA
  rw [map_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [map_smul]
  change q u • hilbertResidue (A * u) (Nat.mul_pos hA u.pos) =
    q u • hilbertDilation A hA (hilbertResidue u u.pos) +
      q u • hilbertResidue A hA
  rw [hilbertDilation_residue_eq_sub, smul_sub]
  abel

/-- The actual finite signed packet has fifth coordinate charge exactly
`-5 q₅`, with absent coefficients interpreted as zero. -/
theorem fifthChargeObserver_finiteRoughPacket (s : Finset ℕ+) (q : ℕ+ → ℝ)
    (hs : ∀ u ∈ s, Nat.Coprime (u : ℕ) 6) :
    fifthChargeObserver (finiteRoughPacket s q) =
      -5 * (if (5 : ℕ+) ∈ s then q 5 else 0) := by
  simp only [finiteRoughPacket, map_sum, map_smul, RingHom.id_apply, smul_eq_mul]
  calc
    (∑ u ∈ s, q u * fifthChargeObserver (hilbertResidue u u.pos)) =
        ∑ u ∈ s, if u = (5 : ℕ+) then -5 * q 5 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [fifthChargeObserver_residue u u.pos (hs u hu)]
      by_cases he : u = (5 : ℕ+)
      · subst u
        norm_num <;> ring
      · have he' : (u : ℕ) ≠ 5 := by
          intro heq
          apply he
          exact Subtype.ext heq
        simp [he, he']
    _ = _ := by
      by_cases hmem : (5 : ℕ+) ∈ s <;> simp [hmem]

/-- The explicit full signed lower bound (11.6). Every coefficient except
the detected fifth charge may vary arbitrarily with the outward scale. -/
theorem commonScaleRoughPacket_norm_sq_lower (A : ℕ) (hA : 2 ≤ A)
    (s : Finset ℕ+) (q : ℕ+ → ℝ)
    (hs : ∀ u ∈ s, Nat.Coprime (u : ℕ) 6) :
    25 * (A : ℝ) * (if (5 : ℕ+) ∈ s then q 5 else 0)^2 /
        (52 * (1 + 2 * Real.sqrt 2)^2) ≤
      ‖commonScaleRoughPacket A (by omega) s q‖^2 := by
  have h := commonDilation_fifthCharge_control A hA (finiteRoughPacket s q)
    (∑ u ∈ s, q u)
  rw [fifthChargeObserver_finiteRoughPacket s q hs, sq_abs] at h
  rw [← commonScaleRoughPacket_eq A (by omega) s q] at h
  have hden : 0 < 52 * (1 + 2 * Real.sqrt 2)^2 := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Persistent fifth charge forces every common outward repair to diverge,
even when every other component and every finite support varies arbitrarily. -/
theorem commonScaleRoughPacket_norm_tendsto_atTop
    (A : ℕ → ℕ) (hA : ∀ j, 2 ≤ A j) (hAinf : Tendsto A atTop atTop)
    (s : ℕ → Finset ℕ+) (q : ℕ → ℕ+ → ℝ)
    (hs : ∀ j u, u ∈ s j → Nat.Coprime (u : ℕ) 6)
    {r : ℝ} (hr : r ≠ 0)
    (hq : Tendsto (fun j => if (5 : ℕ+) ∈ s j then q j 5 else 0)
      atTop (nhds r)) :
    Tendsto (fun j =>
      ‖commonScaleRoughPacket (A j) (by have := hA j; omega) (s j) (q j)‖)
      atTop atTop := by
  have hobs : Tendsto (fun j => fifthChargeObserver (finiteRoughPacket (s j) (q j)))
      atTop (nhds (-5 * r)) := by
    have heq : (fun j => fifthChargeObserver (finiteRoughPacket (s j) (q j))) =
        (fun j => -5 * (if (5 : ℕ+) ∈ s j then q j 5 else 0)) := by
      funext j
      exact fifthChargeObserver_finiteRoughPacket (s j) (q j) (hs j)
    rw [heq]
    exact hq.const_mul (-5)
  have hnon : -5 * r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h := commonDilation_norm_tendsto_of_fifthCharge A hA hAinf
    (fun j => finiteRoughPacket (s j) (q j))
    (fun j => ∑ u ∈ s j, q j u) hnon hobs
  simpa only [commonScaleRoughPacket_eq] using h

end
end RiemannResearch.RH.Pareto

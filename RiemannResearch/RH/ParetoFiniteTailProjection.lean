import RiemannResearch.RH.ParetoFiniteGram
import RiemannResearch.RH.ParetoTailOrthogonalization

/-!
# Finite tail projection with exact norm splitting and preserved head

Source: repair of the covariance suggestion in the user-provided
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §8.

This is the finite simultaneous step in reverse Gram--Schmidt for arithmetic
repairs. The tail family is already orthogonal, and all its directions vanish
on the current head. Orthogonal projection therefore preserves that head,
the current Möbius defect, and a strictly positive anchored pivot.

The equality uses the complete infinite Pareto covariance. The projection
stays in the real span of its inputs. When those inputs are legal packet
combinations, it remains a legal packet combination. It makes no assertion about infinite triangular
coefficient transforms or density of the binary repair span.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def finiteTailProjection {ι : Type*} (s : Finset ι)
    (r : ℕ → ℝ) (v : ι → ℕ → ℝ) (k : ℕ) : ℝ :=
  r k - ∑ i ∈ s, (paretoInner r (v i) / paretoInner (v i) (v i)) * v i k

theorem finiteTailProjection_bounded {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i) :
    ∀ k, |finiteTailProjection s r v k| ≤
      C + ∑ i ∈ s, |paretoInner r (v i) / paretoInner (v i) (v i)| * B i :=
  bounded_sub hr (bounded_finsetCombination s _ hv)

theorem finiteTailProjection_orthogonal {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (v i) (v j) = 0)
    (hn : ∀ i ∈ s, paretoInner (v i) (v i) ≠ 0)
    (j : ι) (hj : j ∈ s) :
    paretoInner (finiteTailProjection s r v) (v j) = 0 := by
  classical
  let a : ι → ℝ := fun i => paretoInner r (v i) / paretoInner (v i) (v i)
  have ha := fun i => bounded_const_mul (hv i) (a i)
  change paretoInner (fun k => r k - ∑ i ∈ s, a i * v i k) (v j) = 0
  rw [paretoInner_sub_left hr (bounded_finsetCombination s a hv) (hv j),
    paretoInner_finsetSum_left s ha (hv j)]
  have hsum : (∑ i ∈ s, paretoInner (fun k => a i * v i k) (v j)) =
      paretoInner r (v j) := by
    rw [Finset.sum_eq_single j]
    · rw [paretoInner_const_mul_left (hv j) (hv j)]
      exact div_mul_cancel₀ _ (hn j hj)
    · intro i hi hij
      rw [paretoInner_const_mul_left (hv i) (hv j), ho i hi j hj hij, mul_zero]
    · exact fun h => (h hj).elim
  rw [hsum, sub_self]

/-- Exact coefficient energy of the orthogonal tail projection. -/
theorem finiteTailProjection_projection_energy {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {B : ι → ℝ}
    (hv : ∀ i k, |v i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (v i) (v j) = 0)
    (hn : ∀ i ∈ s, paretoInner (v i) (v i) ≠ 0) :
    paretoInner
      (fun k => ∑ i ∈ s, (paretoInner r (v i) / paretoInner (v i) (v i)) * v i k)
      (fun k => ∑ i ∈ s, (paretoInner r (v i) / paretoInner (v i) (v i)) * v i k) =
      ∑ i ∈ s, (paretoInner r (v i))^2 / paretoInner (v i) (v i) := by
  rw [paretoInner_finsetCombination_of_orthogonal s _ hv ho]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hn i hi]

/-- The finite Schur complement is exactly the remaining full squared norm. -/
theorem finiteTailProjection_norm {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (v i) (v j) = 0)
    (hn : ∀ i ∈ s, paretoInner (v i) (v i) ≠ 0) :
    paretoInner (finiteTailProjection s r v) (finiteTailProjection s r v) =
      paretoInner r r - ∑ i ∈ s,
        (paretoInner r (v i))^2 / paretoInner (v i) (v i) := by
  let a : ι → ℝ := fun i => paretoInner r (v i) / paretoInner (v i) (v i)
  let P : ℕ → ℝ := fun k => ∑ i ∈ s, a i * v i k
  have hP := bounded_finsetCombination s a hv
  have ha := fun i => bounded_const_mul (hv i) (a i)
  have hcross : paretoInner r P = ∑ i ∈ s,
      (paretoInner r (v i))^2 / paretoInner (v i) (v i) := by
    dsimp [P]
    rw [paretoInner_finsetSum_right s hr ha]
    apply Finset.sum_congr rfl
    intro i hi
    rw [paretoInner_const_mul_right hr (hv i)]
    dsimp [a]
    ring
  have hnorm : paretoInner P P = ∑ i ∈ s,
      (paretoInner r (v i))^2 / paretoInner (v i) (v i) :=
    finiteTailProjection_projection_energy s hv ho hn
  have h := paretoInner_residual_polynomial hr hP (1 : ℝ)
  have h' : paretoInner (fun k => r k - P k) (fun k => r k - P k) =
      paretoInner r r - 2 * paretoInner r P + paretoInner P P := by
    simpa only [one_mul, one_pow, mul_one] using h
  change paretoInner (fun k => r k - P k) (fun k => r k - P k) = _
  rw [h', hcross, hnorm]
  ring

theorem finiteTailProjection_energy_split {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (v i) (v j) = 0)
    (hn : ∀ i ∈ s, paretoInner (v i) (v i) ≠ 0) :
    paretoInner r r =
      paretoInner (finiteTailProjection s r v) (finiteTailProjection s r v) +
      ∑ i ∈ s, (paretoInner r (v i))^2 / paretoInner (v i) (v i) := by
  rw [finiteTailProjection_norm s hr hv ho hn]
  ring

theorem finiteTailProjection_norm_le {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → paretoInner (v i) (v j) = 0)
    (hn : ∀ i ∈ s, paretoInner (v i) (v i) ≠ 0) :
    paretoInner (finiteTailProjection s r v) (finiteTailProjection s r v) ≤
      paretoInner r r := by
  rw [finiteTailProjection_norm s hr hv ho hn]
  exact sub_le_self _ (Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (paretoInner_self_nonneg (v i)))

theorem finiteTailProjection_preserves_head {ι : Type*} (s : Finset ι)
    (r : ℕ → ℝ) (v : ι → ℕ → ℝ) (p : ℕ)
    (hvhead : ∀ i ∈ s, ∀ k ≤ p, v i k = 0) :
    ∀ k ≤ p, finiteTailProjection s r v k = r k := by
  intro k hk
  unfold finiteTailProjection
  have hsum : (∑ i ∈ s,
      (paretoInner r (v i) / paretoInner (v i) (v i)) * v i k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hvhead i hi k hk, mul_zero]
  rw [hsum, sub_zero]

/-- A unit anchor gives a positive lower bound even after all finite tail
directions have been eliminated simultaneously. -/
theorem finiteTailProjection_anchor_lower {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (p : ℕ) (hrp : r p = -1) (hvhead : ∀ i ∈ s, ∀ k ≤ p, v i k = 0) :
    positiveWeight p ≤
      paretoInner (finiteTailProjection s r v) (finiteTailProjection s r v) := by
  have h := paretoInner_coordinate_square_le (finiteTailProjection_bounded s hr hv) p
  rw [finiteTailProjection_preserves_head s r v p hvhead p le_rfl, hrp] at h
  simpa using h

theorem finiteTailProjection_pos_of_anchor {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (p : ℕ) (hp : 0 < p) (hrp : r p ≠ 0)
    (hvhead : ∀ i ∈ s, ∀ k ≤ p, v i k = 0) :
    0 < paretoInner (finiteTailProjection s r v) (finiteTailProjection s r v) := by
  apply paretoInner_pos_of_anchor (finiteTailProjection_bounded s hr hv) p hp
  rwa [finiteTailProjection_preserves_head s r v p hvhead p le_rfl]

theorem finiteTailProjection_preserves_defect {ι : Type*} (s : Finset ι)
    (r : ℕ → ℝ) (v : ι → ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hvhead : ∀ i ∈ s, ∀ k ≤ p, v i k = 0) :
    mobiusDifference p (finiteTailProjection s r v) = mobiusDifference p r := by
  unfold finiteTailProjection
  rw [mobiusDifference_sub_fn]
  have hzero : mobiusDifference p
      (fun k => ∑ i ∈ s, (paretoInner r (v i) / paretoInner (v i) (v i)) * v i k) = 0 := by
    apply mobiusDifference_zero_of_head _ p hp
    intro k hk
    apply Finset.sum_eq_zero
    intro i hi
    rw [hvhead i hi k hk, mul_zero]
  rw [hzero, sub_zero]

theorem finiteTailProjection_preserves_mean {ι : Type*} (s : Finset ι)
    {r : ℕ → ℝ} {v : ι → ℕ → ℝ} {C : ℝ} {B : ι → ℝ}
    (hr : ∀ k, |r k| ≤ C) (hv : ∀ i k, |v i k| ≤ B i)
    (hvm : ∀ i ∈ s, paretoMean (v i) = 0) :
    paretoMean (finiteTailProjection s r v) = paretoMean r := by
  let a : ι → ℝ := fun i => paretoInner r (v i) / paretoInner (v i) (v i)
  have hP := bounded_finsetCombination s a hv
  have ha := fun i => bounded_const_mul (hv i) (a i)
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have hsum : paretoMean (fun k => ∑ i ∈ s, a i * v i k) = 0 := by
    rw [← paretoInner_one_right, paretoInner_finsetSum_left s ha h1]
    apply Finset.sum_eq_zero
    intro i hi
    rw [paretoInner_const_mul_left (hv i) h1, paretoInner_one_right, hvm i hi, mul_zero]
  change paretoMean (fun k => r k - ∑ i ∈ s, a i * v i k) = paretoMean r
  rw [paretoMean_sub hr hP, hsum, sub_zero]

end
end RiemannResearch.RH.Pareto

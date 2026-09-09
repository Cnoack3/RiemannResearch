import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoFiniteSchur
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact head interpolation in the genuine Pareto CRT form

Source: user-provided argument in
`RH_CRT_Packet_Research_2026-09-09.md`, Section 2, equations (3)--(6).
The existing periodic regrouping and finite Schur modules supply the
infinite-sum identities. This module identifies the strictly positive
tail weights, retains the full signed defect from uniform CRT weights,
and assembles exact head interpolation with simultaneous optimization.

There is no uniform-in-N estimate in this file. The genuine Gram inverse
is constructed from independence of the actual residue columns.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ExactHeadCRT
noncomputable section

/-- The entire progression after removing its possible head coordinate. -/
def tailWeight (Q N r : ℕ) : ℝ :=
  progressionWeight Q r - if r ≤ N then positiveWeight r else 0

/-- Complete tail energy represented on one period, not a truncated sum. -/
def tailEnergy (Q N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ r : Fin Q, tailWeight Q N (r.val + 1) * (f (r.val + 1)) ^ 2

/-- The full signed defect from the uniform residue law. -/
def uniformDefect (Q r : ℕ) : ℝ := progressionWeight Q r - 1 / (Q : ℝ)

theorem tailWeight_eq (Q N r : ℕ) (hQ : 0 < Q) :
    tailWeight Q N r =
      if r ≤ N then progressionWeight Q (r + Q) else progressionWeight Q r := by
  by_cases hr : r ≤ N
  · simp only [tailWeight, if_pos hr]
    rw [progressionWeight_split Q r hQ]
    ring
  · simp [tailWeight, hr]

theorem tailWeight_pos (Q N r : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    0 < tailWeight Q N r := by
  rw [tailWeight_eq Q N r hQ]
  split
  · exact progressionWeight_pos Q (r + Q) hQ (by omega)
  · exact progressionWeight_pos Q r hQ hr

theorem tailEnergy_nonneg (Q N : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) :
    0 ≤ tailEnergy Q N f := by
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (le_of_lt (tailWeight_pos Q N (r.val + 1) hQ (by omega)))
    (sq_nonneg _)

private theorem initialMass (N : ℕ) :
    (∑ j ∈ Finset.range N, positiveWeight (j + 1)) = (N : ℝ) / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [positiveWeight, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [h1, h2]
    <;> ring

/-- The head contribution in any larger residue chart is exactly N/(N+1). -/
theorem headMass (Q N : ℕ) (hNQ : N ≤ Q) :
    (∑ r : Fin Q, if r.val + 1 ≤ N then positiveWeight (r.val + 1) else 0) =
      (N : ℝ) / (N + 1) := by
  change (∑ r : Fin Q, (fun j : ℕ =>
    if j + 1 ≤ N then positiveWeight (j + 1) else 0) r.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if j + 1 ≤ N then positiveWeight (j + 1) else 0) Q]
  calc
    _ = ∑ j ∈ Finset.range N, positiveWeight (j + 1) := by
      symm
      calc
        _ = ∑ j ∈ Finset.range N,
            if j + 1 ≤ N then positiveWeight (j + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
        _ = ∑ j ∈ Finset.range Q,
            if j + 1 ≤ N then positiveWeight (j + 1) else 0 := by
          apply Finset.sum_subset (Finset.range_mono hNQ)
          intro j _ hj
          have hjN : ¬ j < N := by simpa only [Finset.mem_range] using hj
          have hn : ¬ j + 1 ≤ N := by omega
          simp only [if_neg hn]
    _ = _ := initialMass N

/-- Actual periodic norm equals the exact head mass plus the complete tail. -/
theorem norm_decomposition (Q N : ℕ) (hQ : 0 < Q) (hNQ : N ≤ Q)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + Q) = f k)
    (hh : ∀ k, 0 < k → k ≤ N → f k = 1) :
    paretoInner f f = (N : ℝ) / (N + 1) + tailEnergy Q N f := by
  rw [periodic_paretoInner Q hQ f hf hp, ← headMass Q N hNQ]
  unfold tailEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.val + 1 ≤ N
  · simp only [tailWeight, if_pos hr, hh (r.val + 1) (by omega) hr, one_pow, mul_one]
    ring
  · simp [tailWeight, hr]

/-- Null head directions have identical full and tail quadratic energies. -/
theorem nullHead_norm (Q N : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + Q) = f k)
    (hh : ∀ k, 0 < k → k ≤ N → f k = 0) :
    paretoInner f f = tailEnergy Q N f := by
  rw [periodic_paretoInner Q hQ f hf hp]
  unfold tailEnergy
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.val + 1 ≤ N
  · simp [tailWeight, hr, hh (r.val + 1) (by omega) hr]
  · simp [tailWeight, hr]

theorem uniformDefect_sum (Q : ℕ) (hQ : 0 < Q) :
    (∑ r : Fin Q, uniformDefect Q (r.val + 1)) = 0 := by
  unfold uniformDefect
  rw [Finset.sum_sub_distrib, progressionWeight_normalization Q hQ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  field_simp [hQ0]
  ring

/-- Uniform averaging plus its entire defect, including every mixed entry. -/
theorem mixed_uniform_defect (Q : ℕ) (hQ : 0 < Q)
    (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hpf : ∀ k, f (k + Q) = f k) (hpg : ∀ k, g (k + Q) = g k) :
    paretoInner f g =
      (1 / (Q : ℝ)) * (∑ r : Fin Q, f (r.val + 1) * g (r.val + 1)) +
      ∑ r : Fin Q, uniformDefect Q (r.val + 1) *
        (f (r.val + 1) * g (r.val + 1)) := by
  rw [periodic_paretoInner_mixed Q hQ f g hf hg hpf hpg]
  simp only [uniformDefect, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The first defect has an explicit lower bound; no equidistribution is assumed. -/
theorem uniformDefect_one_lower (Q : ℕ) (hQ : 0 < Q) :
    (1 / 2 : ℝ) - 1 / (Q : ℝ) ≤ uniformDefect Q 1 := by
  have h := positiveWeight_le_progressionWeight Q 1 hQ
  norm_num [positiveWeight] at h
  unfold uniformDefect
  linarith

section Schur
open FiniteSchur
variable {ι : Type*} [Fintype ι]

/-- The actual tail Gram matrix, retaining every signed mixed entry. -/
def tailGram (Q N : ℕ) (z : ι → ℕ → ℝ) (i j : ι) : ℝ :=
  ∑ r : Fin Q, tailWeight Q N (r.val + 1) * z i (r.val + 1) * z j (r.val + 1)

theorem tailEnergy_combination (Q N : ℕ) (z : ι → ℕ → ℝ) (b : ι → ℝ) :
    tailEnergy Q N (combination z b) =
      ∑ i, ∑ j, b i * b j * tailGram Q N z i j := by
  unfold tailEnergy tailGram combination
  calc
    _ = ∑ r : Fin Q, ∑ i, ∑ j,
        b i * b j *
          (tailWeight Q N (r.val + 1) * z i (r.val + 1) * z j (r.val + 1)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]

/-- Redundant function columns removed: the genuine tail Gram form is positive.
Independence is stated as injectivity of synthesis on the complete residue chart. -/
theorem tailGram_positive (Q N : ℕ) (hQ : 0 < Q) (z : ι → ℕ → ℝ)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1)))
    (b : ι → ℝ) (hb : b ≠ 0) :
    0 < ∑ i, ∑ j, b i * b j * tailGram Q N z i j := by
  rw [← tailEnergy_combination]
  have hr : ∃ r : Fin Q, combination z b (r.val + 1) ≠ 0 := by
    by_contra! hn
    apply hb
    apply hi
    funext r
    simpa only [combination, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using hn r
  obtain ⟨r, hr⟩ := hr
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (le_of_lt (tailWeight_pos Q N (s.val + 1) hQ (by omega)))
      (sq_nonneg _)
  · exact ⟨r, Finset.mem_univ r,
      mul_pos (tailWeight_pos Q N (r.val + 1) hQ (by omega)) (sq_pos_of_ne_zero hr)⟩

/-- The linear action of the actual weighted tail Gram matrix. -/
def tailGramMap (Q N : ℕ) (z : ι → ℕ → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun b i := ∑ j, tailGram Q N z i j * b j
  map_add' b c := by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c b := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem tailGram_quadratic_eq (Q N : ℕ) (z : ι → ℕ → ℝ) (b : ι → ℝ) :
    (∑ i, ∑ j, b i * b j * tailGram Q N z i j) =
      ∑ i, b i * tailGramMap Q N z b i := by
  apply Finset.sum_congr rfl
  intro i _
  change _ = b i * ∑ j, tailGram Q N z i j * b j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tailGramMap_injective (Q N : ℕ) (hQ : 0 < Q) (z : ι → ℕ → ℝ)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1))) :
    Function.Injective (tailGramMap Q N z) := by
  intro b c hbc
  by_contra hne
  have hpos := tailGram_positive Q N hQ z hi (b - c) (sub_ne_zero.mpr hne)
  have hz : tailGramMap Q N z (b - c) = 0 := by rw [map_sub, hbc, sub_self]
  rw [tailGram_quadratic_eq, hz] at hpos
  simpa using hpos

/-- An inverse of the genuine tail Gram action exists after redundant columns
are removed. This is proved by positive definiteness and finite dimension. -/
def tailGramEquiv (Q N : ℕ) (hQ : 0 < Q) (z : ι → ℕ → ℝ)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1))) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofBijective (tailGramMap Q N z)
    ⟨tailGramMap_injective Q N hQ z hi,
      (LinearMap.injective_iff_surjective).mp (tailGramMap_injective Q N hQ z hi)⟩

theorem tailGramEquiv_apply (Q N : ℕ) (hQ : 0 < Q) (z : ι → ℕ → ℝ)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1)))
    (b : ι → ℝ) (i : ι) :
    tailGramEquiv Q N hQ z hi b i = tailGramMap Q N z b i := rfl

/-- A null head makes the full mixed Gram entry exactly its tail entry. -/
theorem nullHead_inner_eq_tailGram (Q N : ℕ) (hQ : 0 < Q)
    {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i)
    (hzp : ∀ i k, z i (k + Q) = z i k)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0) (i j : ι) :
    paretoInner (z i) (z j) = tailGram Q N z i j := by
  rw [periodic_paretoInner_mixed Q hQ (z i) (z j) (hz i) (hz j) (hzp i) (hzp j)]
  unfold tailGram
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.val + 1 ≤ N
  · simp [tailWeight, hr, hzh i (r.val + 1) (by omega) hr]
  · simp [tailWeight, hr, mul_assoc]

theorem tailGramEquiv_eq_gramApply (Q N : ℕ) (hQ : 0 < Q)
    {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i)
    (hzp : ∀ i k, z i (k + Q) = z i k)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1)))
    (b : ι → ℝ) (i : ι) :
    tailGramEquiv Q N hQ z hi b i = gramApply z b i := by
  rw [tailGramEquiv_apply]
  change (∑ j, tailGram Q N z i j * b j) = ∑ j, paretoInner (z i) (z j) * b j
  simp only [nullHead_inner_eq_tailGram Q N hQ hz hzp hzh]

theorem combination_periodic (Q : ℕ) (z : ι → ℕ → ℝ)
    (hzp : ∀ i k, z i (k + Q) = z i k) (b : ι → ℝ) :
    ∀ k, combination z b (k + Q) = combination z b k := by
  intro k
  simp only [combination, hzp]

theorem combination_nullHead (N : ℕ) (z : ι → ℕ → ℝ)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0) (b : ι → ℝ) :
    ∀ k, 0 < k → k ≤ N → combination z b k = 0 := by
  intro k hk hkN
  simp only [combination, hzh _ k hk hkN, mul_zero, Finset.sum_const_zero]

/-- Full affine Schur completion, expressed in the actual CRT tail form.
The normal equations are for all controls simultaneously. -/
theorem tail_schur_completion (Q N : ℕ) (hQ : 0 < Q) (hNQ : N ≤ Q)
    {f : ℕ → ℝ} {C : ℝ} {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ k, |f k| ≤ C) (hz : ∀ i k, |z i k| ≤ B i)
    (hfp : ∀ k, f (k + Q) = f k) (hzp : ∀ i k, z i (k + Q) = z i k)
    (hfh : ∀ k, 0 < k → k ≤ N → f k = 1)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0)
    (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f)
    (b : ι → ℝ) :
    tailEnergy Q N (fun k => f k - combination z b k) =
      tailEnergy Q N f - ∑ i, d i * paretoInner (z i) f +
      tailEnergy Q N (combination z (fun i => b i - d i)) := by
  have hbh := combination_nullHead N z hzh b
  have hbp := combination_periodic Q z hzp b
  have hres := norm_decomposition Q N hQ hNQ
    (fun k => f k - combination z b k)
    (bounded_sub hf (combination_bounded hz b))
    (by intro k; rw [hfp, hbp])
    (by intro k hk hkN; rw [hfh k hk hkN, hbh k hk hkN, sub_zero])
  have hbase := norm_decomposition Q N hQ hNQ f hf hfp hfh
  have hexcess := nullHead_norm Q N hQ (combination z (fun i => b i - d i))
    (combination_bounded hz _) (combination_periodic Q z hzp _)
    (combination_nullHead N z hzh _)
  have h := residual_completion hz hf d hd b
  rw [residual_schur_value hz hf d hd, hres, hbase, hexcess] at h
  linarith

/-- The CRT tail optimum uses the inverse of the genuine infinite Gram action. -/
theorem inverse_tail_value (Q N : ℕ) (hQ : 0 < Q) (hNQ : N ≤ Q)
    {f : ℕ → ℝ} {C : ℝ} {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ k, |f k| ≤ C) (hz : ∀ i k, |z i k| ≤ B i)
    (hfp : ∀ k, f (k + Q) = f k) (hzp : ∀ i k, z i (k + Q) = z i k)
    (hfh : ∀ k, 0 < k → k ≤ N → f k = 1)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) :
    tailEnergy Q N (fun k => f k - combination z (inverseCoeff e z f) k) =
      tailEnergy Q N f - ∑ i, inverseCoeff e z f i * cross z f i := by
  have h := tail_schur_completion Q N hQ hNQ hf hz hfp hzp hfh hzh
    (inverseCoeff e z f) (inverseCoeff_normal hz e he f) (inverseCoeff e z f)
  simpa [tailEnergy, combination, cross] using h

/-- Independent actual periodic controls provide both the Gram inverse and
the attained Schur minimum; invertibility is no longer a hypothesis. -/
theorem exists_inverse_tail_optimizer (Q N : ℕ) (hQ : 0 < Q) (hNQ : N ≤ Q)
    {f : ℕ → ℝ} {C : ℝ} {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hf : ∀ k, |f k| ≤ C) (hz : ∀ i k, |z i k| ≤ B i)
    (hfp : ∀ k, f (k + Q) = f k) (hzp : ∀ i k, z i (k + Q) = z i k)
    (hfh : ∀ k, 0 < k → k ≤ N → f k = 1)
    (hzh : ∀ i k, 0 < k → k ≤ N → z i k = 0)
    (hi : Function.Injective
      (fun b : ι → ℝ => fun r : Fin Q => combination z b (r.val + 1))) :
    ∃ e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ),
      (∀ b i, e b i = gramApply z b i) ∧
      tailEnergy Q N (fun k => f k - combination z (inverseCoeff e z f) k) =
        tailEnergy Q N f - ∑ i, inverseCoeff e z f i * cross z f i ∧
      ∀ b : ι → ℝ,
        tailEnergy Q N (fun k => f k - combination z (inverseCoeff e z f) k) ≤
          tailEnergy Q N (fun k => f k - combination z b k) := by
  let e := tailGramEquiv Q N hQ z hi
  have he : ∀ b i, e b i = gramApply z b i :=
    tailGramEquiv_eq_gramApply Q N hQ hz hzp hzh hi
  have hvalue := inverse_tail_value Q N hQ hNQ hf hz hfp hzp hfh hzh e he
  refine ⟨e, he, hvalue, ?_⟩
  intro b
  rw [tail_schur_completion Q N hQ hNQ hf hz hfp hzp hfh hzh
    (inverseCoeff e z f) (inverseCoeff_normal hz e he f) b, hvalue]
  exact le_add_of_nonneg_right (tailEnergy_nonneg Q N hQ _)

end Schur
end
end RiemannResearch.RH.Pareto.ExactHeadCRT

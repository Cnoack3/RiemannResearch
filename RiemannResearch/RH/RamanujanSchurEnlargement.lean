import RiemannResearch.RH.RamanujanOrthogonalScores
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.ParetoGramMeanOptimizer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Arbitrary-conductor Ramanujan Schur enlargement

Source: user-requested duality program, 23 October 2026.
Every new conductor outside the old finite set has positive Schur pivot.
The update is identified with the actual enlarged optimizer, so the exact
gain belongs to the actual mass and retains every complete Pareto tail.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanInnovation
open FiniteSchur RamanujanOptimizer

private theorem family_combination_nat (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    combination (family s) (fun i => c i.val) k =
      ∑ d ∈ s, c d * ramanujanPacket d k := by
  classical
  unfold combination family
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i _
    exact i.property
  · intro i _ j _ hij
    exact Subtype.ext hij
  · intro d hd
    exact ⟨⟨d, hd⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    rfl

/-- No ordering assumption on the new conductor is needed. -/
theorem pivot_pos_of_not_mem (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s) : 0 < pivot s hs q := by
  classical
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have hn : 0 ≤ pivot s hs q := paretoInner_self_nonneg _
  by_contra hpos
  have hz : pivot s hs q = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hvalues := (paretoInner_self_zero_iff_positive hC).mp hz
  have hzero : ∀ k, innovation s hs q k = 0 := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [innovation, fit, combination, family, ramanujanPacket, residue]
    · exact hvalues k (Nat.pos_of_ne_zero hk)
  let c : ℕ → ℝ := fun d => if d = q then 1 else
    if hd : d ∈ s then -(fitCoefficients s hs q ⟨d, hd⟩) else 0
  have hsum (k : ℕ) : (∑ d ∈ s, c d * ramanujanPacket d k) = -fit s hs q k := by
    rw [← family_combination_nat]
    change (∑ i : s, c i.val * ramanujanPacket i.val k) =
      -(∑ i : s, fitCoefficients s hs q i * ramanujanPacket i.val k)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hiq : i.val ≠ q := by
      intro h
      exact hqs (h ▸ i.property)
    simp [c, hiq, i.property]
  have hall (k : ℕ) : ∑ d ∈ insert q s, c d * ramanujanPacket d k = 0 := by
    rw [Finset.sum_insert hqs, hsum]
    simpa [c, innovation, sub_eq_add_neg] using hzero k
  have hc := ramanujanPacket_finite_independent (insert q s) c
    (by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hq
      · exact hs d hd) hall q (Finset.mem_insert_self _ _)
  norm_num [c] at hc

/-- The signed screened source is the actual old residual correlation. -/
theorem score_eq_raw_residual (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    score s hs q = paretoMean (ramanujanPacket q) -
      paretoInner (ramanujanPacket q) (projection s hs) := by
  have hf := combination_bounded (family_bounded s) (fitCoefficients s hs q)
  change ∀ k, |fit s hs q k| ≤ _ at hf
  have hp := combination_bounded (family_bounded s) (coefficients s hs)
  change ∀ k, |projection s hs k| ≤ _ at hp
  have ho := innovation_orthogonal s hs q (coefficients s hs)
  change paretoInner (fun k => ramanujanPacket q k - fit s hs q k)
    (projection s hs) = 0 at ho
  rw [paretoInner_sub_left (ramanujanPacket_abs_le q) hf hp] at ho
  have hm := projection_pairing (family_bounded s) (coefficients s hs)
    (fitCoefficients s hs q) (normal_equations s hs)
  change paretoInner (fit s hs q) (projection s hs) = paretoMean (fit s hs q) at hm
  have hscore := paretoMean_sub (ramanujanPacket_abs_le q) hf
  change score s hs q = paretoMean (ramanujanPacket q) - paretoMean (fit s hs q) at hscore
  linarith

theorem packet_innovation_inner (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    paretoInner (ramanujanPacket q) (innovation s hs q) = pivot s hs q := by
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have hf := combination_bounded (family_bounded s) (fitCoefficients s hs q)
  change ∀ k, |fit s hs q k| ≤ _ at hf
  have ho := innovation_orthogonal s hs q (fitCoefficients s hs q)
  rw [paretoInner_comm] at ho
  change paretoInner (fit s hs q) (innovation s hs q) = 0 at ho
  have h := paretoInner_sub_left (ramanujanPacket_abs_le q) hf hC
  change pivot s hs q = paretoInner (ramanujanPacket q) (innovation s hs q) -
    paretoInner (fit s hs q) (innovation s hs q) at h
  rw [ho, sub_zero] at h
  exact h.symm

theorem update_inner {f : ℕ → ℝ} {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (q : ℕ) :
    paretoInner f (update s hs q) = paretoInner f (projection s hs) +
      (score s hs q / pivot s hs q) * paretoInner f (innovation s hs q) := by
  obtain ⟨D, hD⟩ := innovation_bounded s hs q
  have hp := combination_bounded (family_bounded s) (coefficients s hs)
  change ∀ k, |projection s hs k| ≤ _ at hp
  have he : update s hs q = fun k => projection s hs k -
      (-(score s hs q / pivot s hs q)) * innovation s hs q k := by
    funext k
    unfold update
    ring
  rw [he, paretoInner_sub_right hf hp (bounded_const_mul hD _),
    paretoInner_const_mul_right hf hD]
  ring

/-- Exact error decrease for every new conductor, including smaller insertions. -/
theorem update_error_of_not_mem (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s) :
    paretoError (update s hs q) =
      1 - mass s hs - (score s hs q)^2 / pivot s hs q := by
  obtain ⟨C, hC⟩ := innovation_bounded s hs q
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have h := paretoInner_optimal_scalar_gain
    (r := fun k => 1 - projection s hs k) (g := innovation s hs q)
    (bounded_sub h1 (combination_bounded (family_bounded s) (coefficients s hs)))
    hC (ne_of_gt (pivot_pos_of_not_mem s hs q hq hqs))
    (score s hs q / pivot s hs q)
  rw [residual_score] at h
  change paretoInner
    (fun k => (1 - projection s hs k) - (score s hs q / pivot s hs q) * innovation s hs q k)
    (fun k => (1 - projection s hs k) - (score s hs q / pivot s hs q) * innovation s hs q k) =
      paretoError (projection s hs) - (score s hs q)^2 / pivot s hs q +
        pivot s hs q * (score s hs q / pivot s hs q - score s hs q / pivot s hs q)^2 at h
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
    projection_error] at h
  simpa only [paretoError, update, sub_add_eq_sub_sub] using h

theorem gain_le_error_of_not_mem (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s) :
    (score s hs q)^2 / pivot s hs q ≤ 1 - mass s hs := by
  have h : 0 ≤ paretoError (update s hs q) := paretoInner_self_nonneg _
  rw [update_error_of_not_mem s hs q hq hqs] at h
  linarith

/-- The exact Schur update has a legal coefficient vector in the enlarged family. -/
theorem update_is_combination (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hqs : q ∉ s) :
    ∃ b : ↥(insert q s) → ℝ,
      combination (family (insert q s)) b = update s hs q := by
  classical
  let t := score s hs q / pivot s hs q
  let c : ℕ → ℝ := fun d => if d = q then t else
    if hd : d ∈ s then coefficients s hs ⟨d, hd⟩ -
      t * fitCoefficients s hs q ⟨d, hd⟩ else 0
  have hcold : (fun i : s => c i.val) =
      fun i => coefficients s hs i - t * fitCoefficients s hs q i := by
    funext i
    have hiq : i.val ≠ q := by
      intro h
      exact hqs (h ▸ i.property)
    simp [c, hiq, i.property]
  have hcomb (k : ℕ) :
      combination (family s)
        (fun i => coefficients s hs i - t * fitCoefficients s hs q i) k =
      projection s hs k - t * fit s hs q k := by
    simp [combination, projection, fit, sub_mul, mul_assoc,
      Finset.sum_sub_distrib, Finset.mul_sum]
  refine ⟨fun i => c i.val, ?_⟩
  funext k
  rw [family_combination_nat, Finset.sum_insert hqs,
    ← family_combination_nat, hcold, hcomb]
  simp only [c, if_pos rfl]
  change t * ramanujanPacket q k + (projection s hs k - t * fit s hs q k) =
    projection s hs k + t * (ramanujanPacket q k - fit s hs q k)
  ring

theorem update_normal_of_not_mem (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s) (i : ↥(insert q s)) :
    paretoInner (family (insert q s) i) (update s hs q) =
      meanVector (insert q s) i := by
  have hf := combination_bounded (family_bounded s) (fitCoefficients s hs q)
  change ∀ k, |fit s hs q k| ≤ _ at hf
  have hold (j : s) : paretoInner (family s j) (update s hs q) = meanVector s j := by
    have ho : paretoInner (family s j) (innovation s hs q) = 0 := by
      change paretoInner (family s j)
        (fun k => ramanujanPacket q k - fit s hs q k) = 0
      rw [paretoInner_sub_right (family_bounded s j) (ramanujanPacket_abs_le q) hf,
        fit_normal, sub_self]
    rw [update_inner (family_bounded s j), normal_equations, ho, mul_zero, add_zero]
  by_cases hiq : i.val = q
  · change paretoInner (ramanujanPacket i.val) (update s hs q) =
      paretoMean (ramanujanPacket i.val)
    rw [hiq, update_inner (ramanujanPacket_abs_le q), packet_innovation_inner,
      div_mul_cancel₀ _ (ne_of_gt (pivot_pos_of_not_mem s hs q hq hqs))]
    linarith [score_eq_raw_residual s hs q]
  · have his : i.val ∈ s := (Finset.mem_insert.mp i.property).resolve_left hiq
    exact hold ⟨i.val, his⟩

/-- The Schur update equals the independently constructed enlarged Gram optimizer. -/
theorem projection_insert (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s)
    (hs' : ∀ d ∈ insert q s, 1 < d) :
    projection (insert q s) hs' = update s hs q := by
  obtain ⟨b, hb⟩ := update_is_combination s hs q hqs
  have hn : ramanujanGramAction (insert q s) b = meanVector (insert q s) := by
    funext i
    change gramApply (family (insert q s)) b i = meanVector (insert q s) i
    rw [gramApply_eq_inner (family_bounded (insert q s)), hb]
    exact update_normal_of_not_mem s hs q hq hqs i
  have hc : b = coefficients (insert q s) hs' := by
    apply ramanujanGramAction_injective (insert q s) hs'
    exact hn.trans (ramanujanGramSolve_normal_equations
      (insert q s) hs' (meanVector (insert q s))).symm
  rw [hc] at hb
  exact hb

/-- Exact gain in the actual optimizer mass, with the signed screened score. -/
theorem mass_insert (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s)
    (hs' : ∀ d ∈ insert q s, 1 < d) :
    mass (insert q s) hs' = mass s hs + (score s hs q)^2 / pivot s hs q := by
  have h := update_error_of_not_mem s hs q hq hqs
  rw [← projection_insert s hs q hq hqs hs', projection_error] at h
  linarith

/-- A new packet increases mass precisely when its screened source is nonzero. -/
theorem mass_insert_strict_iff (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (q : ℕ) (hq : 1 < q) (hqs : q ∉ s)
    (hs' : ∀ d ∈ insert q s, 1 < d) :
    mass s hs < mass (insert q s) hs' ↔ score s hs q ≠ 0 := by
  rw [mass_insert s hs q hq hqs hs']
  constructor
  · intro h hzero
    simp [hzero] at h
  · intro hscore
    have hgain : 0 < (score s hs q)^2 / pivot s hs q :=
      div_pos (sq_pos_of_ne_zero hscore) (pivot_pos_of_not_mem s hs q hq hqs)
    linarith

end RiemannResearch.RH.Pareto.RamanujanInnovation

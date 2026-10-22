import RiemannResearch.RH.ParetoPrimeDualNorm
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoDefectContinuity
import RiemannResearch.RH.ParetoApproximationRatio
import RiemannResearch.RH.ThresholdLegalIntegrability

/-!
# Local Möbius flow constraints on actual two-seed coefficients

Source: user-provided September 11, 2026 conversation, legal sequences and
Ramanujan continuation. The finite coefficients below synthesize the existing
legal integer dilations. All norms and error floors use the complete Pareto
sum. No convergence or uniform tail bound is asserted.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Actual finite synthesis with every dilation in S available. -/
def legalMobiusPacket (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ m ∈ S, c₂ m * dilation m (residue 2) n) +
  (∑ m ∈ S, c₃ m * dilation m (residue 3) n)

/-- Coefficient flow: outgoing floor coefficients minus incoming seed edges. -/
def legalMobiusFlow (a d : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, c m *
    ((if d = m then (m : ℝ) else 0) -
      (if d = m*a then ((m*a : ℕ) : ℝ) else 0))

theorem legalMobiusPacket_mem (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) :
    legalMobiusPacket S c₂ c₃ ∈ legalSeedSpan ({2,3} : Set ℕ) := by
  have hsum (a : ℕ) (ha : a ∈ ({2,3} : Set ℕ)) (c : ℕ → ℝ) :
      (∑ m ∈ S, c m • dilation m (residue a)) ∈
        legalSeedSpan ({2,3} : Set ℕ) := by
    apply (legalSeedSpan ({2,3} : Set ℕ)).sum_mem
    intro m hm
    exact (legalSeedSpan ({2,3} : Set ℕ)).smul_mem (c m)
      (dilation_generator_mem _ ha (hS m hm))
  have h := (legalSeedSpan ({2,3} : Set ℕ)).add_mem
    (hsum 2 (by simp) c₂) (hsum 3 (by simp) c₃)
  have he : legalMobiusPacket S c₂ c₃ =
      (∑ m ∈ S, c₂ m • dilation m (residue 2)) +
      (∑ m ∈ S, c₃ m • dilation m (residue 3)) := by
    funext n
    simp only [legalMobiusPacket, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply]
  rw [he]
  exact h

private theorem legalMobiusSeeds_pos : ∀ a ∈ ({2,3} : Set ℕ), 0 < a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> norm_num

theorem legalMobiusPacket_bounded (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) :
    ∃ C : ℝ, ∀ n, |legalMobiusPacket S c₂ c₃ n| ≤ C :=
  legalSeedSpan_bounded _ legalMobiusSeeds_pos (legalMobiusPacket_mem S c₂ c₃ hS)

theorem legalMobiusPacket_zero (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ) :
    legalMobiusPacket S c₂ c₃ 0 = 0 := by
  simp [legalMobiusPacket, dilation, residue]

/-- The exact floor-function formula for one actual legal generator. -/
theorem legalMobiusGenerator_floor (a m n : ℕ) :
    dilation m (residue a) n =
      (m : ℝ) * (n / m : ℕ) - ((m*a : ℕ) : ℝ) * (n / (m*a) : ℕ) := by
  rw [residue_mul_floor]
  have h₁ := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div n m)
  have h₂ := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div n (m*a))
  simp only [Nat.cast_add, Nat.cast_mul] at h₁ h₂ ⊢
  unfold residue
  linarith

theorem legalMobiusGenerator_difference (a m d : ℕ) (hd : 1 < d) :
    mobiusDifference d (dilation m (residue a)) =
      (if d = m then (m : ℝ) else 0) -
      (if d = m*a then ((m*a : ℕ) : ℝ) else 0) := by
  have he : dilation m (residue a) =
      (fun n => residue (m*a) n - residue m n) := by
    funext n
    exact residue_mul_floor m a n
  rw [he, mobiusDifference_sub_fn, mobiusDifference_residue _ _ hd,
    mobiusDifference_residue _ _ hd]
  split_ifs <;> ring

/-- The page's coefficient recurrence, with finite support kept explicit. -/
theorem legalMobiusPacket_difference (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (d : ℕ) (hd : 1 < d) :
    mobiusDifference d (legalMobiusPacket S c₂ c₃) =
      legalMobiusFlow 2 d S c₂ + legalMobiusFlow 3 d S c₃ := by
  unfold legalMobiusPacket
  rw [mobiusDifference_add_fn, mobiusDifference_sum, mobiusDifference_sum]
  simp only [legalMobiusGenerator_difference _ _ _ hd, legalMobiusFlow]

/-- Any successful actual legal sequence has the local Möbius flow limits. -/
theorem legalMobiusFlow_tendsto (S : ℕ → Finset ℕ) (c₂ c₃ : ℕ → ℕ → ℝ)
    (hS : ∀ j m, m ∈ S j → 0 < m)
    (herr : Tendsto (fun j => paretoError (legalMobiusPacket (S j) (c₂ j) (c₃ j)))
      atTop (nhds 0)) (d : ℕ) (hd : 1 < d) :
    Tendsto (fun j => legalMobiusFlow 2 d (S j) (c₂ j) +
      legalMobiusFlow 3 d (S j) (c₃ j))
      atTop (nhds (ArithmeticFunction.moebius d : ℝ)) := by
  have h := paretoError_tendsto_mobiusDifference
    (fun j => legalMobiusPacket_bounded (S j) (c₂ j) (c₃ j) (hS j))
    (fun j => legalMobiusPacket_zero (S j) (c₂ j) (c₃ j)) herr d (by omega)
  simpa only [legalMobiusPacket_difference _ _ _ _ hd] using h

/-- At indices not divisible by the seed, there is no incoming edge. -/
theorem legalMobiusFlow_no_incoming (a p : ℕ) (ha : ¬ a ∣ p)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    legalMobiusFlow a p S c = (p : ℝ) * (if p ∈ S then c p else 0) := by
  have hmul (m : ℕ) : p ≠ m*a := by
    intro h
    apply ha
    rw [h]
    exact dvd_mul_left a m
  unfold legalMobiusFlow
  simp only [if_neg (hmul _), sub_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> ring

/-- The remaining Möbius coordinate at one, including its anchor. -/
theorem legalMobiusPacket_difference_one (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ) :
    mobiusDifference 1 (legalMobiusPacket S c₂ c₃) =
      (if 1 ∈ S then c₂ 1 else 0) + (if 1 ∈ S then c₃ 1 else 0) := by
  have hg (a m : ℕ) (ha : 1 < a) :
      dilation m (residue a) 1 = if 1 = m then 1 else 0 := by
    by_cases hm0 : m = 0
    · subst m
      simp [dilation]
    by_cases hm1 : m = 1
    · subst m
      simp [dilation, residue, Nat.mod_eq_of_lt ha]
    have hm : 1 < m := by omega
    simp [dilation, residue, Nat.div_eq_of_lt hm, Ne.symm hm1]
  have hmd : mobiusDifference 1 (legalMobiusPacket S c₂ c₃) =
      legalMobiusPacket S c₂ c₃ 1 := by
    norm_num [mobiusDifference, legalMobiusPacket_zero]
  rw [hmd]
  simp only [legalMobiusPacket, hg 2 _ (by decide), hg 3 _ (by decide),
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]

/-- The positive unit coordinate requires the total first coefficient to approach one. -/
theorem legalMobiusPacket_one_coeff_tendsto
    (S : ℕ → Finset ℕ) (c₂ c₃ : ℕ → ℕ → ℝ)
    (hS : ∀ j m, m ∈ S j → 0 < m)
    (herr : Tendsto (fun j => paretoError (legalMobiusPacket (S j) (c₂ j) (c₃ j)))
      atTop (nhds 0)) :
    Tendsto (fun j => (if 1 ∈ S j then c₂ j 1 else 0) +
      (if 1 ∈ S j then c₃ j 1 else 0)) atTop (nhds 1) := by
  have h := paretoError_tendsto_mobiusDifference
    (fun j => legalMobiusPacket_bounded (S j) (c₂ j) (c₃ j) (hS j))
    (fun j => legalMobiusPacket_zero (S j) (c₂ j) (c₃ j)) herr 1 (by decide)
  simpa [legalMobiusPacket_difference_one] using h

/-- Every prime away from the two seeds requires a coefficient limit -1/p. -/
theorem legalMobiusPacket_prime_coeff_tendsto
    (S : ℕ → Finset ℕ) (c₂ c₃ : ℕ → ℕ → ℝ)
    (hS : ∀ j m, m ∈ S j → 0 < m)
    (herr : Tendsto (fun j => paretoError (legalMobiusPacket (S j) (c₂ j) (c₃ j)))
      atTop (nhds 0)) (p : ℕ) (hp : p.Prime)
    (h₂ : ¬ 2 ∣ p) (h₃ : ¬ 3 ∣ p) :
    Tendsto (fun j => (if p ∈ S j then c₂ j p else 0) +
      (if p ∈ S j then c₃ j p else 0)) atTop (nhds (-(1 : ℝ) / p)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := (legalMobiusFlow_tendsto S c₂ c₃ hS herr p hp.one_lt).div_const (p : ℝ)
  simp only [legalMobiusFlow_no_incoming 2 p h₂,
    legalMobiusFlow_no_incoming 3 p h₃,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one] at h
  have he (x y : ℝ) : ((p : ℝ)*x + (p : ℝ)*y)/(p : ℝ) = x+y := by
    field_simp [hp0]
  simpa only [he] using h

/-- Prime coefficient obstruction in squared form with the exact dual constant. -/
theorem legalMobiusPacket_prime_sq_bound (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (h₂ : ¬ 2 ∣ p) (h₃ : ¬ 3 ∣ p) :
    ((p : ℝ) * ((if p ∈ S then c₂ p else 0) +
        (if p ∈ S then c₃ p else 0)) + 1)^2 ≤
      2 * ((p : ℝ)^2 + 1) * paretoError (legalMobiusPacket S c₂ c₃) := by
  let f := legalMobiusPacket S c₂ c₃
  have hf := legalSeedSpan_error_summable _ legalMobiusSeeds_pos
    (legalMobiusPacket_mem S c₂ c₃ hS)
  have h := prime_dual_full_sq_bound p hp3 (fun n => 1 - f n) hf
  have hid := legalMobiusPacket_difference S c₂ c₃ p hp.one_lt
  rw [mobiusDifference_prime p hp _ (legalMobiusPacket_zero S c₂ c₃),
    legalMobiusFlow_no_incoming 2 p h₂,
    legalMobiusFlow_no_incoming 3 p h₃] at hid
  change ((1-f p) - (1-f (p-1)) - (1-f 1))^2 ≤
    2 * ((p : ℝ)^2 + 1) * paretoError f at h
  have he : (1-f p) - (1-f (p-1)) - (1-f 1) =
      -((p : ℝ) * ((if p ∈ S then c₂ p else 0) +
        (if p ∈ S then c₃ p else 0)) + 1) := by
    dsimp [f] at *
    linarith [hid]
  rw [he, neg_sq] at h
  exact h

/-- Omitting dilation five forces a full-tail squared error of at least 1/52. -/
theorem legalMobiusPacket_omit_five_error_floor (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) (hfive : 5 ∉ S) :
    (1 : ℝ) / 52 ≤ paretoError (legalMobiusPacket S c₂ c₃) := by
  have h := legalMobiusPacket_prime_sq_bound S c₂ c₃ hS 5
    (by decide) (by decide) (by decide) (by decide)
  norm_num [hfive] at h
  linarith

/-- The same error floor is a variance floor under the actual mean-one constraint. -/
theorem legalMobiusPacket_omit_five_variance_floor (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m) (hfive : 5 ∉ S)
    (hmean : paretoMean (legalMobiusPacket S c₂ c₃) = 1) :
    (1 : ℝ) / 52 ≤ paretoVariance (legalMobiusPacket S c₂ c₃) := by
  obtain ⟨C,hC⟩ := legalMobiusPacket_bounded S c₂ c₃ hS
  have h := legalMobiusPacket_omit_five_error_floor S c₂ c₃ hS hfive
  simpa [paretoError_eq_variance_add_bias_sq hC, hmean] using h

/-- Nonnegative coefficients cannot satisfy the required negative prime defect. -/
theorem legalMobiusPacket_nonnegative_error_floor (S : Finset ℕ) (c₂ c₃ : ℕ → ℝ)
    (hS : ∀ m ∈ S, 0 < m)
    (h₂ : ∀ m ∈ S, 0 ≤ c₂ m) (h₃ : ∀ m ∈ S, 0 ≤ c₃ m) :
    (1 : ℝ) / 52 ≤ paretoError (legalMobiusPacket S c₂ c₃) := by
  have h := legalMobiusPacket_prime_sq_bound S c₂ c₃ hS 5
    (by decide) (by decide) (by decide) (by decide)
  have hc₂ : 0 ≤ (if 5 ∈ S then c₂ 5 else 0) := by
    split_ifs with hh
    · exact h₂ 5 hh
    · rfl
  have hc₃ : 0 ≤ (if 5 ∈ S then c₃ 5 else 0) := by
    split_ifs with hh
    · exact h₃ 5 hh
    · rfl
  norm_num at h
  nlinarith [sq_nonneg ((if 5 ∈ S then c₂ 5 else 0) +
    (if 5 ∈ S then c₃ 5 else 0))]

end
end RiemannResearch.RH.Pareto

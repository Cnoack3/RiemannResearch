import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoFiniteCertificates
import RiemannResearch.RH.ParetoPrimorialObstruction

/-!
Source: user-provided Pareto CRT research note §§5-6. This module discharges
absolute summability for actual packet combinations and lifts finite certificates
to the complete Pareto error. It also excludes nonzero linear sequences from
the weighted square-summable space.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem residue_abs_le (n k : ℕ) (hn : 0 < n) : |residue n k| ≤ (n : ℝ) := by
  unfold residue
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.mod_lt k hn).le

theorem ramanujanPacket_abs_le (q k : ℕ) :
    |ramanujanPacket q k| ≤ ∑ d ∈ q.divisors,
      |(ArithmeticFunction.moebius (q/d) : ℝ)| * (d : ℝ) := by
  unfold ramanujanPacket
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro d hd
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (residue_abs_le d k (Nat.pos_of_mem_divisors hd))
    (abs_nonneg _)

theorem packetCombination_bounded (s : Finset ℕ) (c : ℕ → ℝ) :
    ∃ C : ℝ, ∀ k, |∑ q ∈ s, c q * ramanujanPacket q k| ≤ C := by
  refine ⟨∑ q ∈ s, |c q| * (∑ d ∈ q.divisors,
    |(ArithmeticFunction.moebius (q/d) : ℝ)| * (d : ℝ)), ?_⟩
  intro k
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro q hq
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (ramanujanPacket_abs_le q k) (abs_nonneg _)

theorem error_square_bounded {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) :
    ∀ k, |(1-f k)^2| ≤ (1+C)^2 := by
  intro k
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC k)
  rw [abs_of_nonneg (sq_nonneg _)]
  have hb : |1-f k| ≤ 1+C := by
    calc
      _ ≤ |(1 : ℝ)| + |f k| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (1 : ℝ) 0 (f k)
      _ ≤ _ := by simpa using add_le_add (le_refl (1 : ℝ)) (hC k)
  nlinarith [sq_abs (1-f k), abs_nonneg (1-f k)]

/-- Full-tail finite real packet combinations always have a finite squared error. -/
theorem packetCombination_error_summable (s : Finset ℕ) (c : ℕ → ℝ) :
    Summable (fun k => positiveWeight k * (1-∑ q ∈ s, c q*ramanujanPacket q k)^2) := by
  obtain ⟨C,hC⟩ := packetCombination_bounded s c
  exact weighted_summable_of_bounded (error_square_bounded hC)

/-- The previously finite certificate now bounds the genuine infinite Pareto norm. -/
theorem primePowerCombination_full_error_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ p a, p.Prime ∧ q = p^a) :
    (3562158 : ℝ) / 256250081 ≤
      ∑' k, positiveWeight k * (1-∑ q ∈ s, c q*ramanujanPacket q k)^2 := by
  have h := primePowerCombination_error_floor s c hs
  have hfinite : (∑ k : Fin 15,
      (1-∑ q ∈ s, c q*ramanujanPacket q (k+1))^2 / (coordinateWeight k : ℝ)) =
      ∑ k ∈ Finset.Ico 1 16, positiveWeight k *
        (1-∑ q ∈ s, c q*ramanujanPacket q k)^2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num only [Nat.reduceSub]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    unfold coordinateWeight positiveWeight
    push_cast
    simp only [Nat.add_comm 1]
    ring
  rw [hfinite] at h
  exact le_trans h ((packetCombination_error_summable s c).sum_le_tsum
    (Finset.Ico 1 16) (fun k hk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)))

/-- A square-summable linear sequence for the Pareto weights must be zero. -/
theorem linear_square_summable_iff (c : ℝ) :
    Summable (fun k => positiveWeight k * (c * (k : ℝ))^2) ↔ c = 0 := by
  constructor
  · intro hs
    have hshift := (summable_nat_add_iff 1).mpr hs
    have hconst : Summable (fun _ : ℕ => c^2 / 2) := by
      apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hshift
      intro k
      unfold positiveWeight
      push_cast
      have hk1 : (k : ℝ)+1 > 0 := by positivity
      have hk2 : (k : ℝ)+2 > 0 := by positivity
      rw [show (k : ℝ)+1+1 = (k : ℝ)+2 by ring]
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ (mul_pos hk1 hk2)).mpr
      nlinarith [mul_nonneg (sq_nonneg c) (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hk1.le)]
    have hz : c^2 / 2 = 0 := (summable_const_iff (c^2 / 2)).mp hconst
    nlinarith [sq_nonneg c]
  · rintro rfl
    simp

end
end RiemannResearch.RH.Pareto

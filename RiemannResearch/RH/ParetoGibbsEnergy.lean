import RiemannResearch.RH.ParetoGibbsOperator

/-!
# Exact Gibbs energy identities on the full weighted Hilbert space

All hypotheses are genuine weighted-square-summability hypotheses. The complete
product-index sums and mixed terms are retained. Fixed vectors are proved to be
constants from strict positivity of the actual transition kernel.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem gibbs_product_left_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * f p.1) := by
  have hs := (gibbs_product_summable hf).comp_injective (Equiv.prodComm ℕ ℕ).injective
  change Summable (fun p : ℕ × ℕ => geometricKernel p.2 p.1 * f p.1) at hs
  exact hs.congr (fun p => by rw [geometricKernel_symm p.2 p.1])

theorem gibbs_product_left_tsum {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * f p.1) =
      ∑' n, paretoWeight n * f n := by
  rw [(gibbs_product_left_summable hf).tsum_prod]
  simp_rw [tsum_mul_right, geometricKernel_tsum]

/-- Full mixed-product convergence follows from the two weighted square sums. -/
theorem gibbs_cross_summable {f g : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2))
    (hg : Summable (fun n => paretoWeight n * g n ^ 2)) :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * (f p.1 * g p.2)) := by
  have hA := gibbs_product_left_summable (f := fun n => f n ^ 2)
    (by simpa only [abs_sq] using hf)
  have hB := gibbs_product_summable (f := fun n => g n ^ 2)
    (by simpa only [abs_sq] using hg)
  apply (hA.add hB).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (geometricKernel_pos p.1 p.2).le]
  have hab : |f p.1 * g p.2| ≤ f p.1 ^ 2 + g p.2 ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|f p.1| - |g p.2|), sq_abs (f p.1), sq_abs (g p.2)]
  nlinarith [mul_le_mul_of_nonneg_left hab (geometricKernel_pos p.1 p.2).le]

/-- The infinite kernel form equals the actual weighted operator pairing. -/
theorem gibbs_cross_tsum {f g : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2))
    (hg : Summable (fun n => paretoWeight n * g n ^ 2)) :
    (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 * g p.2)) =
      ∑' n, paretoWeight n * (f n * gibbsAction g n) := by
  rw [(gibbs_cross_summable hf hg).tsum_prod]
  apply tsum_congr
  intro n
  calc
    _ = f n * (∑' m, geometricKernel n m * g m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      ring
    _ = _ := by rw [← gibbsAction_weight_mul g n]; ring

/-- Symmetry of the actual kernel gives self-adjointness on the whole weighted space. -/
theorem gibbsAction_pairing_symm {f g : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2))
    (hg : Summable (fun n => paretoWeight n * g n ^ 2)) :
    (∑' n, paretoWeight n * (f n * gibbsAction g n)) =
      ∑' n, paretoWeight n * (g n * gibbsAction f n) := by
  have hX := gibbs_cross_summable hf hg
  have hY := gibbs_cross_summable hg hf
  rw [← gibbs_cross_tsum hf hg, ← gibbs_cross_tsum hg hf,
    hX.tsum_prod, ← Summable.tsum_comm hX, hY.tsum_prod]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro m
  rw [geometricKernel_symm]
  ring

/-- Every term of the full Dirichlet energy is absolutely summable on H. -/
theorem gibbs_dirichlet_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) := by
  have habs : Summable (fun n => paretoWeight n * |f n ^ 2|) := by
    simpa only [abs_sq] using hf
  apply (((gibbs_product_left_summable habs).add (gibbs_product_summable habs)).sub
    ((gibbs_cross_summable hf hf).mul_left 2)).congr
  intro p
  ring

/-- Exact full-H Dirichlet identity, with no boundedness restriction. -/
theorem gibbs_dirichlet_identity {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    (1 / 2 : ℝ) * (∑' p : ℕ × ℕ,
      geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) =
        (∑' n, paretoWeight n * f n ^ 2) -
          ∑' n, paretoWeight n * (f n * gibbsAction f n) := by
  have habs : Summable (fun n => paretoWeight n * |f n ^ 2|) := by
    simpa only [abs_sq] using hf
  have hA := gibbs_product_left_summable habs
  have hB := gibbs_product_summable habs
  have hX := gibbs_cross_summable hf hf
  have he (p : ℕ × ℕ) : geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2 =
      (geometricKernel p.1 p.2 * f p.1 ^ 2 + geometricKernel p.1 p.2 * f p.2 ^ 2) -
        2 * (geometricKernel p.1 p.2 * (f p.1 * f p.2)) := by ring
  simp_rw [he]
  rw [(hA.add hB).tsum_sub (hX.mul_left 2), hA.tsum_add hB, hX.tsum_mul_left,
    gibbs_product_left_tsum habs, gibbs_product_tsum habs, gibbs_cross_tsum hf hf]
  ring

/-- The complete conditional-variance loss is summable for every vector of H. -/
theorem gibbs_conditional_loss_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    Summable (fun p : ℕ × ℕ =>
      geometricKernel p.1 p.2 * (f p.2 - gibbsAction f p.1) ^ 2) := by
  have hp := gibbsAction_square_summable hf
  have hA := gibbs_product_left_summable (f := fun n => gibbsAction f n ^ 2)
    (by simpa only [abs_sq] using hp)
  have hB := gibbs_product_summable (f := fun n => f n ^ 2)
    (by simpa only [abs_sq] using hf)
  apply ((hA.add hB).sub ((gibbs_cross_summable hp hf).mul_left 2)).congr
  intro p
  ring

/-- Exact full weighted norm loss under one Gibbs step. -/
theorem gibbs_conditional_loss_identity {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    (∑' n, paretoWeight n * f n ^ 2) -
        (∑' n, paretoWeight n * gibbsAction f n ^ 2) =
      ∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.2 - gibbsAction f p.1) ^ 2 := by
  have hp := gibbsAction_square_summable hf
  have ha : Summable (fun n => paretoWeight n * |gibbsAction f n ^ 2|) := by
    simpa only [abs_sq] using hp
  have hb : Summable (fun n => paretoWeight n * |f n ^ 2|) := by
    simpa only [abs_sq] using hf
  have hA := gibbs_product_left_summable ha
  have hB := gibbs_product_summable hb
  have hX := gibbs_cross_summable hp hf
  have he (p : ℕ × ℕ) : geometricKernel p.1 p.2 * (f p.2 - gibbsAction f p.1) ^ 2 =
      (geometricKernel p.1 p.2 * gibbsAction f p.1 ^ 2 + geometricKernel p.1 p.2 * f p.2 ^ 2) -
        2 * (geometricKernel p.1 p.2 * (gibbsAction f p.1 * f p.2)) := by ring
  simp_rw [he]
  rw [(hA.add hB).tsum_sub (hX.mul_left 2), hA.tsum_add hB, hX.tsum_mul_left,
    gibbs_product_left_tsum ha, gibbs_product_tsum hb, gibbs_cross_tsum hp hf]
  simp only [← pow_two]
  ring

/-- Strict positivity of every transition forces all fixed vectors to be constants. -/
theorem gibbsAction_fixed_iff_constant {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    gibbsAction f = f ↔ ∃ c : ℝ, f = fun _ => c := by
  constructor
  · intro hfix
    have he := gibbs_dirichlet_identity hf
    rw [hfix] at he
    simp only [← pow_two, sub_self] at he
    have hz : (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) = 0 := by
      linarith
    refine ⟨f 0, ?_⟩
    funext n
    have hb := (gibbs_dirichlet_summable hf).le_tsum (n, 0)
      (fun p hp => mul_nonneg (geometricKernel_pos p.1 p.2).le (sq_nonneg _))
    rw [hz] at hb
    have hn : geometricKernel n 0 * (f n - f 0) ^ 2 = 0 :=
      le_antisymm hb (mul_nonneg (geometricKernel_pos n 0).le (sq_nonneg _))
    have hs : (f n - f 0) ^ 2 = 0 :=
      (mul_eq_zero.mp hn).resolve_left (ne_of_gt (geometricKernel_pos n 0))
    nlinarith [sq_nonneg (f n - f 0)]
  · rintro ⟨c, rfl⟩
    exact gibbsAction_const c

/-- Equality in the full norm contraction occurs exactly for constants. -/
theorem gibbsAction_square_eq_iff_constant {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    (∑' n, paretoWeight n * gibbsAction f n ^ 2) =
        (∑' n, paretoWeight n * f n ^ 2) ↔
      ∃ c : ℝ, f = fun _ => c := by
  constructor
  · intro heq
    have he := gibbs_conditional_loss_identity hf
    rw [heq, sub_self] at he
    have hz : (∑' p : ℕ × ℕ,
        geometricKernel p.1 p.2 * (f p.2 - gibbsAction f p.1) ^ 2) = 0 := he.symm
    refine ⟨gibbsAction f 0, ?_⟩
    funext n
    have hb := (gibbs_conditional_loss_summable hf).le_tsum (0, n)
      (fun p hp => mul_nonneg (geometricKernel_pos p.1 p.2).le (sq_nonneg _))
    rw [hz] at hb
    have hn : geometricKernel 0 n * (f n - gibbsAction f 0) ^ 2 = 0 :=
      le_antisymm hb (mul_nonneg (geometricKernel_pos 0 n).le (sq_nonneg _))
    have hs : (f n - gibbsAction f 0) ^ 2 = 0 :=
      (mul_eq_zero.mp hn).resolve_left (ne_of_gt (geometricKernel_pos 0 n))
    nlinarith [sq_nonneg (f n - gibbsAction f 0)]
  · rintro ⟨c, rfl⟩
    rw [gibbsAction_const]

/-- Every nonconstant vector loses strictly positive full weighted energy.
This is a vectorwise strict inequality, not a uniform spectral-gap estimate. -/
theorem gibbsAction_square_lt_of_nonconstant {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2))
    (hnc : ¬ ∃ c : ℝ, f = fun _ => c) :
    (∑' n, paretoWeight n * gibbsAction f n ^ 2) <
      ∑' n, paretoWeight n * f n ^ 2 := by
  exact lt_of_le_of_ne (gibbsAction_square_contraction hf)
    (fun heq => hnc ((gibbsAction_square_eq_iff_constant hf).mp heq))

end
end RiemannResearch.RH.Pareto

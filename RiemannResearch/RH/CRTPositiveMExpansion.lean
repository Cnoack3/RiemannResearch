import RiemannResearch.RH.CRTExactSignedEnergy

/-!
# A direct positive expansion of the quadratic CRT weight
Source: user-provided CRT handoff, Sections 12--14, and the finite geometric
identity (1-z)^(-1)(1-z^2)^(-1). The argument below is developed here.
This module does not assert subpolynomial arithmetic energy.
-/
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
noncomputable section

def mMidpointTerm (j : ℕ) (t : ℝ) : ℝ :=
  2 * ((j : ℝ) + 1) *
    (1 / (t + 1)^(2*j+4) + 1 / (t + 1)^(2*j+5))

def mMidpointRemainder (N : ℕ) (t : ℝ) : ℝ :=
  ((N : ℝ) + 1 - (N : ℝ) / (t+1)^2) *
    (lKernel t / t) / (t+1)^(2*N)

def mMidpointApprox (Q r : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑' k : ℕ, mMidpointTerm j (Q*k+r)

def mMidpointTail (Q r : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, mMidpointRemainder N (Q*k+r)

/-- Exact finite-series remainder step; no asymptotic expansion is used. -/
theorem mMidpointRemainder_step (N : ℕ) {t : ℝ} (ht : 0 < t) :
    mMidpointRemainder N t =
      mMidpointTerm N t + mMidpointRemainder (N+1) t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t+1 ≠ 0 := by positivity
  have h2 : t+2 ≠ 0 := by positivity
  unfold mMidpointRemainder mMidpointTerm lKernel
  simp only [Nat.cast_add, Nat.cast_one, Nat.mul_add, Nat.mul_one, pow_add]
  field_simp
  ring

theorem mMidpointRemainder_pos (N : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < mMidpointRemainder N t := by
  have hd : (N : ℝ) / (t+1)^2 ≤ N :=
    div_le_self (Nat.cast_nonneg N) (by nlinarith)
  have hc : 0 < (N : ℝ) + 1 - (N : ℝ) / (t+1)^2 := by linarith
  unfold mMidpointRemainder lKernel
  positivity

theorem mMidpointRemainder_le (N : ℕ) {t : ℝ} (ht : 0 < t) :
    mMidpointRemainder N t ≤ ((N : ℝ)+1) * (lKernel t / t) := by
  have hk : 0 ≤ lKernel t / t := by unfold lKernel; positivity
  have hc : (N : ℝ)+1-(N : ℝ)/(t+1)^2 ≤ (N : ℝ)+1 := by
    have : 0 ≤ (N : ℝ)/(t+1)^2 := by positivity
    linarith
  unfold mMidpointRemainder
  calc
    _ ≤ (((N : ℝ)+1) * (lKernel t / t)) / (t+1)^(2*N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hk) (by positivity)
    _ ≤ _ := div_le_self (by positivity)
      (one_le_pow₀ (show 1 ≤ t+1 by linarith))

theorem mMidpointRemainder_summable (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => mMidpointRemainder N (Q*k+r)) :=
  ((progressionM_summable hQ hr).mul_left ((N : ℝ)+1)).of_nonneg_of_le
    (fun k => (mMidpointRemainder_pos N (by positivity)).le)
    (fun k => mMidpointRemainder_le N (by positivity))

theorem mMidpointTerm_summable (j : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => mMidpointTerm j (Q*k+r)) := by
  apply (mMidpointRemainder_summable j hQ hr).of_nonneg_of_le
  · intro k
    unfold mMidpointTerm
    positivity
  · intro k
    have hs := mMidpointRemainder_step j (show 0 < Q*(k : ℝ)+r by positivity)
    have hp := mMidpointRemainder_pos (j+1) (show 0 < Q*(k : ℝ)+r by positivity)
    linarith

theorem mMidpointTail_step (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    mMidpointTail Q r N = (∑' k : ℕ, mMidpointTerm N (Q*k+r)) +
      mMidpointTail Q r (N+1) := by
  calc
    _ = ∑' k : ℕ, (mMidpointTerm N (Q*k+r) +
      mMidpointRemainder (N+1) (Q*k+r)) :=
        tsum_congr (fun k => mMidpointRemainder_step N (by positivity))
    _ = _ := (mMidpointTerm_summable N hQ hr).tsum_add
      (mMidpointRemainder_summable (N+1) hQ hr)

/-- The actual quadratic progression weight equals its positive core plus tail. -/
theorem progressionM_midpoint_exact (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    progressionM Q r = mMidpointApprox Q r N + mMidpointTail Q r N := by
  induction N with
  | zero => simp [mMidpointApprox, mMidpointTail, mMidpointRemainder, progressionM]
  | succ N ih =>
    have ha : mMidpointApprox Q r (N+1) = mMidpointApprox Q r N +
        (∑' k : ℕ, mMidpointTerm N (Q*k+r)) := by
      simp [mMidpointApprox, Finset.sum_range_succ]
    rw [ha, add_assoc, ← mMidpointTail_step N hQ hr]
    exact ih

theorem mMidpointTail_pos (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    0 < mMidpointTail Q r N :=
  (mMidpointRemainder_summable N hQ hr).tsum_pos
    (fun k => (mMidpointRemainder_pos N (by positivity)).le) 0
    (mMidpointRemainder_pos N (by positivity))

theorem mMidpointRemainder_relative (N : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    mMidpointRemainder N t ≤
      (((N : ℝ)+1) / (4 : ℝ)^N) * (lKernel t / t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hk : 0 ≤ lKernel t / t := by unfold lKernel; positivity
  have hc : (N : ℝ)+1-(N : ℝ)/(t+1)^2 ≤ (N : ℝ)+1 := by
    have : 0 ≤ (N : ℝ)/(t+1)^2 := by positivity
    linarith
  have hp : (4 : ℝ)^N ≤ (t+1)^(2*N) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by nlinarith) N
  unfold mMidpointRemainder
  calc
    _ ≤ (((N : ℝ)+1) * (lKernel t / t)) / (t+1)^(2*N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hk) (by positivity)
    _ ≤ (((N : ℝ)+1) * (lKernel t / t)) / (4 : ℝ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by ring

theorem mMidpointTail_relative (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) :
    mMidpointTail Q r N ≤
      (((N : ℝ)+1) / (4 : ℝ)^N) * progressionM Q r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  unfold mMidpointTail progressionM
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (mMidpointRemainder_summable N hQ hr0)
    ((progressionM_summable hQ hr0).mul_left _)
  intro k
  apply mMidpointRemainder_relative N
  have hk : 0 ≤ Q*(k : ℝ) := by positivity
  linarith

def positiveMCore (Q N : ℕ) (B : Fin Q → ℝ) : ℝ :=
  ∑ r : Fin Q, mMidpointApprox Q (r.val+1) N * (B r)^2

def positiveMTail (Q N : ℕ) (B : Fin Q → ℝ) : ℝ :=
  ∑ r : Fin Q, mMidpointTail Q (r.val+1) N * (B r)^2

/-- B may be any signed affine combination of actual CRT defects. -/
theorem positiveM_quadratic_exact (Q : ℕ) (hQ : 0 < Q) (N : ℕ) (B : Fin Q → ℝ) :
    (∑ r : Fin Q, progressionM Q (r.val+1) * (B r)^2) =
      positiveMCore Q N B + positiveMTail Q N B := by
  unfold positiveMCore positiveMTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [progressionM_midpoint_exact N (by exact_mod_cast hQ) (by positivity)]
  ring

theorem positiveMTail_nonneg (Q : ℕ) (hQ : 0 < Q) (N : ℕ) (B : Fin Q → ℝ) :
    0 ≤ positiveMTail Q N B := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (mMidpointTail_pos N (by exact_mod_cast hQ) (by positivity)).le
    (sq_nonneg _)

theorem positiveMTail_relative (Q : ℕ) (hQ : 0 < Q) (N : ℕ) (B : Fin Q → ℝ) :
    positiveMTail Q N B ≤ (((N : ℝ)+1) / (4 : ℝ)^N) *
      (∑ r : Fin Q, progressionM Q (r.val+1) * (B r)^2) := by
  unfold positiveMTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have h := mul_le_mul_of_nonneg_right
    (mMidpointTail_relative N (Q := (Q : ℝ)) (r := (r.val : ℝ)+1) (by exact_mod_cast hQ)
      (show (1 : ℝ) ≤ (r.val : ℝ)+1 by have := Nat.cast_nonneg r.val (α := ℝ); linarith))
    (sq_nonneg (B r))
  simpa only [mul_assoc] using h


/-- Scaling the convergent positive reciprocal-power series is exact. -/
theorem midpoint_powerSeries_scale (m : ℕ) {Q r : ℝ} (hQ : 0 < Q) (_hr : 0 < r) :
    (∑' k : ℕ, 1 / (Q*(k : ℝ)+r+1)^(m+2)) =
      reciprocalPowerSeries m ((r+1)/Q) / Q^(m+2) := by
  unfold reciprocalPowerSeries
  rw [← tsum_div_const]
  apply tsum_congr
  intro k
  have he : Q*(k : ℝ)+r+1 = Q*((k : ℝ)+(r+1)/Q) := by
    field_simp
    ring
  rw [he, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem midpoint_powerSeries_summable (m : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => 1 / (Q*(k : ℝ)+r+1)^(m+2)) := by
  have hs := (reciprocalPowerSeries_summable m
    (show 0 < (r+1)/Q by positivity)).div_const (Q^(m+2))
  apply hs.congr
  intro k
  have he : Q*(k : ℝ)+r+1 = Q*((k : ℝ)+(r+1)/Q) := by
    field_simp
    ring
  rw [he, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The positive core uses actual polygamma values, not placeholder functions. -/
theorem mMidpointTerm_tsum_polygamma (j : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    (∑' k : ℕ, mMidpointTerm j (Q*k+r)) =
      2*((j : ℝ)+1) *
        (iteratedDeriv (2*j+3) realDigamma ((r+1)/Q) /
          (((2*j+3).factorial : ℝ)*Q^(2*j+4)) -
         iteratedDeriv (2*j+4) realDigamma ((r+1)/Q) /
          (((2*j+4).factorial : ℝ)*Q^(2*j+5))) := by
  have hx : 0 < (r+1)/Q := by positivity
  have hs0 := midpoint_powerSeries_summable (2*j+2) hQ hr
  have hs1 := midpoint_powerSeries_summable (2*j+3) hQ hr
  simp only [Nat.add_assoc] at hs0 hs1
  unfold mMidpointTerm
  rw [tsum_mul_left, hs0.tsum_add hs1]
  have h0 := midpoint_powerSeries_scale (2*j+2) hQ hr
  have h1 := midpoint_powerSeries_scale (2*j+3) hQ hr
  simp only [Nat.add_assoc] at h0 h1
  rw [h0, h1]
  have p0 := iteratedDeriv_digamma_series (2*j+2) hx
  have p1 := iteratedDeriv_digamma_series (2*j+3) hx
  have sg0 : (-1 : ℝ)^(2*j+2) = 1 := by
    rw [pow_add, pow_mul]; norm_num
  have sg1 : (-1 : ℝ)^(2*j+3) = -1 := by
    rw [pow_add, pow_mul]; norm_num
  simp only [Nat.add_assoc, sg0, sg1, one_mul, neg_one_mul] at p0 p1
  rw [p0, p1]
  have f0 : ((2*j+3).factorial : ℝ) ≠ 0 := by positivity
  have f1 : ((2*j+4).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Two complete mean-zero energies are compared by the same diagonal weights. -/
theorem zeroMean_positiveM_exact (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n+Q)=F n) (hm : periodMean F Q=0) (N : ℕ) :
    (∑' k : ℕ, RiemannResearch.RH.ArithmeticCumulative.mixtureWeight (k+1) *
      (RiemannResearch.Probability.ConditionalIID.cesaro F (k+1))^2) =
      positiveMCore Q N (fun r => periodDefect F Q (r.val+1)) +
      positiveMTail Q N (fun r => periodDefect F Q (r.val+1)) := by
  have he := periodic_error_energy_identity F Q hQ hp 0
  simp only [hm, sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_mul, zero_add] at he
  rw [he]
  exact positiveM_quadratic_exact Q hQ N _


/-- Already at order one, the positive core is uniformly equivalent to the energy. -/
theorem positiveM_orderOne_enclosure (Q : ℕ) (hQ : 0 < Q) (B : Fin Q → ℝ) :
    positiveMCore Q 1 B ≤ (∑ r : Fin Q, progressionM Q (r.val+1)*(B r)^2) ∧
    (∑ r : Fin Q, progressionM Q (r.val+1)*(B r)^2) ≤ 2*positiveMCore Q 1 B := by
  have he := positiveM_quadratic_exact Q hQ 1 B
  have hn := positiveMTail_nonneg Q hQ 1 B
  have ht := positiveMTail_relative Q hQ 1 B
  norm_num at ht
  constructor <;> linarith

/-- The comparison is for the actual infinite conditional energy of F. -/
theorem zeroMean_positiveM_orderOne (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n+Q)=F n) (hm : periodMean F Q=0) :
    positiveMCore Q 1 (fun r => periodDefect F Q (r.val+1)) ≤
      (∑' k : ℕ, RiemannResearch.RH.ArithmeticCumulative.mixtureWeight (k+1) *
        (RiemannResearch.Probability.ConditionalIID.cesaro F (k+1))^2) ∧
    (∑' k : ℕ, RiemannResearch.RH.ArithmeticCumulative.mixtureWeight (k+1) *
        (RiemannResearch.Probability.ConditionalIID.cesaro F (k+1))^2) ≤
      2*positiveMCore Q 1 (fun r => periodDefect F Q (r.val+1)) := by
  have he := periodic_error_energy_identity F Q hQ hp 0
  simp only [hm, sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_mul, zero_add] at he
  rw [he]
  exact positiveM_orderOne_enclosure Q hQ _

/-- Equivalence of two open growing bounds, not a proof of either bound. -/
theorem growing_zeroMean_positiveM_subpolynomial_iff
    (F : ℕ → ℕ → ℝ) (Q Y : ℕ → ℕ)
    (hQ : ∀ j, 0 < Q j) (hp : ∀ j n, F j (n+Q j)=F j n)
    (hm : ∀ j, periodMean (F j) (Q j)=0) :
    HasSubpolynomialEnergy Y
      (fun j => ∑' k : ℕ, RiemannResearch.RH.ArithmeticCumulative.mixtureWeight (k+1) *
        (RiemannResearch.Probability.ConditionalIID.cesaro (F j) (k+1))^2) ↔
    HasSubpolynomialEnergy Y
      (fun j => positiveMCore (Q j) 1 (fun r => periodDefect (F j) (Q j) (r.val+1))) := by
  have hb (j : ℕ) := zeroMean_positiveM_orderOne (F j) (Q j) (hQ j) (hp j) (hm j)
  constructor
  · intro h ε hε
    obtain ⟨C,hC,j₀,hbound⟩ := h ε hε
    exact ⟨C,hC,j₀,fun j hj => (hb j).1.trans (hbound j hj)⟩
  · intro h ε hε
    obtain ⟨C,hC,j₀,hbound⟩ := h ε hε
    refine ⟨2*C,by positivity,j₀,?_⟩
    intro j hj
    calc
      _ ≤ 2*positiveMCore (Q j) 1 (fun r => periodDefect (F j) (Q j) (r.val+1)) := (hb j).2
      _ ≤ 2*(C*(Y j : ℝ)^ε) := mul_le_mul_of_nonneg_left (hbound j hj) (by norm_num)
      _ = _ := by ring

end
end RiemannResearch.RH.CRTBlock

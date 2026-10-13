import RiemannResearch.Analysis.SharpLogarithmicResidualBarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
/-!
# Innovation bounds forced by a logarithmic residual barrier

Source: user-requested backward-RH audit, 13 October 2026.
The deductions from adjacent gains and an explicit reciprocal-index envelope
are independently derived. The sharp log-gain telescope is reused from
SharpLogarithmicResidualBarrier. No Burnol theorem is assumed or asserted
without an explicit hypothesis, and no innovation lower bound is proved.
-/

set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.InnovationLogBarrier
open RiemannResearch.Analysis.LogarithmicResidualBarrier

theorem finite_quartic_bound (u b v A t a c r : ℝ)
    (hu : 0 < u) (hA : 0 ≤ A) (ht : 0 < t)
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hv : v ≤ u) (hsource : A ≤ 2 * (u - b) * (b - v))
    (hdrop : t * (u - v) ≤ a * u) (hlower : c ≤ 2 * t * u) (hmid : r * u ≤ b) :
    A * c ^ 2 * r ^ 4 ≤ 2 * a ^ 2 * b ^ 4 := by
  have ham : 2 * A ≤ (u - v) ^ 2 := by nlinarith [sq_nonneg (u - 2 * b + v)]
  have hs : (t * (u - v)) ^ 2 ≤ (a * u) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ht.le (sub_nonneg.mpr hv)) hdrop 2
  have hAt : 2 * A * t ^ 2 ≤ a ^ 2 * u ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right ham (sq_nonneg t)]
  have hc2 := pow_le_pow_left₀ hc hlower 2
  have hb4 := pow_le_pow_left₀ (mul_nonneg hr hu.le) hmid 4
  calc
    A * c ^ 2 * r ^ 4 ≤ A * (2 * t * u) ^ 2 * r ^ 4 := by gcongr
    _ = (2 * A * t ^ 2) * (2 * u ^ 2 * r ^ 4) := by ring
    _ ≤ (a ^ 2 * u ^ 2) * (2 * u ^ 2 * r ^ 4) := by gcongr
    _ = 2 * a ^ 2 * (r * u) ^ 4 := by ring
    _ ≤ 2 * a ^ 2 * b ^ 4 := by gcongr

theorem late_quartic_bound (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d) (hA : ∀ k, 0 ≤ A k)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (a r : ℝ) (ha : 1 < a) (hr : 0 < r) (hr1 : r < 1) (J : ℕ) :
    ∃ j, J ≤ j ∧ A (2 * j + 1) * c ^ 2 * r ^ 4 ≤ 2 * a ^ 2 * (d (2 * j + 1)) ^ 4 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (a / (1 - r))
  have hel : ∀ k, K ≤ k → (c / 2) / ((k : ℝ) + 1) ≤ d (2 * k) := by
    intro k hk
    have h := hl (2 * k) (by omega)
    have hden : 0 < ((2 * k:ℕ): ℝ) + 1 := by positivity
    apply le_trans _ h
    apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1) hden).mpr
    push_cast
    nlinarith
  obtain ⟨j,hj,hsmall⟩ := exists_late_scaled_gain_lt_of_distance_lower
    (fun k => d (2 * k)) (fun k => hd _) (c / 2) (by positivity) K hel a ha
    (max J (max K M))
  have hJ : J ≤ j := le_trans (le_max_left _ _) hj
  have hK : K ≤ j := by omega
  have hMj : M ≤ j := by omega
  have hjreal : (M : ℝ) ≤ j := by exact_mod_cast hMj
  have hta : a ≤ ((j : ℝ) + 1) * (1 - r) := by
    have hh := (div_lt_iff₀ (sub_pos.mpr hr1)).mp hM
    nlinarith
  have hdrop : ((j : ℝ) + 1) * (d (2 * j) - d (2 * j + 2)) ≤ a * d (2 * j) := by
    unfold relativeGain at hsmall
    have he : 2 * (j + 1) = 2 * j + 2 := by omega
    dsimp only at hsmall
    rw [he] at hsmall
    have hh := (div_lt_iff₀ (hd (2 * j))).mp
      (show (((j : ℝ) + 1) * (d (2 * j) - d (2 * j + 2))) / d (2 * j) < a by
        simpa only [mul_div_assoc] using hsmall)
    exact hh.le
  have hlower : c ≤ 2 * ((j : ℝ) + 1) * d (2 * j) := by
    have hh := (div_le_iff₀ (by positivity : 0 < ((2 * j:ℕ): ℝ) + 1)).mp
      (hl (2 * j) (by omega))
    push_cast at hh
    nlinarith [hd (2 * j)]
  have hmid : r * d (2 * j) ≤ d (2 * j + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hta (hd (2 * j)).le
    have hm' := hm (show 2 * j + 1 ≤ 2 * j + 2 by omega)
    nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity)
      (sub_nonneg.mpr hm')]
  exact ⟨j,hJ,finite_quartic_bound _ _ _ _ _ _ _ _
    (hd _) (hA _) (by positivity) hc.le hr.le
    (hm (by omega)) (hs (2 * j)) hdrop hlower hmid⟩

theorem reciprocal_quartic_model (C t : ℝ) (hC : 0 < C) (ht : 1 < t) :
    2 * (C / (t - 1) - C / t) * (C / t - C / (t + 1)) =
      (2 / C ^ 2) * (t ^ 2 / (t ^ 2 - 1)) * (C / t) ^ 4 := by
  have h0 : t ≠ 0 := by linarith
  have hm : t - 1 ≠ 0 := by linarith
  have hp : t + 1 ≠ 0 := by linarith
  have hsq : t ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

theorem no_quadratic_eventually (d : ℕ → ℝ) (hd : ∀ k, 0 < d k)
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (q : ℝ) (hq : q < 1) (J : ℕ)
    (hstep : ∀ k, J ≤ k → d (k + 1) ≤ q * d k) : False := by
  obtain ⟨M,hM⟩ := exists_nat_gt (2 / (1 - q))
  obtain ⟨j,hj,hsmall⟩ := exists_late_scaled_gain_lt_of_distance_lower
    d hd c hc K hl 2 (by norm_num) (max J M)
  have hlarge : 2 < ((j : ℝ) + 1) * (1 - q) := by
    have hh := (div_lt_iff₀ (by linarith : 0 < 1 - q)).mp hM
    have hm : (M : ℝ) ≤ j := by exact_mod_cast (show M ≤ j by omega)
    nlinarith
  have hs := hstep j (by omega)
  have hg : 1 - q ≤ relativeGain d j := by
    unfold relativeGain
    apply (le_div_iff₀ (hd j)).mpr
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ (j : ℝ) + 1 by positivity)]

theorem no_divergent_quartic_ratio (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d) (hA : ∀ k, 0 ≤ A k)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (hdiv : Tendsto (fun k => A k / (d k) ^ 4) atTop atTop) : False := by
  obtain ⟨J,hJ⟩ := (tendsto_atTop_atTop.mp hdiv) (128 / c ^ 2 + 1)
  obtain ⟨j,hj,hb⟩ := late_quartic_bound d A hd hm hA hs c hc K hl
    2 (1 / 2) (by norm_num) (by norm_num) (by norm_num) J
  have hh := hJ (2 * j + 1) (by omega)
  have hh' := (le_div_iff₀ (pow_pos (hd _) 4)).mp hh
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hp := mul_le_mul_of_nonneg_right hh' hc2.le
  have he : (128 / c ^ 2 + 1) * (d (2 * j + 1)) ^ 4 * c ^ 2 =
      (128 + c ^ 2) * (d (2 * j + 1)) ^ 4 := by field_simp
  rw [he] at hp
  norm_num at hb
  nlinarith [mul_pos hc2 (pow_pos (hd (2 * j + 1)) 4)]


/-- No positive real exponent below four can hold eventually, even when
convergence to zero is supplied independently. -/
theorem no_subquartic_of_zero_limit (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d) (hA : ∀ k, 0 ≤ A k)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (hz : Tendsto d atTop (𝓝 0)) (p η : ℝ) (hp : p < 4) (hη : 0 < η)
    (J : ℕ) (hsource : ∀ k, J ≤ k → η * (d k) ^ p ≤ A k) : False := by
  have hlim : Tendsto (fun k => 128 * (d k) ^ (4 - p)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (by linarith : 4 - p ≠ 0)] using
      (tendsto_const_nhds.mul (hz.rpow_const (Or.inr (by linarith : 0 ≤ 4 - p))))
  have hevent := hlim.eventually_lt_const (mul_pos hη (sq_pos_of_pos hc))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  obtain ⟨j, hj, hb⟩ := late_quartic_bound d A hd hm hA hs c hc K hl
    2 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (max J M)
  have hnJ : J ≤ 2 * j + 1 := by omega
  have hnM : M ≤ 2 * j + 1 := by omega
  have hlow := mul_le_mul_of_nonneg_right (hsource _ hnJ) (sq_nonneg c)
  norm_num at hb
  have hbound : η * c ^ 2 * (d (2 * j + 1)) ^ p ≤
      128 * (d (2 * j + 1)) ^ 4 := by nlinarith
  have hratio : η * c ^ 2 ≤ 128 * (d (2 * j + 1)) ^ (4 - p) := by
    rw [Real.rpow_sub (hd _) 4 p]
    norm_num only [Real.rpow_ofNat]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (hd _) p)).mpr
    simpa only [mul_div_assoc] using hbound
  exact (not_lt_of_ge hratio) (hM _ hnM)

/-- Convergence is only to an unspecified nonnegative limit.
The hypothesized innovation lower bound itself forces that limit to vanish. -/
theorem no_subquartic_of_limit (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d) (hA : ∀ k, 0 ≤ A k)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (l : ℝ) (ht : Tendsto d atTop (𝓝 l))
    (p η : ℝ) (hp0 : 0 < p) (hp : p < 4) (hη : 0 < η)
    (J : ℕ) (hsource : ∀ k, J ≤ k → η * (d k) ^ p ≤ A k) : False := by
  have hshift (j : ℕ) : Tendsto (fun k => d (k + j)) atTop (𝓝 l) :=
    ht.comp (tendsto_add_atTop_nat j)
  have hleft : Tendsto (fun k => η * (d (k + 1)) ^ p) atTop (𝓝 (η * l ^ p)) :=
    tendsto_const_nhds.mul ((hshift 1).rpow_const (Or.inr hp0.le))
  have hright : Tendsto (fun k => 2 * (d k - d (k + 1)) *
      (d (k + 1) - d (k + 2))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (ht.sub (hshift 1))).mul
      ((hshift 1).sub (hshift 2))
  have he : η * l ^ p ≤ 0 := le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨J, fun k hk => (hsource (k+1) (by omega)).trans (hs k)⟩)
  have hl0 : 0 ≤ l := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall (fun k => (hd k).le))
  have hz : l = 0 := by
    by_contra h
    have hlp : 0 < l := lt_of_le_of_ne hl0 (Ne.symm h)
    exact (not_lt_of_ge he) (mul_pos hη (Real.rpow_pos_of_pos hlp p))
  subst l
  exact no_subquartic_of_zero_limit d A hd hm hA hs c hc K hl ht p η hp hη J hsource


open scoped BigOperators
/-- A finite counting budget for any selected contraction stages. -/
theorem contraction_count_budget (d : ℕ → ℝ) (hd : ∀ k, 0 < d k)
    (hm : Antitone d) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (q c : ℝ) (hc : 0 < c)
    (hl : c / ((N : ℝ) + 1) ≤ d N)
    (hstep : ∀ j ∈ S, d (j + 1) ≤ q * d j) :
    (S.card : ℝ) * (-Real.log q) ≤ Real.log (d 0 / c) + Real.log ((N : ℝ) + 1) := by
  have hp (j : ℕ) : 0 < 1 - relativeGain d j := by
    rw [one_sub_relativeGain d j (ne_of_gt (hd j))]
    exact div_pos (hd _) (hd _)
  have hn (j : ℕ) : 0 ≤ -Real.log (1 - relativeGain d j) := by
    have he : 1 - relativeGain d j ≤ 1 := by
      rw [one_sub_relativeGain d j (ne_of_gt (hd j))]
      exact (div_le_one (hd j)).mpr (hm (by omega))
    have hh := Real.log_le_log (hp j) he
    simpa using neg_le_neg hh
  calc
    _ = ∑ j ∈ S, -Real.log q := by simp
    _ ≤ ∑ j ∈ S, -Real.log (1 - relativeGain d j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply neg_le_neg
      apply Real.log_le_log (hp j)
      rw [one_sub_relativeGain d j (ne_of_gt (hd j))]
      exact (div_le_iff₀ (hd j)).mpr (hstep j hj)
    _ ≤ ∑ j ∈ Finset.range N, -Real.log (1 - relativeGain d j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun j _ _ => hn j)
    _ ≤ _ := log_gain_budget_of_distance_lower d hd N c hc hl

theorem reciprocal_model_allows_quartic (C t : ℝ) (hC : 0 < C) (ht : 1 < t) :
    (2 / C ^ 2) * (C / t) ^ 4 ≤
      2 * (C / (t - 1) - C / t) * (C / t - C / (t + 1)) := by
  rw [reciprocal_quartic_model C t hC ht]
  have hr : 1 ≤ t ^ 2 / (t ^ 2 - 1) :=
    (le_div_iff₀ (by nlinarith : 0 < t ^ 2 - 1)).mpr (by nlinarith)
  calc
    _ = (2 / C ^ 2) * 1 * (C / t) ^ 4 := by ring
    _ ≤ _ := by gcongr

/-- Upper recurrences alone provide no positive innovation lower bound. -/
theorem zero_source_satisfies_upper (u b v : ℝ) (hub : b ≤ u) (hbv : v ≤ b) :
    (0 : ℝ) ≤ 2 * (u - b) * (b - v) := by positivity

/-- The sharp critical constant for an eventually uniform quartic lower bound. -/
theorem quartic_coefficient_cap (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d) (hA : ∀ k, 0 ≤ A k)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hl : ∀ k, K ≤ k → c / ((k : ℝ) + 1) ≤ d k)
    (η : ℝ) (J : ℕ) (hsource : ∀ k, J ≤ k → η * (d k) ^ 4 ≤ A k) :
    η * c ^ 2 ≤ 2 := by
  have hparam (a r : ℝ) (ha : 1 < a) (hr : 0 < r) (hr1 : r < 1) :
      η * c ^ 2 * r ^ 4 ≤ 2 * a ^ 2 := by
    obtain ⟨j, hj, hb⟩ := late_quartic_bound d A hd hm hA hs c hc K hl a r ha hr hr1 J
    have hp := mul_le_mul_of_nonneg_right (hsource (2 * j + 1) (by omega))
      (show 0 ≤ c ^ 2 * r ^ 4 by positivity)
    apply (mul_le_mul_iff_left₀ (pow_pos (hd (2 * j + 1)) 4)).mp
    nlinarith
  let t : ℕ → ℝ := fun k => ((k : ℝ) + 2)⁻¹
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
      (fun k : ℕ => (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith))
      tendsto_natCast_atTop_atTop)
  have hp (k : ℕ) : 0 < t k ∧ t k < 1 := by
    dsimp [t]
    constructor
    · positivity
    · exact (inv_lt_one₀ (by positivity)).mpr
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hleft : Tendsto (fun k => η * c ^ 2 * (1 - t k) ^ 4)
      atTop (𝓝 (η * c ^ 2)) := by
    simpa using (tendsto_const_nhds.mul ((hone.sub ht).pow 4) :
      Tendsto (fun k => η * c ^ 2 * (1 - t k) ^ 4)
        atTop (𝓝 (η * c ^ 2 * (1 - 0) ^ 4)))
  have hright : Tendsto (fun k => 2 * (1 + t k) ^ 2) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.mul ((hone.add ht).pow 2) :
      Tendsto (fun k => 2 * (1 + t k) ^ 2) atTop (𝓝 (2 * (1 + 0) ^ 2)))
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall (fun k => hparam (1 + t k) (1 - t k)
    (by linarith [(hp k).1]) (by linarith [(hp k).2]) (by linarith [(hp k).1]))


/-- Even an arbitrarily sparse cofinal linear lower bound is impossible.
This uses adjacent gains and positivity, without a logarithmic envelope. -/
theorem no_cofinal_linear_source (d A : ℕ → ℝ)
    (hd : ∀ k, 0 < d k) (hm : Antitone d)
    (hs : ∀ k, A (k + 1) ≤ 2 * (d k - d (k + 1)) * (d (k + 1) - d (k + 2)))
    (l : ℝ) (ht : Tendsto d atTop (𝓝 l)) (η : ℝ) (hη : 0 < η)
    (hsource : ∀ B, ∃ k, B ≤ k ∧ η * d (k + 1) ≤ A (k + 1)) : False := by
  choose k hk hsrc using hsource
  have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hshift (j : ℕ) : Tendsto (fun i => d (k i + j)) atTop (𝓝 l) :=
    (ht.comp (tendsto_add_atTop_nat j)).comp hkt
  have hprev : Tendsto (fun i => d (k i)) atTop (𝓝 l) := ht.comp hkt
  have hleft : Tendsto (fun i => η * d (k i + 1)) atTop (𝓝 (η * l)) :=
    tendsto_const_nhds.mul (hshift 1)
  have hright : Tendsto (fun i => 2 * (d (k i) - d (k i + 1)) *
      (d (k i + 1) - d (k i + 2))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hprev.sub (hshift 1))).mul
      ((hshift 1).sub (hshift 2))
  have he : η * l ≤ 0 := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun i => (hsrc i).trans (hs (k i))))
  have hl0 : 0 ≤ l := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall (fun i => (hd i).le))
  have hz : l = 0 := by nlinarith
  have hbound (i : ℕ) : η ≤ 2 * d (k i) := by
    have hu : A (k i + 1) ≤ 2 * d (k i) * d (k i + 1) := by
      calc
        _ ≤ 2 * (d (k i) - d (k i + 1)) *
          (d (k i + 1) - d (k i + 2)) := hs (k i)
        _ ≤ 2 * d (k i) * d (k i + 1) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (sub_le_self _ (hd _).le) (by norm_num)
          · exact sub_le_self _ (hd _).le
          · exact sub_nonneg.mpr (hm (by omega))
          · exact mul_nonneg (by norm_num) (hd _).le
    exact (mul_le_mul_iff_left₀ (hd (k i + 1))).mp ((hsrc i).trans hu)
  have hh : η ≤ 2 * l := le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_const_nhds.mul hprev) (Eventually.of_forall hbound)
  rw [hz] at hh
  linarith
end RiemannResearch.Analysis.InnovationLogBarrier

import RiemannResearch.Analysis.HeadTailPairing
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# Cofinal product and signed trial-tail conditions
Source: user-provided Green-Pareto-Schur continuation, Sections 17 and 18.
The signed fraction, growing-tail balance and product conditions are explicit
conditional research reductions. None supplies an arithmetic provider.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.HeadTailStrengthening

/-- A surviving correction vanishes if its complete tail product vanishes
along a cofinal sequence. The inequality is needed only eventually. -/
theorem limit_eq_zero_of_cofinal_tail_product
    (T A S : ℕ → ℝ) (D : ℝ) (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop)
    (hT : Tendsto T atTop (𝓝 D))
    (hprod : Tendsto (fun n => A (k n) * S (k n)) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, (T (k n)) ^ 2 ≤ A (k n) * S (k n)) :
    D = 0 := by
  have hle : D ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto ((hT.comp hk).pow 2) hprod hbound
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg D))

/-- The equivalent provider can be stated without choosing a subsequence:
the product is arbitrarily small arbitrarily far out. This is the natural
`liminf = 0` formulation when the complete product is nonnegative. -/
theorem limit_eq_zero_of_frequent_small_tail_product
    (T A S : ℕ → ℝ) (D : ℝ)
    (hT : Tendsto T atTop (𝓝 D))
    (hbound : ∀ᶠ n in atTop, (T n) ^ 2 ≤ A n * S n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, A n * S n ≤ ε) :
    D = 0 := by
  by_contra hD
  have hpos : 0 < D ^ 2 := sq_pos_of_ne_zero hD
  have hfreq : ∃ᶠ n in atTop, (T n) ^ 2 ≤ D ^ 2 / 2 :=
    ((hsmall (D ^ 2 / 2) (by linarith)).and_eventually hbound).mono
      (fun n hn => hn.2.trans hn.1)
  have hle : D ^ 2 ≤ D ^ 2 / 2 :=
    le_of_tendsto_of_frequently (hT.pow 2) hfreq
  linarith

/-- A concrete quantifier form of the frequent-smallness provider. -/
theorem limit_eq_zero_of_arbitrarily_late_small_tail_product
    (T A S : ℕ → ℝ) (D : ℝ)
    (hT : Tendsto T atTop (𝓝 D))
    (hbound : ∀ᶠ n in atTop, (T n) ^ 2 ≤ A n * S n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ M : ℕ,
      ∃ n : ℕ, M ≤ n ∧ A n * S n ≤ ε) : D = 0 := by
  apply limit_eq_zero_of_frequent_small_tail_product T A S D hT hbound
  intro ε hε
  exact frequently_atTop.mpr (hsmall ε hε)

/-- Product-smallness survives a vanishing error budget and absorption of
any fixed strict fraction of the squared correction. Neither absolute tail
boundedness nor a separately vanishing explicit trial tail is required. -/
theorem limit_eq_zero_of_cofinal_absorbed_tail_product
    (T A S E : ℕ → ℝ) (D θ : ℝ) (k : ℕ → ℕ)
    (hθ : θ < 1) (hk : Tendsto k atTop atTop)
    (hT : Tendsto T atTop (𝓝 D))
    (hprod : Tendsto (fun n => A (k n) * S (k n)) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (T (k n)) ^ 2 ≤ θ * (T (k n)) ^ 2 + A (k n) * S (k n) + E n) :
    D = 0 := by
  have hsq := (hT.comp hk).pow 2
  have hrhs := ((hsq.const_mul θ).add hprod).add hE
  have hle : D ^ 2 ≤ θ * D ^ 2 := by
    simpa only [add_zero] using le_of_tendsto_of_tendsto hsq hrhs hbound
  have hfactor : 0 < 1 - θ := sub_pos.mpr hθ
  have hzero : (1 - θ) * D ^ 2 = 0 := by
    apply le_antisymm
    · nlinarith [hle]
    · exact mul_nonneg hfactor.le (sq_nonneg D)
  exact sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hfactor))

/-- Permits controlled growth of the explicit trial tail. A growing
envelope `R` is harmless when its product with the optimizer tail vanishes. -/
theorem limit_eq_zero_of_cofinal_growth_tail_balance
    (T A S R : ℕ → ℝ) (D C : ℝ) (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop)
    (hT : Tendsto T atTop (𝓝 D))
    (hbalance : Tendsto (fun n => R n * S (k n)) atTop (𝓝 0))
    (hS : ∀ᶠ n in atTop, 0 ≤ S (k n))
    (hA : ∀ᶠ n in atTop, A (k n) ≤ C * R n)
    (hbound : ∀ᶠ n in atTop, (T (k n)) ^ 2 ≤ A (k n) * S (k n)) :
    D = 0 := by
  have hmajor : ∀ᶠ n in atTop,
      (T (k n)) ^ 2 ≤ C * (R n * S (k n)) :=
    ((hbound.and hA).and hS).mono fun n hn => by
      have hp := mul_le_mul_of_nonneg_right hn.1.2 hn.2
      simpa only [mul_assoc] using hn.1.1.trans hp
  have hlim : Tendsto (fun n => C * (R n * S (k n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbalance.const_mul C
  have hle : D ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto ((hT.comp hk).pow 2) hlim hmajor
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg D))

/-- A positive surviving defect forces the exact head-lift tail energy to
diverge to infinity when the actual optimizer tail tends to zero. This is
the full limit statement, rather than just a finite reciprocal bound. -/
theorem tail_energy_tendsto_atTop_of_positive_correction
    (T A S : ℕ → ℝ) (D : ℝ) (hD : 0 < D)
    (hT : Tendsto T atTop (𝓝 D))
    (hS : Tendsto S atTop (𝓝 0))
    (hSnonneg : ∀ᶠ n in atTop, 0 ≤ S n)
    (hbound : ∀ᶠ n in atTop, (T n) ^ 2 ≤ A n * S n) :
    Tendsto A atTop atTop := by
  refine tendsto_atTop.mpr fun B => ?_
  have hTlarge : ∀ᶠ n in atTop, D / 2 < T n :=
    hT.eventually (Ioi_mem_nhds (by linarith))
  have hSsmall : ∀ᶠ n in atTop, B * S n < D ^ 2 / 4 := by
    have hz : 0 < D ^ 2 / 4 := by nlinarith [sq_pos_of_pos hD]
    have hb : Tendsto (fun n => B * S n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hS.const_mul B
    exact hb.eventually (Iio_mem_nhds hz)
  exact (((hTlarge.and hSsmall).and hSnonneg).and hbound).mono fun n hn => by
    by_contra hBA
    have hAB : A n < B := lt_of_not_ge hBA
    have hmul : A n * S n ≤ B * S n :=
      mul_le_mul_of_nonneg_right hAB.le hn.1.2
    have hpos : 0 < T n := by linarith [hn.1.1.1]
    nlinarith [hn.1.1.1, hn.1.1.2, hn.2, hmul]

/-- In an exact signed decomposition, a vanishing head error forces the
complete signed tail pairing to approach the residual defect. This retains
the signed pairing; it places no bound on either absolute tail norm. -/
theorem signed_tail_tendsto_of_head_error_bound
    (D H L E : ℕ → ℝ) (δ B : ℝ)
    (hD : Tendsto D atTop (𝓝 δ))
    (hE : Tendsto E atTop (𝓝 0))
    (hhead : ∀ᶠ n in atTop, |H n| ≤ B * E n)
    (hidentity : ∀ n, D n = H n + L n) :
    Tendsto L atTop (𝓝 δ) := by
  have hH : Tendsto H atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · simpa only [Real.norm_eq_abs] using hhead
    · simpa only [mul_zero] using hE.const_mul B
  have hfun : (fun n => D n - H n) = L := by
    funext n
    linarith [hidentity n]
  simpa only [hfun, sub_zero] using hD.sub hH

/-- A strict-fraction upper bound for the complete signed tail pairing
closes the residual defect on a cofinal sequence. The arithmetic provider
here is signed cancellation, not an absolute Gram-energy cap. -/
theorem limit_eq_zero_of_signed_cofinal_fraction
    (D H L E Z : ℕ → ℝ) (δ B θ : ℝ) (k : ℕ → ℕ)
    (hδ : 0 ≤ δ) (hθ : θ < 1) (hk : Tendsto k atTop atTop)
    (hD : Tendsto D atTop (𝓝 δ))
    (hE : Tendsto (fun n => E (k n)) atTop (𝓝 0))
    (hZ : Tendsto Z atTop (𝓝 0))
    (hhead : ∀ᶠ n in atTop, |H (k n)| ≤ B * E (k n))
    (hidentity : ∀ n, D n = H n + L n)
    (hfraction : ∀ᶠ n in atTop, L (k n) ≤ θ * D (k n) + Z n) :
    δ = 0 := by
  have hL : Tendsto (fun n => L (k n)) atTop (𝓝 δ) :=
    signed_tail_tendsto_of_head_error_bound
      (fun n => D (k n)) (fun n => H (k n))
      (fun n => L (k n)) (fun n => E (k n)) δ B
      (hD.comp hk) hE hhead (fun n => hidentity (k n))
  have hle : δ ≤ θ * δ := by
    simpa only [add_zero] using
      le_of_tendsto_of_tendsto hL (((hD.comp hk).const_mul θ).add hZ) hfraction
  have hfactor : 0 < 1 - θ := sub_pos.mpr hθ
  have hzero : (1 - θ) * δ = 0 := by
    apply le_antisymm
    · nlinarith [hle]
    · exact mul_nonneg hfactor.le hδ
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hfactor)

/-- A surviving residual forces divergence of the complete tail energy of
every chosen trial family whose head error tends to zero. Exact head
interpolation is unnecessary. The Cauchy hypothesis is applied to the
actual signed pairing after its limit has been identified. -/
theorem trial_tail_tendsto_atTop_of_positive_residual
    (D H L E A S : ℕ → ℝ) (δ B : ℝ) (hδ : 0 < δ)
    (hD : Tendsto D atTop (𝓝 δ))
    (hE : Tendsto E atTop (𝓝 0))
    (hhead : ∀ᶠ n in atTop, |H n| ≤ B * E n)
    (hidentity : ∀ n, D n = H n + L n)
    (hS : Tendsto S atTop (𝓝 0))
    (hSnonneg : ∀ᶠ n in atTop, 0 ≤ S n)
    (hCauchy : ∀ᶠ n in atTop, (L n) ^ 2 ≤ A n * S n) :
    Tendsto A atTop atTop := by
  exact tail_energy_tendsto_atTop_of_positive_correction L A S δ hδ
    (signed_tail_tendsto_of_head_error_bound D H L E δ B hD hE hhead hidentity)
    hS hSnonneg hCauchy

end RiemannResearch.Analysis.HeadTailStrengthening

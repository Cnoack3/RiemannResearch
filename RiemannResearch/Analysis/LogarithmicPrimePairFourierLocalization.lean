import RiemannResearch.Analysis.LogarithmicFejerLocalization
import RiemannResearch.Analysis.LogarithmicPrimePairCenteredLimit
import RiemannResearch.Analysis.LogarithmicPrimePairSieve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additive Fourier localization for the actual centered prime polynomial

Plancherel and the annular diagonal give the first tail bound. At the natural
frequency scale only a bounded *upper* count for the sharp pair statistic
at the single width 1 is used. In the sieve corollary this follows from the
explicit literature hypothesis `GPYPrimePairSieve` (Goldston, Pintz and
Yıldırım, *Primes in tuples IV*, Acta Arith. 160 (2013), (5.3)–(5.5),
https://doi.org/10.4064/aa160-1-3). The local variance is an open input.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators Topology ArithmeticFunction

namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open FractionalFejer

/-- Normalized centered energy on a measurable frequency set (used on arcs and complements). -/
def centeredEnergyOn (s : Set Circle₁) (A B u X : ℝ) : ℝ :=
  energyOn s (shiftWidth u X) (u * Real.log X - shiftWidth u X)
    (Ioc ⌊A*X⌋₊ ⌊B*X⌋₊) (fun n => Λ n - 1) / (X * (Real.log X)^2)

theorem centeredEnergyOn_split (δ A B u X : ℝ) :
    centeredEnergyOn (centralArc δ) A B u X + centeredEnergyOn (centralArc δ)ᶜ A B u X =
      annularEnergy A B u X (fun n => Λ n - 1) / (X * (Real.log X)^2) := by
  unfold centeredEnergyOn annularEnergy
  rw [← add_div, energy_split_arc]

private theorem fraction_bounds {u X : ℝ} (hu : 0 < u) (hX : 1 < X) :
    0 ≤ u * Real.log X - shiftWidth u X ∧ u * Real.log X - shiftWidth u X ≤ 1 := by
  have hf := Nat.floor_le (mul_pos hu (Real.log_pos hX)).le
  have hl := Nat.lt_floor_add_one (u * Real.log X)
  change 0 ≤ u * Real.log X - (⌊u * Real.log X⌋₊ : ℝ) ∧
    u * Real.log X - (⌊u * Real.log X⌋₊ : ℝ) ≤ 1
  constructor <;> linarith

private theorem centeredEnergyOn_nonneg (s : Set Circle₁) (A B : ℝ) {u X : ℝ}
    (hu : 0 < u) (hX : 1 < X) : 0 ≤ centeredEnergyOn s A B u X :=
  div_nonneg (energyOn_nonneg _ _ (fraction_bounds hu hX).1 (fraction_bounds hu hX).2 _ _)
    (mul_nonneg (by linarith) (sq_nonneg _))

/-- The exterior energy is negligible whenever the squared chord radius times log X diverges. -/
theorem tendsto_centered_offArc {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ X in atTop, 0 < δ X)
    (hgrow : Tendsto (fun X => (δ X)^2 * Real.log X) atTop atTop) :
    Tendsto (fun X => centeredEnergyOn (centralArc (δ X))ᶜ A B u X) atTop (𝓝 0) := by
  have hl := ((annular_centered_diagonal_limit hA hAB).const_mul 4).div_atTop hgrow
  apply squeeze_zero' _ _ hl
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact centeredEnergyOn_nonneg _ A B hu hX
  filter_upwards [hδ, eventually_gt_atTop (1 : ℝ)] with X hd hX
  have hx : 0 < X := by linarith
  have hL := Real.log_pos hX
  obtain ⟨h0, h1⟩ := fraction_bounds hu hX
  have he := offArc_energy_le (δ X) hd.le (shiftWidth u X) h0 h1
    (Ioc ⌊A*X⌋₊ ⌊B*X⌋₊) (fun n => Λ n - 1)
  rw [mul_comm ((δ X)^2)] at he
  have hb := (le_div_iff₀ (sq_pos_of_pos hd)).mpr he
  unfold centeredEnergyOn
  exact (div_le_div_of_nonneg_right hb (mul_pos hx (sq_pos_of_pos hL)).le).trans_eq
    (by field_simp [hd.ne', hx.ne', hL.ne'] <;> ring)

/-- A finite uniform bound for all shorter centered windows from positive uncentered pairs.
The second site of the pair count is free to cross the annular endpoint. -/
private theorem short_centered_energy_le (A B X : ℝ) (j U : ℕ) (hj : j ≤ U) :
    let I := Ioc ⌊A*X⌋₊ ⌊B*X⌋₊
    energy j 0 I (fun n => Λ n - 1) ≤
      (j : ℝ) * ((∑ n ∈ I, (Λ n - 1)^2) +
        2 * ((∑ h ∈ Ioc 0 U, pairBlock A B X h) + (U : ℝ) * I.card)) := by
  intro I
  have hc (h : ℕ) : correlation I (fun n => Λ n - 1) h ≤ pairBlock A B X h + I.card := by
    have hrow (n : ℕ) :
        (if n+h ∈ I then (Λ n - 1) * (Λ (n+h) - 1) else 0) ≤ Λ n * Λ (n+h) + 1 := by
      have h1 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have h2 : 0 ≤ Λ (n+h) := ArithmeticFunction.vonMangoldt_nonneg
      split_ifs <;> nlinarith [mul_nonneg h1 h2]
    simpa only [correlation, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, I, pairBlock]
      using sum_le_sum (s := I) (fun n _ => hrow n)
  have hrow (h : ℕ) (hh : h ∈ Ioc 0 j) :
      ((j : ℝ) - h) * correlation I (fun n => Λ n - 1) h ≤
        (j : ℝ) * (pairBlock A B X h + I.card) := by
    have hjh : (h : ℝ) ≤ j := by exact_mod_cast (mem_Ioc.mp hh).2
    exact (mul_le_mul_of_nonneg_left (hc h) (sub_nonneg.mpr hjh)).trans
      (mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg h))
        (add_nonneg (pairBlock_nonneg _ _ _ _) (Nat.cast_nonneg _)))
  have hsum := sum_le_sum hrow
  have hsub : Ioc 0 j ⊆ Ioc 0 U := fun _ hh => mem_Ioc.mpr
    ⟨(mem_Ioc.mp hh).1, (mem_Ioc.mp hh).2.trans hj⟩
  have hh := sum_le_sum_of_subset_of_nonneg (f := fun h => (j : ℝ)*(pairBlock A B X h + I.card))
    hsub (fun h _ _ => mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (pairBlock_nonneg _ _ _ _) (Nat.cast_nonneg _)))
  have hcomb := hsum.trans hh
  rw [← mul_sum, sum_add_distrib] at hcomb
  simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero] at hcomb
  rw [energy_eq]
  simp only [add_zero]
  linarith only [hcomb]

private theorem short_energy_bound {A B S : ℝ} (hA : 0 < A) (hAB : A < B)
    (hS : ∀ᶠ X : ℝ in atTop, sharpPairAverage A B 1 X ≤ S) :
    ∀ᶠ X : ℝ in atTop, ∀ j ≤ shiftWidth 1 X,
      energy j 0 (Ioc ⌊A*X⌋₊ ⌊B*X⌋₊) (fun n => Λ n - 1) ≤
        (j : ℝ) * (((B-A+1) + 2*(S+B))*(X*Real.log X)) := by
  filter_upwards [hS, (annular_centered_diagonal_limit hA hAB).eventually_lt_const
    (show B-A < B-A+1 by linarith), eventually_gt_atTop (1 : ℝ)] with X hs hd hX
  intro j hj
  let I := Ioc ⌊A*X⌋₊ ⌊B*X⌋₊
  let U := shiftWidth 1 X
  have hx : 0 < X := by linarith
  have hL := Real.log_pos hX
  have hpos := mul_pos hx hL
  have hd' : (∑ n ∈ I, (Λ n - 1)^2) ≤ (B-A+1)*(X*Real.log X) :=
    ((div_lt_iff₀ hpos).mp hd).le
  have hs' : (∑ h ∈ Ioc 0 U, pairBlock A B X h) ≤ S*(X*Real.log X) := by
    unfold sharpPairAverage at hs
    rw [sum_comm] at hs
    exact (div_le_iff₀ hpos).mp hs
  have hi : (I.card : ℝ) ≤ B*X := by
    dsimp [I]
    rw [Nat.card_Ioc]
    exact (show ((⌊B*X⌋₊ - ⌊A*X⌋₊ : ℕ) : ℝ) ≤ ⌊B*X⌋₊ by
      exact_mod_cast Nat.sub_le _ _).trans (Nat.floor_le (mul_pos (hA.trans hAB) hx).le)
  have hw : (U : ℝ) ≤ Real.log X := by simpa [U, shiftWidth] using Nat.floor_le hL.le
  have hcard := mul_le_mul hw hi (Nat.cast_nonneg I.card) hL.le
  apply (short_centered_energy_le A B X j U hj).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg j)
  change (∑ n ∈ I, (Λ n - 1)^2) + 2 * ((∑ h ∈ Ioc 0 U, pairBlock A B X h) +
    (U : ℝ)*I.card) ≤ _
  linarith only [hd', hs', hcard]

/-- Only upper control of the prime-pair count at width 1 enters this uniform tail bound. -/
theorem eventually_centered_offArc_le_of_sharp_bound {A B S : ℝ} (hA : 0 < A) (hAB : A < B)
    (hS : 0 < S) (hs : ∀ᶠ X : ℝ in atTop, sharpPairAverage A B 1 X ≤ S) :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 5 ≤ δ * Real.log X →
      ∀ u : ℝ, 0 < u → centeredEnergyOn (centralArc δ)ᶜ A B u X ≤ C / (δ * Real.log X) := by
  let K := (B - A + 1) + 2 * (S + B)
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨20 * K, by positivity, ?_⟩
  filter_upwards [short_energy_bound hA hAB hs, eventually_gt_atTop (1 : ℝ)] with X hshort hX
  intro δ hd hd1 hg u hu
  have hx : 0 < X := by linarith
  have hL := Real.log_pos hX
  have he := offArc_energy_le_of_short_bound hd hd1 hg
    (show 0 ≤ K * (X * Real.log X) from (mul_pos hK (mul_pos hx hL)).le)
    (shiftWidth u X) (fraction_bounds hu hX).1 (fraction_bounds hu hX).2
    (Ioc ⌊A*X⌋₊ ⌊B*X⌋₊) (fun n => Λ n - 1)
    (fun j hj => hshort j (by simpa [shiftWidth] using hj))
  exact (div_le_div_of_nonneg_right he (mul_pos hx (sq_pos_of_pos hL)).le).trans_eq
    (by field_simp [hd.ne', hx.ne', hL.ne'] <;> ring)

/-- The sieve gives a vanishing tail on any arc wider than 1/log X by a divergent factor. -/
theorem tendsto_centered_offArc_of_sieve (published : GPYPrimePairSieve)
    {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop) :
    Tendsto (fun X => centeredEnergyOn (centralArc (δ X))ᶜ A B u X) atTop (𝓝 0) := by
  obtain ⟨S, hS, hs⟩ := eventually_sharp_bounded_of_sieve published hA hAB zero_lt_one
  obtain ⟨C, _, hb⟩ := eventually_centered_offArc_le_of_sharp_bound hA hAB hS hs
  apply squeeze_zero' _ _ ((tendsto_const_nhds (x := C)).div_atTop hgrow)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact centeredEnergyOn_nonneg _ A B hu hX
  filter_upwards [hb, hδ, hgrow.eventually_ge_atTop 5] with X h hd hg
  exact h (δ X) hd.1 hd.2 hg u hu

/-- Local excess of the power spectrum over its exact Plancherel density. -/
def centeredPowerExcess (A B X : ℝ) (t : Circle₁) : ℝ :=
  let I := Ioc ⌊A*X⌋₊ ⌊B*X⌋₊
  ‖polynomial I (fun n => Λ n - 1) t‖^2 - ∑ n ∈ I, (Λ n - 1)^2

/-- Cosine probes on the central arc, without a Fejér weight or width parameter. -/
def localMode (A B X δ : ℝ) (h : ℕ) : ℝ :=
  cosineMoment (centralArc δ) (centeredPowerExcess A B X) h / X

/-- Normalized signed excess over the constant Plancherel density on the central arc. -/
def localCovariance (A B u X δ : ℝ) : ℝ :=
  (∫ t in centralArc δ, kernel (shiftWidth u X) (u * Real.log X - shiftWidth u X) t *
    centeredPowerExcess A B X t ∂AddCircle.haarAddCircle)
      / (X * (Real.log X)^2)

private def normalizedKernelMass (s : Set Circle₁) (u X : ℝ) : ℝ :=
  energyOn s (shiftWidth u X) (u * Real.log X - shiftWidth u X) {0} (fun _ => 1) / Real.log X

private theorem localCovariance_eq (A B u X δ : ℝ) :
    localCovariance A B u X δ = centeredEnergyOn (centralArc δ) A B u X -
      ((∑ n ∈ Ioc ⌊A*X⌋₊ ⌊B*X⌋₊, (Λ n - 1)^2) / (X * Real.log X)) *
        normalizedKernelMass (centralArc δ) u X := by
  unfold localCovariance centeredPowerExcess centeredEnergyOn normalizedKernelMass
  rw [← energyOn_sub_diagonal]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

private theorem tendsto_kernelMass_centralArc {u : ℝ} (hu : 0 < u) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop) :
    Tendsto (fun X => normalizedKernelMass (centralArc (δ X)) u X) atTop (𝓝 u) := by
  have ht : Tendsto (fun X => normalizedKernelMass (centralArc (δ X))ᶜ u X) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ ((tendsto_const_nhds (x := (20 : ℝ))).div_atTop hgrow)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      exact div_nonneg
        (energyOn_nonneg _ _ (fraction_bounds hu hX).1 (fraction_bounds hu hX).2 _ _)
        (Real.log_pos hX).le
    filter_upwards [hδ, hgrow.eventually_ge_atTop 5, eventually_gt_atTop (1 : ℝ)]
      with X hd hg hX
    have he := offArc_energy_le_of_short_bound hd.1 hd.2 hg (zero_le_one : (0 : ℝ) ≤ 1)
      (shiftWidth u X) (fraction_bounds hu hX).1 (fraction_bounds hu hX).2 {0} (fun _ => 1)
      (fun j _ => by rw [energy_singleton_zero]; simp)
    exact (div_le_div_of_nonneg_right he (Real.log_pos hX).le).trans_eq (by ring)
  have h := (tendsto_const_nhds (x := u)).sub ht
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hf := energy_split_arc (δ X) (shiftWidth u X) (u * Real.log X - shiftWidth u X)
    {0} (fun _ => 1)
  rw [energy_singleton_zero] at hf
  unfold normalizedKernelMass
  apply (eq_div_iff (Real.log_pos hX).ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ (Real.log_pos hX).ne']
  linarith

private theorem centered_energy_of_localCovariance_tail
    {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop)
    (htail : Tendsto (fun X => centeredEnergyOn (centralArc (δ X))ᶜ A B u X) atTop (𝓝 0))
    (hc : Tendsto (fun X => localCovariance A B u X (δ X)) atTop (𝓝 0)) :
    Tendsto (fun X => annularEnergy A B u X (fun n => Λ n - 1) / (X * (Real.log X)^2))
      atTop (𝓝 ((B - A) * u)) := by
  have hm := (annular_centered_diagonal_limit hA hAB).mul
    (tendsto_kernelMass_centralArc hu δ hδ hgrow)
  have hn := hc.add hm
  rw [zero_add] at hn
  have hnear : Tendsto (fun X => centeredEnergyOn (centralArc (δ X)) A B u X)
      atTop (𝓝 ((B - A) * u)) := hn.congr fun X => by rw [localCovariance_eq, sub_add_cancel]
  have hf := hnear.add htail
  rw [add_zero] at hf
  exact hf.congr fun X => centeredEnergyOn_split (δ X) A B u X

/-- A signed off-diagonal estimate on the central arc transfers to the full centered variance. -/
theorem centered_energy_of_localCovariance (published : GPYPrimePairSieve)
    {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop)
    (hc : Tendsto (fun X => localCovariance A B u X (δ X)) atTop (𝓝 0)) :
    Tendsto (fun X => annularEnergy A B u X (fun n => Λ n - 1) / (X * (Real.log X)^2))
      atTop (𝓝 ((B - A) * u)) :=
  centered_energy_of_localCovariance_tail hA hAB hu δ hδ hgrow
    (tendsto_centered_offArc_of_sieve published hA hAB hu δ hδ hgrow) hc

/-- On the coarser shrinking arcs, Plancherel alone supplies the requisite tail bound. -/
theorem centered_energy_of_localCovariance_plancherel {A B u : ℝ}
    (hA : 0 < A) (hAB : A < B) (hu : 0 < u) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => (δ X)^2 * Real.log X) atTop atTop)
    (hc : Tendsto (fun X => localCovariance A B u X (δ X)) atTop (𝓝 0)) :
    Tendsto (fun X => annularEnergy A B u X (fun n => Λ n - 1) / (X * (Real.log X)^2))
      atTop (𝓝 ((B - A) * u)) := by
  have hg : Tendsto (fun X => δ X * Real.log X) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hgrow.eventually_ge_atTop b, hδ, eventually_gt_atTop (1 : ℝ)] with X hb hd hX
    exact hb.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hd.1.le (sub_nonneg.mpr hd.2)]) (Real.log_pos hX).le)
  exact centered_energy_of_localCovariance_tail hA hAB hu δ hδ hg
    (tendsto_centered_offArc hA hAB hu δ (hδ.mono fun _ h => h.1) hgrow) hc

/-- One fixed-width sharp upper bound (from the published sieve) and localized covariances
at each positive width give the actual sharp prime-pair law. -/
theorem sharpPairAverage_of_localCovariance (published : GPYPrimePairSieve)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop)
    (hc : ∀ u : ℝ, 0 < u → Tendsto (fun X => localCovariance A B u X (δ X)) atTop (𝓝 0))
    {d : ℝ} (hd : 0 < d) :
    Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B - A) * d)) :=
  sharpPairAverage_of_centered_energy hA hAB
    (fun u hu => centered_energy_of_localCovariance published hA hAB hu δ hδ hgrow (hc u hu)) hd

/-- The normalized peak of the Fejér kernel multiplies the error in the unweighted local modes. -/
theorem abs_localCovariance_le_modes {A B u X δ e : ℝ} (hu : 0 < u)
    (hX : 1 < X) (hL : 1 ≤ Real.log X)
    (hm : ∀ h ≤ shiftWidth u X, |localMode A B X δ h| ≤ e) :
    |localCovariance A B u X δ| ≤ (u^2 + 1) * e := by
  have hx : 0 < X := by linarith
  have hl := Real.log_pos hX
  have he : 0 ≤ e := (abs_nonneg _).trans (hm 0 (Nat.zero_le _))
  let H := shiftWidth u X
  let r := u * Real.log X - H
  have hfrac : 0 ≤ r ∧ r ≤ 1 := fraction_bounds hu hX
  have hcont : Continuous (centeredPowerExcess A B X) :=
    ((continuous_polynomial _ _).norm.pow 2).sub continuous_const
  have hb (h : ℕ) (hh : h ≤ H) :
      |cosineMoment (centralArc δ) (centeredPowerExcess A B X) h| ≤ e * X := by
    have hbound := hm h hh
    rwa [localMode, abs_div, abs_of_pos hx, div_le_iff₀ hx] at hbound
  have htest := abs_integral_kernel_mul_le_modes (centralArc δ) H hfrac.1
    (centeredPowerExcess A B X) hcont hb
  have hpeak : kernel H r 0 / (Real.log X)^2 ≤ u^2 + 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    rw [kernel_at_zero, show (H : ℝ) + r = u * Real.log X by dsimp [r]; ring]
    nlinarith [sq_nonneg (r - 1/2), sq_nonneg (Real.log X - 1)]
  rw [localCovariance, abs_div, abs_of_pos (mul_pos hx (sq_pos_of_pos hl))]
  calc
    _ ≤ (kernel H r 0 * (e * X)) / (X * (Real.log X)^2) :=
      div_le_div_of_nonneg_right htest (mul_pos hx (sq_pos_of_pos hl)).le
    _ = (kernel H r 0 / (Real.log X)^2) * e := by field_simp [hx.ne', hl.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpeak he

/-- Uniform cancellation of the localized cosine moments for h = O(log X) suffices.
The error function can depend on the fixed band multiplier v. -/
theorem sharpPairAverage_of_localModes (published : GPYPrimePairSieve)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) (δ : ℝ → ℝ)
    (hδ : ∀ᶠ X in atTop, 0 < δ X ∧ δ X ≤ 1)
    (hgrow : Tendsto (fun X => δ X * Real.log X) atTop atTop)
    (hm : ∀ v : ℝ, 0 < v → ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ X in atTop, ∀ h ≤ shiftWidth v X, |localMode A B X (δ X) h| ≤ e X)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B - A) * d)) := by
  apply sharpPairAverage_of_localCovariance published hA hAB δ hδ hgrow _ hd
  intro u hu
  obtain ⟨e, he, hmodes⟩ := hm u hu
  have hl := he.const_mul (u^2 + 1)
  rw [mul_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [hmodes, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hb hX hL
  exact abs_localCovariance_le_modes hu hX hL hb

end RiemannResearch.Analysis.LogarithmicPrimePairs

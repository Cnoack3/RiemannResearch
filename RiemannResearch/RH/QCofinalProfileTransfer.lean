/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.RH.QMertensUniformDefectSlope
import Mathlib.NumberTheory.Bertrand
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.RH.QCofinalHarmonicWitness
import RiemannResearch.Analysis.VinogradovKorobovProfile

/-!
# Cofinal bounds from a uniform defect slope

The profile may be chosen separately from the finite prime test. Each cutoff uses its own sign and legal head.
-/

/-! # The complete-tail cost of power-sized Möbius heads

A square-root tail bound absorbs both a power below one half and the harmonic
cost of the finite prime-residue majorant.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-- The complete-tail cost vanishes for every head exponent strictly below
one half. The outer cutoff can tend to infinity arbitrarily slowly. -/
theorem vk_far_cost_tendsto (θ : ℝ) (hθ : θ < 1 / 2) :
    Tendsto (fun X : ℕ => ((X : ℝ) ^ θ * (1 + 2 * (harmonic (X + 1) : ℝ))) / Real.sqrt ((X : ℝ) + 1)) atTop (𝓝 0) := by
  let b : ℝ := 1 / 2 - θ
  have hb : 0 < b := sub_pos.mpr hθ
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp hnat
  have hl : Tendsto (fun X : ℕ => Real.log (X : ℝ) / (X : ℝ) ^ b) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero.comp hnat
  have hlim : Tendsto (fun X : ℕ => (5 + 2 * Real.log (X : ℝ)) / (X : ℝ) ^ b)
      atTop (𝓝 0) := by
    have hh := (hp.const_div_atTop (5 : ℝ)).add (hl.const_mul 2)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun X : ℕ => by dsimp; ring)
  have hH (X : ℕ) : 0 ≤ (harmonic (X + 1) : ℝ) :=
    (Real.log_nonneg (show (1 : ℝ) ≤ ((X + 1 + 1 : ℕ) : ℝ) by
      exact_mod_cast (show 1 ≤ X + 1 + 1 by omega))).trans (log_add_one_le_harmonic (X + 1))
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun X : ℕ => div_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (by linarith [hH X])) (Real.sqrt_nonneg _))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hx : (0 : ℝ) < X := by linarith
    have hXle : ((X + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by push_cast; linarith
    have hhlog := Real.log_le_log (show 0 < ((X + 1 : ℕ) : ℝ) by positivity) hXle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at hhlog
    have hHbound : 1 + 2 * (harmonic (X + 1) : ℝ) ≤ 5 + 2 * Real.log (X : ℝ) := by
      linarith only [harmonic_le_one_add_log (X + 1), hhlog,
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs : (X : ℝ) ^ θ / Real.sqrt ((X : ℝ) + 1) ≤ 1 / (X : ℝ) ^ b := by
      calc
        _ ≤ (X : ℝ) ^ θ / Real.sqrt (X : ℝ) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (Real.sqrt_pos.mpr hx)
            (Real.sqrt_le_sqrt (by linarith))
        _ = (X : ℝ) ^ (-b) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
          congr 1
          dsimp [b]
          ring
        _ = _ := by rw [Real.rpow_neg hx.le, one_div]
    calc
      _ = ((X : ℝ) ^ θ / Real.sqrt ((X : ℝ) + 1)) * (1 + 2 * (harmonic (X + 1) : ℝ)) := by ring
      _ ≤ (1 / (X : ℝ) ^ b) * (5 + 2 * Real.log (X : ℝ)) :=
        mul_le_mul hs hHbound (by linarith [hH X]) (by positivity)
      _ = _ := by ring

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-!
# Legal Möbius heads at arbitrary real powers of a physical cutoff

Rounding X ^ θ upward preserves the lower VK comparison. Bertrand's theorem
then supplies a prime conductor with a uniform factor four in the upper size.
-/

noncomputable section
open Filter

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis

theorem vk_exists_scaled_head (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, Squarefree (N + 1) ∧ 0 < N ∧ (X : ℝ) ^ θ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * (X : ℝ) ^ θ ∧ θ ^ (3 / 5 : ℝ) * vkProfile (X : ℝ) ≤ vkProfile (N : ℝ) := by
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ => (X : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp hnat
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hpow.eventually (eventually_gt_atTop (Real.exp 1)), hpow.eventually vkProfile_eventually_mono]
    with X hX hpowlarge hmono
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans_le hx1
  have hp1 : (1 : ℝ) ≤ (X : ℝ) ^ θ := Real.one_le_rpow hx1 hθ.le
  have hp0 : (0 : ℝ) < (X : ℝ) ^ θ := zero_lt_one.trans_le hp1
  let k : ℕ := ⌈(X : ℝ) ^ θ⌉₊
  have hklo : (X : ℝ) ^ θ ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ (X : ℝ) ^ θ + 1 := (Nat.ceil_lt_add_one hp0.le).le
  have hk0 : 0 < k := by exact_mod_cast hp0.trans_le hklo
  obtain ⟨p, hp, hkp, hpk⟩ := Nat.exists_prime_lt_and_le_two_mul k hk0.ne'
  let N := p-1
  have hNk : k ≤ N := by dsimp [N]; omega
  have hNp : N + 1 = p := by dsimp [N]; omega
  have hNmax : (N : ℝ) ≤ 2 * (k : ℝ) := by
    exact_mod_cast (show N ≤ 2 * k by dsimp [N]; omega)
  have hNL : (X : ℝ) ^ θ ≤ (N : ℝ) := hklo.trans (by exact_mod_cast hNk)
  have hxle : (X : ℝ) ^ θ ≤ (X : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hθ1.le
  have hlog : θ * Real.log (X : ℝ) ≤ Real.log ((X : ℝ) ^ θ) := by
    simp only [Real.log_rpow hx0, mul_comm, le_refl]
  have hbase := QMertensFirstMoment.vkProfile_lower_of_log_ratio hpowlarge hxle hθ.le hlog
  exact ⟨N, by simpa only [hNp] using hp.squarefree, hk0.trans_le hNk, hNL, by linarith only [hNmax, hkhi, hp1],
    hbase.trans (hmono _ hNL)⟩

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-!
# A cofinal one-sided prefix bound at a general Mertens profile

A common small slope of each legal defect controls the prefix cost. A power
strictly below one half makes its remaining harmonic tail vanish. The profile
and its multiplicative comparison between the head and the cutoff are parameters.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability QSignedTailRigidity QAnnihilatorTailEscape
open RiemannResearch.Analysis.CofinalMoments

/-- Choose a legal head exponent and a decay rate strictly below their endpoint values. -/
theorem exists_profile_cutoff_parameters {a b d : ℝ} (hd : 0 < d) (hb : 0 ≤ b)
    (hba : b < a * (1 / 2 : ℝ) ^ d) :
    ∃ θ c : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ 0 < c ∧ c < a ∧ b < c * θ ^ d := by
  have ht : 0 < (1 / 2 : ℝ) ^ d := by positivity
  obtain ⟨c, hlo, hca⟩ := exists_between ((div_lt_iff₀ ht).mpr hba)
  have hc : 0 < c := (div_nonneg hb ht.le).trans_lt hlo
  have hbc : b / c < (1 / 2 : ℝ) ^ d := by
    apply (div_lt_iff₀ hc).mpr
    simpa only [mul_comm c] using (div_lt_iff₀ ht).mp hlo
  let t := (b / c) ^ d⁻¹
  have ht₀ : 0 ≤ t := Real.rpow_nonneg (div_nonneg hb hc.le) _
  have hth : t < 1 / 2 := by
    calc
      t < ((1 / 2 : ℝ) ^ d) ^ d⁻¹ :=
        Real.rpow_lt_rpow (div_nonneg hb hc.le) hbc (inv_pos.mpr hd)
      _ = 1 / 2 := by rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]; simp [hd.ne']
  obtain ⟨θ, hθt, hθ⟩ := exists_between hth
  refine ⟨θ, c, ht₀.trans_lt hθt, hθ, hc, hca, ?_⟩
  have he : t ^ d = b / c := by
    dsimp only [t]
    rw [← Real.rpow_mul (div_nonneg hb hc.le)]
    simp [hd.ne']
  have hlt := Real.rpow_lt_rpow ht₀ hθt hd
  rw [he] at hlt
  simpa only [mul_comm c] using (div_lt_iff₀ hc).mp hlt

/-- Uniform exponential decay of the defect slopes at `V N` transfers a cofinal
one-sided bound at `V X` to vanishing of the mean of the actual witness. -/
theorem witness_mean_zero_of_cofinal_profile_fraction (V : ℕ → ℝ) (c θ b t : ℝ)
    (hc : 0 < c) (hθ : 0 < θ) (hhalf : θ < 1 / 2)
    (hb : 0 ≤ b) (hgap : b < c * t) (hV : Tendsto V atTop atTop)
    (hslope : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |qSequence (defect N) n| ≤
      (n : ℝ) * Real.exp (-c * V N))
    (hscales : ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, Squarefree (N + 1) ∧ 0 < N ∧ (X : ℝ) ^ θ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * (X : ℝ) ^ θ ∧ t * V X ≤ V N)
    (hgood : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ Real.exp (b * V X)) :
    inner ℝ qOne witness = 0 := by
  let U := smoothingMoment + 1 / zetaTwo
  let B := ‖witness‖ ^ 2 + 2 / zetaTwo
  let g := c * t - b
  have hZ := zetaTwo_pos
  have hU : 0 ≤ U := add_nonneg smoothingMoment_nonneg (div_nonneg zero_le_one hZ.le)
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _) (div_nonneg zero_le_two hZ.le)
  have hg : 0 < g := sub_pos.mpr hgap
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun X : ℕ => Real.exp (-g * V X)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hg hV)
  let F := fun X : ℕ => (2 * U) * Real.exp (-g * V X) + (12 * B) * (((X : ℝ) ^ θ * (1 + 2 * (harmonic (X + 1) : ℝ))) / Real.sqrt ((X : ℝ) + 1))
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [F, mul_zero, add_zero] using
      (he.const_mul (2 * U)).add ((vk_far_cost_tendsto θ hhalf).const_mul (12 * B))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hslope
  have hxθ : Tendsto (fun X : ℕ => (X : ℝ) ^ θ) atTop atTop := (tendsto_rpow_atTop hθ).comp hnat
  refine eq_zero_of_frequently_abs_le (f := F) ?_ hF
  refine (hgood.and_eventually (hscales.and
    ((hxθ.eventually (eventually_ge_atTop (N₀ : ℝ))).and
      (hV.eventually (eventually_ge_atTop 0))))).mono ?_
  rintro X ⟨hX, hcut, hlarge, hV₀⟩
  obtain ⟨N, hsf, hN, hlow, hupp, hratio⟩ := hcut
  have hNN : N₀ ≤ N := by exact_mod_cast hlarge.trans hlow
  let δ := Real.exp (-c * V N)
  have hδ := (Real.exp_pos (-c * V N)).le
  have hp := witness_mean_le_capped_harmonic_prefix N X δ hN hδ hsf
    (fun n => by simpa only [mul_comm δ] using hN₀ N hNN n)
  have he₁ : 1 ≤ Real.exp (b * V X) := Real.one_le_exp_iff.mpr (mul_nonneg hb hV₀)
  have hsum : smoothingMoment + minimumHarmonicPrefix X / zetaTwo ≤ U * Real.exp (b * V X) := by
    calc
      _ ≤ smoothingMoment * Real.exp (b * V X) + Real.exp (b * V X) / zetaTwo := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left he₁ smoothingMoment_nonneg
        · exact div_le_div_of_nonneg_right hX hZ.le
      _ = _ := by dsimp only [U]; ring
  have hexp : δ * Real.exp (b * V X) ≤ Real.exp (-g * V X) := by
    have hδ' : δ ≤ Real.exp (-c * (t * V X)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr hc.le))
    calc
      _ ≤ Real.exp (-c * (t * V X)) * Real.exp (b * V X) :=
        mul_le_mul_of_nonneg_right hδ' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [g]; ring
  have hnear : 2 * δ * (smoothingMoment + minimumHarmonicPrefix X / zetaTwo) ≤ (2 * U) * Real.exp (-g * V X) := by
    calc
      _ ≤ (2 * δ) * (U * Real.exp (b * V X)) := mul_le_mul_of_nonneg_left hsum (mul_nonneg zero_le_two hδ)
      _ = (2 * U) * (δ * Real.exp (b * V X)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg zero_le_two hU)
  let h := (harmonic (X + 1) : ℝ)
  have hh : 0 ≤ h :=
    (Real.log_nonneg (show (1 : ℝ) ≤ ((X + 1 + 1 : ℕ) : ℝ) by
      exact_mod_cast (show 1 ≤ X + 1 + 1 by omega))).trans (log_add_one_le_harmonic (X + 1))
  have hcap : 2 * ((3 * (N : ℝ)) * h) + 3 * N ≤ 12 * (X : ℝ) ^ θ * (1 + 2 * h) := by
    calc
      _ = 3 * ((N : ℝ) * (1 + 2 * h)) := by ring
      _ ≤ 3 * ((4 * (X : ℝ) ^ θ) * (1 + 2 * h)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hupp (by positivity)) (by norm_num)
      _ = _ := by ring
  have hfar : (2 * ((3 * (N : ℝ)) * h) + 3 * N) * (∑' n : ℕ, if X<n then |signedCoefficient witness n| else 0) ≤ (12 * B) * (((X : ℝ) ^ θ * (1 + 2 * h)) / Real.sqrt ((X : ℝ) + 1)) := by
    calc
      _ ≤ (2 * ((3 * (N : ℝ)) * h) + 3 * N) * (B / Real.sqrt ((X : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (witness_charge_tail_le_div_sqrt X) (by positivity)
      _ ≤ (12 * (X : ℝ) ^ θ * (1 + 2 * h)) * (B / Real.sqrt ((X : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hcap (div_nonneg hB (Real.sqrt_nonneg _))
      _ = _ := by ring
  exact hp.trans (add_le_add hnear hfar)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

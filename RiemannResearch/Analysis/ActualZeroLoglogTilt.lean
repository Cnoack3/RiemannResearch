import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroInghamHorizontalEnergy
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exponential tilts of absolute zero-displacement moments

For every fixed B, tilts v ≤ B log T / log log T retain the untilted
moment scale. The sharper cap can be integrated exactly at horizontal
displacement (3/2) log log T / log T, giving a frequency-dependent
polynomial up to the (4/3) log T linear tilt. The central term also has
a version retaining the exact number of off-line copies. The density input
is adapted in ActualZeroInghamHorizontalEnergy from Chourasiya–Simonič,
Theorem 1, https://arxiv.org/abs/2507.15184.
-/
noncomputable section
open Filter Zeta23 Set
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The central and Ingham envelopes can be made to meet exactly at
(3/2) log log T / log T. One constant and height threshold work for every
positive order and every tilt strictly below (4/3) log T. -/
theorem exists_ingham_tilted_moment_exact_crossing :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ p : ℕ, ∀ v : ℝ,
      0 ≤ v → v < (4/3) * Real.log T →
      let L := Real.log T
      let d := (3/2) * (Real.log L / L)
      let q := (4/3)*L
      (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v*copyDisplacement T i)) / T ≤
        C*L * Real.exp (v*d) * (q * gammaEndpointPolynomial (p+1) ((q-v)*d) / (q-v)^(p+2)) := by
  obtain ⟨H,hH,hing⟩ := exists_strictTail_ingham_exponential
  let C := max 1 H
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  have hc := eventually_count_le_log_of_lt (show 1/(2*Real.pi) < (1:ℝ) by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three])
  have hscale : Tendsto (fun T : ℝ => Real.log (Real.log T) / Real.log T) atTop (𝓝 0) :=
    Real.log_div_self_tendsto_zero.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1)), hc,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    hscale.eventually_le_const (by norm_num : (0:ℝ)<1/3)] with T hT hc hℓ hgeom
  intro p v hv hvq
  let L := Real.log T
  let d := (3/2)*(Real.log L/L)
  let q := (4/3)*L
  have ht : 1 < T := by linarith [(le_max_left (2:ℝ) (Real.exp 1)).trans hT]
  have ht0 := zero_lt_one.trans ht
  have hL : 0 < L := Real.log_pos ht
  change 0 < Real.log L at hℓ
  have hd : d ∈ Icc (0 : ℝ) (1/2) :=
    ⟨mul_nonneg (by norm_num) (div_nonneg hℓ.le hL.le), by
      change (3/2)*(Real.log (Real.log T)/Real.log T) ≤ 1/2
      linarith only [hgeom]⟩
  have hF : strictTail T 0 ≤ C*T*L := calc
    _ ≤ (Ncount 0 T : ℝ) := strictTail_le_count T 0
    _ ≤ 1*T*L := by simpa only [one_mul,mul_one,mul_comm,L] using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le) hL.le
  have hcross : (C*T*L^3)*Real.exp (-q*d) = C*T*L := by
    have hqd : -q*d = -(Real.log L+Real.log L) := by dsimp [q,d]; field_simp <;> ring
    rw [hqd, Real.exp_neg, Real.exp_add, Real.exp_log hL]
    field_simp
  have htail (t : ℝ) (ht' : t ∈ Icc (0:ℝ) (1/2)) :
      strictTail T t ≤ C*T*L^3*Real.exp (-q*t) := by
    have hh : strictTail T t ≤ H*T*L^3*Real.exp (-q*t) := by
      simpa only [q,L,neg_mul] using hing T hT t ht'.1
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ht0.le) (pow_nonneg hL.le 3)
  have hh := tiltedMoment_le_compensated_subcritical (T := T) p hF (by positivity : 0 ≤ C*T*L^3)
    hv hvq hd hcross htail
  apply (div_le_iff₀ ht0).mpr
  apply hh.trans_eq
  ring

/-- At a linear tilt λ log T the logarithmic power is exactly (3/2)λ
above the untilted moment scale. The polynomial records every lower order. -/
theorem exists_ingham_linear_tilt_power_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ p : ℕ, ∀ slope : ℝ, 0 ≤ slope → slope < 4/3 →
      let L := Real.log T
      let ℓ := Real.log L
      (∑ i : Copies T, copyDisplacement T i^(p+1) *
        Real.exp ((slope*L)*copyDisplacement T i)) / T ≤
        (C*(4/3) * L^((3/2)*slope) / ((4/3-slope)^(p+2)*L^p)) *
          gammaEndpointPolynomial (p+1) ((2-(3/2)*slope)*ℓ) := by
  obtain ⟨C,hC,h⟩ := exists_ingham_tilted_moment_exact_crossing
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hT ht
  intro p slope hslope hquick
  let L := Real.log T
  let ℓ := Real.log L
  have hL : 0 < L := Real.log_pos ht
  have hh := hT p (slope*L) (mul_nonneg hslope hL.le) (mul_lt_mul_of_pos_right hquick hL)
  have h1 : (slope*L)*((3/2)*(ℓ/L)) = ℓ*((3/2)*slope) := by field_simp <;> ring
  have h2 : (4/3)*L-slope*L = (4/3-slope)*L := by ring
  have h3 : ((4/3-slope)*L)*((3/2)*(ℓ/L)) = (2-(3/2)*slope)*ℓ := by field_simp <;> ring
  apply hh.trans_eq
  change C*L*Real.exp ((slope*L)*((3/2)*(ℓ/L))) *
    (((4/3)*L)*gammaEndpointPolynomial (p+1) (((4/3)*L-slope*L)*((3/2)*(ℓ/L))) /
      ((4/3)*L-slope*L)^(p+2)) =
    (C*(4/3)*L^((3/2)*slope) / ((4/3-slope)^(p+2)*L^p)) *
      gammaEndpointPolynomial (p+1) ((2-(3/2)*slope)*ℓ)
  rw [h1,h2,h3,Real.rpow_def_of_pos hL,mul_pow,pow_add L p 2]
  dsimp only [ℓ]
  field_simp [sub_ne_zero.mpr hquick.ne']
  <;> ring

/-- In the full band v ≤ (2/β) log T for any β > 3/2, the frequency
dependence remains explicit in the exponential factor at the cutoff. The central term retains the exact number of off-line zero copies.
The second term uses the Ingham tail with exponent 4/3. -/
theorem exists_ingham_tilted_moment_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 3/2 < β →
      ∀ᶠ T : ℝ in atTop, ∀ p : ℕ, ∀ v : ℝ, 0 ≤ v → v ≤ (2/β) * Real.log T →
        (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v * copyDisplacement T i)) / T ≤
          Real.exp (v * (β * Real.log (Real.log T)/Real.log T)) * (β^(p+1) * (strictTail T 0/(T*Real.log T)) *
            (Real.log (Real.log T))^(p+1) + ((p+1).factorial : ℝ)*(4/3)*C/(4/3-2/β)^(p+2)) / (Real.log T)^p := by
  obtain ⟨C,hC,hing⟩ := exists_strictTail_ingham_exponential
  refine ⟨C,hC,?_⟩
  intro β hβ
  have hβ0 : 0 < β := by linarith
  let k := 2/β
  have hk : 0 < k := div_pos (by norm_num) hβ0
  have hgap : k < 4/3 := (div_lt_iff₀ hβ0).mpr (by linarith)
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with T hT hℓ
  intro p v hv hvw
  let L := Real.log T
  let ℓ := Real.log L
  let b := β*ℓ/L
  let w := k*L
  have hT1 : 1 < T := by linarith [(le_max_left (2:ℝ) (Real.exp 1)).trans hT]
  have hT0 := zero_lt_one.trans hT1
  have hL : 0 < L := Real.log_pos hT1
  change 0 < ℓ at hℓ
  change v ≤ w at hvw
  have hb : 0 < b := div_pos (mul_pos hβ0 hℓ) hL
  have hkw : w < (4/3)*L := mul_lt_mul_of_pos_right hgap hL
  have hwb : w*b = 2*ℓ := by dsimp [w,b,k]; field_simp
  have htail := tiltedMoment_le_expTail (T := T) (v := w) (q := (4/3)*L) p (show 0 ≤ C*T*L^3 by positivity)
    (mul_nonneg hk.le hL.le) hkw (fun t ht => by simpa only [L,neg_mul] using hing T hT t ht.1)
  let E := Real.exp (v*b)
  have hpoint (i : Copies T) :
      copyDisplacement T i^(p+1) * Real.exp (v * copyDisplacement T i) ≤
        (E*b^(p+1))*(if 0 < copyDisplacement T i then 1 else 0) +
          (E/L^2)*(copyDisplacement T i^(p+1)*Real.exp (w * copyDisplacement T i)) := by
    let d := copyDisplacement T i
    have hd : 0 ≤ d := abs_nonneg _
    change d^(p+1) * Real.exp (v*d) ≤ (E*b^(p+1))*(if 0 < d then 1 else 0) + (E/L^2)*
      (d^(p+1) * Real.exp (w*d))
    have hE : 0 < E := Real.exp_pos _
    by_cases hpos : 0 < d
    swap
    · have hz := le_antisymm (le_of_not_gt hpos) hd
      simp [hz]
    rw [if_pos hpos, mul_one]
    by_cases hnear : d ≤ b
    · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnear hv)
      calc
        _ ≤ b^(p+1)*E := mul_le_mul (pow_le_pow_left₀ hd hnear _) he (Real.exp_pos _).le (by positivity)
        _ ≤ _ := by rw [mul_comm (b^(p+1))]; exact le_add_of_nonneg_right (by positivity)
    · have hdiff := mul_le_mul_of_nonneg_left (le_of_not_ge hnear) (sub_nonneg.mpr hvw)
      have harg : v*d ≤ v*b - 2*ℓ + w*d := by nlinarith only [hdiff, hwb]
      have h2 : Real.exp (2*ℓ) = L^2 := by
        rw [show 2*ℓ = ℓ+ℓ by ring, Real.exp_add, Real.exp_log hL, sq]
      have he : Real.exp (v*d) ≤ (E/L^2)*Real.exp (w*d) := by
        apply (Real.exp_le_exp.mpr harg).trans_eq
        rw [Real.exp_add, Real.exp_sub, h2]
      calc
        _ ≤ d^(p+1)*((E/L^2)*Real.exp (w*d)) := mul_le_mul_of_nonneg_left he (pow_nonneg hd (p+1))
        _ = (E/L^2)*(d^(p+1)*Real.exp (w*d)) := by ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hE.le (pow_nonneg hb.le (p+1)))
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hE : 0 < E := Real.exp_pos _
  have hh := hsum.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail
    (div_nonneg hE.le (sq_nonneg L))))
  apply (div_le_iff₀ hT0).mpr
  apply hh.trans_eq
  change (E*b^(p+1))*strictTail T 0 + E/L^2 *
    ((C*T*L^3)*(((p+1).factorial : ℝ)*((4/3)*L)/((4/3)*L-w)^(p+2))) =
    E*(β^(p+1)*(strictTail T 0/(T*L))*ℓ^(p+1) +
      ((p+1).factorial : ℝ)*(4/3)*C/(4/3-k)^(p+2))/L^p*T
  have hp : (4/3)*L-w = (4/3-k)*L := by dsimp [w]; ring
  rw [hp,mul_pow]
  dsimp [b]
  rw [div_pow, mul_pow]
  simp only [pow_add]
  field_simp [sub_ne_zero.mpr hgap.ne']
  <;> ring

/-- Quartic form with the signed horizontal displacement used in the raw Gram kernel. -/
theorem exists_ingham_tilted_fourth_moment_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 3/2 < β →
      ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ (2/β) * Real.log T →
        (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v * |i.1.1.re-1/2|)) / T ≤
          Real.exp (v * (β * Real.log (Real.log T)/Real.log T)) * (β^4 * (strictTail T 0/(T*Real.log T)) *
            (Real.log (Real.log T))^4 + 32*C/(4/3-2/β)^5) / (Real.log T)^3 := by
  obtain ⟨C, hC, h⟩ := exists_ingham_tilted_moment_envelope
  refine ⟨C, hC, ?_⟩
  intro β hβ
  filter_upwards [h β hβ] with T hT
  intro v hv hvw
  have hh := hT 3 v hv hvw
  have hs (x : ℝ) : |x|^4 = x^4 := by
    rw [show (4 : ℕ) = 2*2 by decide, pow_mul, sq_abs, ← pow_mul]
  norm_num [Nat.factorial] at hh
  simpa only [copyDisplacement, hs] using hh

/-- Uniform bound over each band of size B log T / log log T, with no
density assumption on the theorem. -/
theorem exists_ingham_tilted_fourth_moment_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v →
      v ≤ B * Real.log T / Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v * |i.1.1.re-1/2|)) / T ≤
        K * (Real.log (Real.log T))^4 / (Real.log T)^3 := by
  obtain ⟨C, hC, hcap⟩ := exists_ingham_tilted_fourth_moment_envelope
  let K := Real.exp (B*2)*(16+7776*C)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  have hn := eventually_count_le_log_of_lt (show 1/(2*Real.pi) < (1:ℝ) by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three])
  filter_upwards [hcap 2 (by norm_num),hn,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 B)]
    with T he hc hT hlarge
  intro v hv hvB
  change max 1 B ≤ Real.log (Real.log T) at hlarge
  have hℓ := (le_max_left 1 B).trans hlarge
  have hBℓ := (le_max_right 1 B).trans hlarge
  have hT0 := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hoff : strictTail T 0 / (T*Real.log T) ≤ 1 := by
    apply (div_le_one (mul_pos hT0 hL)).mpr
    exact (strictTail_le_count T 0).trans (by simpa only [mul_one,one_mul,mul_comm] using hc)
  have h4 := one_le_pow₀ hℓ (n := 4)
  have hf : 32*C/(4/3-(2:ℝ)/2)^5 = 7776*C := by ring
  have hℓ0 := zero_lt_one.trans_le hℓ
  have hvL : v ≤ (2/(2:ℝ))*Real.log T := by
    norm_num only [div_self (by norm_num : (2:ℝ) ≠ 0), one_mul]
    apply hvB.trans
    apply (div_le_iff₀ hℓ0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hBℓ hL.le]
  have hexp : Real.exp (v*(2*Real.log (Real.log T)/Real.log T)) ≤ Real.exp (B*2) := by
    apply Real.exp_le_exp.mpr
    apply (mul_le_mul_of_nonneg_right hvB (by positivity)).trans_eq
    field_simp [hℓ0.ne', hL.ne']
  have hh := he v hv hvL
  rw [hf] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  change Real.exp (v*(2*Real.log (Real.log T)/Real.log T)) *
    (2^4*(strictTail T 0/(T*Real.log T))*(Real.log (Real.log T))^4 + 7776*C) ≤
    (Real.exp (B*2)*(16+7776*C))*(Real.log (Real.log T))^4
  rw [mul_assoc (Real.exp (B*2))]
  apply mul_le_mul hexp _ (by have ht := strictTail_nonneg T 0; positivity) (Real.exp_pos _).le
  have hcen := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hoff
    (by norm_num : (0:ℝ) ≤ 2^4)) (pow_nonneg (zero_le_one.trans hℓ) 4)
  have hrem := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 7776*C by positivity)
  nlinarith only [hcen,hrem]

/-- Each fixed loglog tilt band is eventually contained in the stronger
Ingham band B log T / log log T. -/
theorem exists_loglog_tilted_fourth_moment_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v →
      v ≤ B * Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re - 1/2)^4 * Real.exp (v * |i.1.1.re - 1/2|)) / T ≤
        K * (Real.log (Real.log T))^4 / (Real.log T)^3 := by
  obtain ⟨K,hK,he⟩ := exists_ingham_tilted_fourth_moment_bound B hB
  refine ⟨K,hK,?_⟩
  have hsmall : Tendsto (fun T : ℝ => (Real.log (Real.log T))^2 / Real.log T) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
    apply h.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T ht
    simp only [Function.comp_def,Real.exp_neg,Real.exp_log ht,div_eq_mul_inv]
  filter_upwards [he,hsmall.eventually_le_const zero_lt_one,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    eventually_gt_atTop (1:ℝ)] with T hT hratio hℓ ht
  intro v hv hbound
  change 0 < Real.log (Real.log T) at hℓ
  apply hT v hv
  apply hbound.trans
  apply (le_div_iff₀ hℓ).mpr
  have hm := (div_le_iff₀ (Real.log_pos ht)).mp hratio
  nlinarith only [mul_le_mul_of_nonneg_left hm hB]

/-- The infimum over allowed cutoffs is 3/2. An upper limiting coefficient
for the off-line count therefore gives this limiting tilted-moment bound
with arbitrarily small slack. -/
theorem eventually_ingham_tilted_moment_of_offline_cap (p : ℕ) {B κ D : ℝ}
    (hB : 0 ≤ B) (hcap : ∀ z : ℝ, κ < z → ∀ᶠ T : ℝ in atTop,
      strictTail T 0 ≤ z*(T*Real.log T))
    (hD : Real.exp (B*(3/2))*(3/2)^(p+1)*κ < D) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ B * Real.log T / Real.log (Real.log T) →
      (∑ i : Copies T, copyDisplacement T i^(p+1) * Real.exp (v*copyDisplacement T i))/T ≤
        D*(Real.log (Real.log T))^(p+1)/(Real.log T)^p := by
  let F (x : ℝ) := Real.exp (B*(3/2+x))*(3/2+x)^(p+1)*(κ+x)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hzero : F 0 < D := by simpa only [F,add_zero] using hD
  have hopen : ∀ᶠ x : ℝ in 𝓝[>] 0, F x < D :=
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hzero)
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  obtain ⟨η,hη,hslack⟩ := (hpos.and hopen).exists
  let β := 3/2+η
  have hβ : 3/2 < β := by dsimp [β]; linarith
  have hβ0 : 0 < β := by linarith
  have hk : 0 < 2/β := div_pos (by norm_num) hβ0
  obtain ⟨C,hC,henv⟩ := exists_ingham_tilted_moment_envelope
  let V := ((p+1).factorial : ℝ)*(4/3)*C/(4/3-2/β)^(p+2)
  let E := Real.exp (B*β)
  have hV : 0 ≤ V := by
    have hk1 : 2/β < 4/3 := (div_lt_iff₀ hβ0).mpr (by linarith)
    dsimp [V]
    positivity
  have hE : 0 < E := Real.exp_pos _
  have hδ := sub_pos.mpr hslack
  have hpow := (tendsto_pow_atTop (Nat.succ_ne_zero p)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [henv β hβ, hcap (κ+η) (by linarith),eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (B/(2/β))),
    hpow.eventually_ge_atTop (E*V/(D-F η))] with T he hf hT hwidth herr
  intro v hv hvB
  let L := Real.log T
  let ℓ := Real.log L
  have hT0 := zero_lt_one.trans hT
  have hL : 0 < L := Real.log_pos hT
  change max 1 (B/(2/β)) ≤ ℓ at hwidth
  have hℓ : 0 < ℓ := zero_lt_one.trans_le ((le_max_left _ _).trans hwidth)
  change E*V/(D-F η) ≤ ℓ^(p+1) at herr
  change v ≤ B*L/ℓ at hvB
  have hvk : v ≤ (2/β)*L := by
    apply hvB.trans
    apply (div_le_iff₀ hℓ).mpr
    have hx := (div_le_iff₀ hk).mp ((le_max_right _ _).trans hwidth)
    nlinarith only [mul_le_mul_of_nonneg_right hx hL.le]
  have hfreq : Real.exp (v*(β*ℓ/L)) ≤ E := by
    apply Real.exp_le_exp.mpr
    apply (mul_le_mul_of_nonneg_right hvB (by positivity)).trans_eq
    field_simp
  have hc : strictTail T 0/(T*L) ≤ κ+η := (div_le_iff₀ (mul_pos hT0 hL)).mpr hf
  apply (he p v hv hvk).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  change Real.exp (v*(β*ℓ/L))*(β^(p+1)*(strictTail T 0/(T*L))*ℓ^(p+1)+V) ≤ D*ℓ^(p+1)
  have hnn := strictTail_nonneg T 0
  apply (mul_le_mul_of_nonneg_right hfreq (by positivity)).trans
  have hcentr := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg hβ0.le (p+1)))
      (pow_nonneg hℓ.le (p+1))) hE.le
  have hfar := (div_le_iff₀ hδ).mp herr
  change E*V ≤ ℓ^(p+1)*(D-E*β^(p+1)*(κ+η)) at hfar
  linarith only [hcentr,hfar]

/-- The infimum over allowed cutoffs is 3/2. An upper limiting coefficient
for the off-line count therefore gives this limiting tilted-moment bound
with arbitrarily small slack. -/
theorem eventually_ingham_tilted_fourth_of_offline_cap {B κ D : ℝ}
    (hB : 0 ≤ B) (hcap : ∀ z : ℝ, κ < z → ∀ᶠ T : ℝ in atTop,
      strictTail T 0 ≤ z*(T*Real.log T))
    (hD : Real.exp (B*(3/2))*(3/2)^4*κ < D) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ B * Real.log T / Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v*|i.1.1.re-1/2|))/T ≤
        D*(Real.log (Real.log T))^4/(Real.log T)^3 := by
  have he := eventually_ingham_tilted_moment_of_offline_cap 3 hB hcap hD
  filter_upwards [he] with T hT
  intro v hv hwidth
  have h := hT v hv hwidth
  have hs (x : ℝ) : |x|^4 = x^4 := by
    rw [show (4 : ℕ) = 2*2 by decide, pow_mul, sq_abs, ← pow_mul]
  simpa only [show (3:ℕ)+1 = 4 by decide, copyDisplacement, hs] using h

end RiemannResearch.Analysis.ActualZeroOrdinate

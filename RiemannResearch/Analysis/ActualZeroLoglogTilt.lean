import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroInghamHorizontalEnergy
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exponential tilts of the fourth absolute zero-displacement moment

For every fixed B, tilts v ≤ B log log T preserve the fourth-moment
Ingham scale. Split the critical strip at displacement 1/log log T.
The lower part has a bounded exponential weight. On the upper part the
weight is at most a fixed power of log T, which a sufficiently high
absolute displacement moment absorbs. The full finite sums count zeta
zeros with analytic multiplicity. The Ingham exponential tail also gives
a wider inverse-cubic-log bound for v ≤ B log T / log log T and a
frequency-dependent estimate up to every fixed tilt below (4/3) log T. The
central term retains the exact number of off-line copies. The density input
is adapted in ActualZeroInghamHorizontalEnergy from Chourasiya–Simonič,
Theorem 1, https://arxiv.org/abs/2507.15184.
-/
noncomputable section
open Filter Zeta23 Set
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem exists_displacementSum_div_height_bound (p : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ T : ℝ in atTop,
      (∑ i : Copies T, copyDisplacement T i ^ (p+1)) / T ≤
        H * (Real.log (Real.log T)/Real.log T)^(p+1) * Real.log T := by
  let H := (3/2 : ℝ)^(p+1)/3+1
  refine ⟨H, by dsimp [H]; positivity, ?_⟩
  have hc := eventually_count_le_log_of_lt (show 1/(2*Real.pi) < (1:ℝ) by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three])
  filter_upwards [eventually_displacementMoment_ratio_le p zero_lt_one, hc, eventually_count_pos,
    eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with T hm hN hp hT hℓ
  have ht : 0 < T := by linarith
  have hL := Real.log_pos hT
  let M := ∑ i : Copies T, copyDisplacement T i ^ (p+1)
  let w := Real.log (Real.log T) / Real.log T
  have hw : 0 < w := div_pos hℓ hL
  change (M / (Ncount 0 T : ℝ)) / w^(p+1) ≤ H at hm
  have hcount : (Ncount 0 T : ℝ)/T ≤ Real.log T := (div_le_iff₀ ht).mpr (by
    simpa only [one_mul, mul_one, mul_comm] using hN)
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  change M/T ≤ H*w^(p+1)*Real.log T
  calc
    M/T = (M/(Ncount 0 T : ℝ))*((Ncount 0 T : ℝ)/T) := by field_simp
    _ ≤ _ := mul_le_mul ((div_le_iff₀ (pow_pos hw _)).mp hm) hcount
      (div_nonneg (Nat.cast_nonneg _) ht.le) (by dsimp [H]; positivity)

/-- Uniform tilted fourth-moment bound over every fixed loglog-frequency
band. The height and constant may depend on B. -/
theorem exists_loglog_tilted_fourth_moment_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v →
      v ≤ B * Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re - 1/2)^4 * Real.exp (v * |i.1.1.re - 1/2|)) / T ≤
        K * (Real.log (Real.log T))^4 / (Real.log T)^3 := by
  obtain ⟨n, hn⟩ := exists_nat_ge B
  let m := n+1
  obtain ⟨H, hH, hfour⟩ := exists_displacementSum_div_height_bound 3
  obtain ⟨J, hJ, hhigh⟩ := exists_displacementSum_div_height_bound (m+3)
  have hsmall : Tendsto (fun T : ℝ => (Real.log (Real.log T))^(2*m) / Real.log T) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2*m)).comp
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
    apply h.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T ht
    simp only [Function.comp_def, Real.exp_neg, Real.exp_log ht, div_eq_mul_inv]
  refine ⟨Real.exp B * H + J + 1, by positivity, ?_⟩
  filter_upwards [hfour,hhigh,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    hsmall.eventually_le_const zero_lt_one] with T h4 hm hT hℓ hscale
  intro v hv hvB
  let L := Real.log T
  let ℓ := Real.log L
  let S := fun k : ℕ => ∑ i : Copies T, copyDisplacement T i ^ k
  have hT0 : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos hT
  change 0 < ℓ at hℓ
  change v ≤ B * ℓ at hvB
  change ℓ^(2*m)/L ≤ 1 at hscale
  change S 4/T ≤ H*(ℓ/L)^4*L at h4
  change S (m+4)/T ≤ J*(ℓ/L)^(m+4)*L at hm
  have hpoint (i : Copies T) :
      (i.1.1.re-1/2)^4 * Real.exp (v * |i.1.1.re-1/2|) ≤
        Real.exp B * copyDisplacement T i ^ 4 +
          (L^n * ℓ^m) * copyDisplacement T i ^ (m+4) := by
    let d := copyDisplacement T i
    have hd : 0 ≤ d := abs_nonneg _
    have hd1 : d ≤ 1 := by
      have hx : d < 1/2 := displacement_lt_half i.1.2
      linarith
    have hpow : (i.1.1.re-1/2)^4 = d^4 := by
      dsimp [d,copyDisplacement]
      rw [show (4 : ℕ) = 2*2 by decide, pow_mul, pow_mul, sq_abs]
    rw [hpow]
    change d^4 * Real.exp (v*d) ≤ Real.exp B * d^4 + (L^n * ℓ^m) * d^(m+4)
    by_cases hnear : ℓ*d ≤ 1
    · have harg : v*d ≤ B := calc
        _ ≤ (B*ℓ)*d := mul_le_mul_of_nonneg_right hvB hd
        _ = B*(ℓ*d) := by ring
        _ ≤ B := (mul_le_mul_of_nonneg_left hnear hB).trans_eq (mul_one B)
      have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (pow_nonneg hd 4)
      nlinarith only [hh, mul_nonneg (mul_nonneg (pow_nonneg hL.le n) (pow_nonneg hℓ.le m))
        (pow_nonneg hd (m+4))]
    · have harg : v*d ≤ (n:ℝ)*ℓ :=
        (mul_le_mul_of_nonneg_left hd1 hv).trans ((mul_one v).le.trans
          (hvB.trans (mul_le_mul_of_nonneg_right hn hℓ.le)))
      have he : Real.exp (v*d) ≤ L^n := by
        apply (Real.exp_le_exp.mpr harg).trans_eq
        rw [Real.exp_nat_mul, Real.exp_log hL]
      have hw : 1 ≤ (ℓ*d)^m := one_le_pow₀ (le_of_not_ge hnear)
      calc
        _ ≤ d^4 * L^n := mul_le_mul_of_nonneg_left he (pow_nonneg hd _)
        _ ≤ (d^4*L^n) * (ℓ*d)^m :=
          (le_mul_of_one_le_right (mul_nonneg (pow_nonneg hd _) (pow_nonneg hL.le _)) hw)
        _ = (L^n * ℓ^m)*d^(m+4) := by rw [mul_pow, pow_add]; ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (pow_nonneg hd _))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  apply (div_le_div_of_nonneg_right hs hT0.le).trans
  change (Real.exp B*S 4 + (L^n*ℓ^m)*S (m+4))/T ≤ (Real.exp B*H+J+1)*ℓ^4/L^3
  simp only [add_div, mul_div_assoc]
  have htail : (L^n*ℓ^m)*(J*(ℓ/L)^(m+4)*L) ≤ J*ℓ^4/L^3 := by
    calc
      _ = (J*ℓ^4/L^3) * (ℓ^(2*m)/L) := by
        dsimp [m]
        simp only [div_pow, pow_add, pow_succ, two_mul]
        field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_left hscale (by positivity)).trans_eq (mul_one _)
  have hhead : Real.exp B * (H*(ℓ/L)^4*L) = (Real.exp B*H)*ℓ^4/L^3 := by rw [div_pow]; field_simp
  calc
    _ ≤ Real.exp B*(H*(ℓ/L)^4*L) + (L^n*ℓ^m)*(J*(ℓ/L)^(m+4)*L) :=
      add_le_add (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg hL.le _) (pow_nonneg hℓ.le _)))
    _ ≤ (Real.exp B*H)*ℓ^4/L^3 + J*ℓ^4/L^3 := add_le_add hhead.le htail
    _ = (Real.exp B*H+J)*(ℓ^4/L^3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- In the full band v ≤ (2/β) log T for any β > 3/2, the frequency
dependence remains explicit in the exponential factor at the cutoff. The central term retains the exact number of off-line zero copies.
The second term uses the Ingham tail with exponent 4/3. -/
theorem exists_ingham_tilted_fourth_moment_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 3/2 < β →
      ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ (2/β) * Real.log T →
        (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v * |i.1.1.re-1/2|)) / T ≤
          Real.exp (v * (β * Real.log (Real.log T)/Real.log T)) * (β^4 * (strictTail T 0/(T*Real.log T)) *
            (Real.log (Real.log T))^4 + 32*C/(4/3-2/β)^5) / (Real.log T)^3 := by
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
  intro v hv hvw
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
  have htail := weightedFourthSum_le_expTail (T := T) (v := w) (q := (4/3)*L) (show 0 ≤ C*T*L^3 by positivity)
    (mul_nonneg hk.le hL.le) hkw (fun t ht => by simpa only [L,neg_mul] using hing T hT t ht.1)
  let E := Real.exp (v*b)
  have hpoint (i : Copies T) :
      (i.1.1.re-1/2)^4 * Real.exp (v * |i.1.1.re-1/2|) ≤
        (E*b^4)*(if 0 < copyDisplacement T i then 1 else 0) +
          (E/L^2)*((i.1.1.re-1/2)^4*Real.exp (w * |i.1.1.re-1/2|)) := by
    let d := copyDisplacement T i
    have hd : 0 ≤ d := abs_nonneg _
    have hid : (i.1.1.re-1/2)^4 = d^4 := by
      dsimp [d,copyDisplacement]
      rw [show (4:ℕ) = 2*2 by decide, pow_mul, pow_mul, sq_abs]
    change (i.1.1.re-1/2)^4 * Real.exp (v*d) ≤ (E*b^4)*(if 0 < d then 1 else 0) + (E/L^2)*
      ((i.1.1.re-1/2)^4 * Real.exp (w*d))
    rw [hid]
    have hE : 0 < E := Real.exp_pos _
    by_cases hpos : 0 < d
    swap
    · have hz := le_antisymm (le_of_not_gt hpos) hd
      simp [hz]
    rw [if_pos hpos, mul_one]
    by_cases hnear : d ≤ b
    · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnear hv)
      calc
        _ ≤ b^4*E := mul_le_mul (pow_le_pow_left₀ hd hnear _) he (Real.exp_pos _).le (by positivity)
        _ ≤ _ := by rw [mul_comm (b^4)]; exact le_add_of_nonneg_right (by positivity)
    · have hdiff := mul_le_mul_of_nonneg_left (le_of_not_ge hnear) (sub_nonneg.mpr hvw)
      have harg : v*d ≤ v*b - 2*ℓ + w*d := by nlinarith only [hdiff, hwb]
      have h2 : Real.exp (2*ℓ) = L^2 := by
        rw [show 2*ℓ = ℓ+ℓ by ring, Real.exp_add, Real.exp_log hL, sq]
      have he : Real.exp (v*d) ≤ (E/L^2)*Real.exp (w*d) := by
        apply (Real.exp_le_exp.mpr harg).trans_eq
        rw [Real.exp_add, Real.exp_sub, h2]
      calc
        _ ≤ d^4*((E/L^2)*Real.exp (w*d)) := mul_le_mul_of_nonneg_left he (pow_nonneg hd 4)
        _ = (E/L^2)*(d^4*Real.exp (w*d)) := by ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hE.le (pow_nonneg hb.le 4))
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hE : 0 < E := Real.exp_pos _
  have hh := hsum.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail
    (div_nonneg hE.le (sq_nonneg L))))
  apply (div_le_iff₀ hT0).mpr
  apply hh.trans_eq
  change (E*b^4)*strictTail T 0 + E/L^2 * ((C*T*L^3)*(24*((4/3)*L)/((4/3)*L-w)^5)) =
    E*(β^4*(strictTail T 0/(T*L))*ℓ^4 + 32*C/(4/3-k)^5)/L^3*T
  have hp : (4/3)*L-w = (4/3-k)*L := by dsimp [w]; ring
  rw [hp,mul_pow]
  dsimp [b]
  rw [div_pow]
  field_simp [sub_ne_zero.mpr hgap.ne']
  <;> ring

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
  let F (x : ℝ) := Real.exp (B*(3/2+x))*(3/2+x)^4*(κ+x)
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
  obtain ⟨C,hC,henv⟩ := exists_ingham_tilted_fourth_moment_envelope
  let V := 32*C/(4/3-2/β)^5
  let E := Real.exp (B*β)
  have hV : 0 ≤ V := by
    have hk1 : 2/β < 4/3 := (div_lt_iff₀ hβ0).mpr (by linarith)
    dsimp [V]
    positivity
  have hE : 0 < E := Real.exp_pos _
  have hδ := sub_pos.mpr hslack
  have hpow := (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp
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
  change E*V/(D-F η) ≤ ℓ^4 at herr
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
  apply (he v hv hvk).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  change Real.exp (v*(β*ℓ/L))*(β^4*(strictTail T 0/(T*L))*ℓ^4+V) ≤ D*ℓ^4
  have hnn := strictTail_nonneg T 0
  apply (mul_le_mul_of_nonneg_right hfreq (by positivity)).trans
  have hcentr := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg hβ0.le 4))
      (pow_nonneg hℓ.le 4)) hE.le
  have hfar := (div_le_iff₀ hδ).mp herr
  change E*V ≤ ℓ^4*(D-E*β^4*(κ+η)) at hfar
  linarith only [hcentr,hfar]

end RiemannResearch.Analysis.ActualZeroOrdinate

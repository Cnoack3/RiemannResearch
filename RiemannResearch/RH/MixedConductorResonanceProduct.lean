import RiemannResearch.RH.MixedConductorSeedObstruction
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoMellinCapacityStability
import RiemannResearch.RH.RamanujanMellinProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-!
# Resonance products for mixed corrections divisible by a common prime

The Mellin transform of a prime packet vanishes at each nonzero point of its
conductor resonance lattice. The optimized finite Mellin Gram inequality can
use all of these points simultaneously. A mean-one condition improves the
resulting distance floor by optimizing over scalar multiples of the trial.
Euler’s sine product, applied on the imaginary axis, evaluates the limit
of the paired resonance factors.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticConductorCommonZeros
open scoped BigOperators

def primePacketResonance (p : ℕ) (k : ℤ) : ℂ :=
  1 + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (Real.log p : ℂ)

theorem primePacketResonance_injective (p : ℕ) (hp : 1 < p) :
    Function.Injective (primePacketResonance p) := by
  have hl : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast hp)).ne'
  intro a b h
  change 1 + _ / _ = 1 + _ / _ at h
  have h' := add_left_cancel h
  have he := (div_left_inj' hl).mp h'
  exact_mod_cast (mul_left_inj' Complex.two_pi_I_ne_zero).mp he

theorem primePacketResonance_re (p : ℕ) (hp : 1 < p) (k : ℤ) :
    (primePacketResonance p k).re = 1 :=
  conductorSymbol_zero_re p hp _ (conductorSymbol_explicit_zero p hp k)

theorem primePacketResonance_mellin_zero (p : ℕ) (hp : p.Prime) (k : ℤ) (hk : k ≠ 0) :
    paretoMellin (ramanujanPacketHilbert p) (primePacketResonance p k) = 0 := by
  let z := primePacketResonance p k
  have hr : z.re = 1 := primePacketResonance_re p hp.one_lt k
  have hzero : conductorSymbol p z = 0 := conductorSymbol_explicit_zero p hp.one_lt k
  have hz : z ≠ 1 := conductorSymbol_extra_zero_ne_one p hp.one_lt k hk
  have hpos : 0 < z.re := by rw [hr]; norm_num
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℂ) ^ (1 - z) = 1 := by
    rw [RiemannResearch.RH.conductorSymbol_eq_cpow p hp.pos] at hzero
    rw [sub_eq_zero] at hzero
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC, Complex.cpow_one, ← hzero]
    field_simp
  have hv : ramanujanPacketHilbert p = digitHilbert p 1 hp.pos (by omega) := by
    apply hilbertSequence_injective
    rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue p hp,
      hilbertSequence_digitHilbert]
    funext n
    simp [digitSequence, residue]
  change paretoMellin _ z = 0
  rw [hv, paretoMellin_residue_zeta p hp.pos z hpos hz, hpow, sub_self, mul_zero]

/-- Finite families of Mellin zeros give a stronger bound when the trial has mean one. -/
theorem mellinZeroProduct_mul_meanOne_energy_ge_one {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (hhalf : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (f : ThresholdHilbert) (hmean : inner ℝ hilbertOne f = 1)
    (hzero : ∀ i, paretoMellin f (z i) = 0) :
    1 ≤ mellinZeroProduct z * ‖f‖ ^ 2 := by
  classical
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective z hhalf).mpr hinj
  have hf : f ≠ 0 := by rintro rfl; simp at hmean
  have hn : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf) _
  let a : ℝ := 1 / ‖f‖ ^ 2
  have hsrc (i : ι) : paretoMellin (hilbertOne - a • f) (z i) = 1 / z i := by
    change paretoMellinContinuous (z i) (hhalf i) (hilbertOne - a • f) = _
    rw [map_sub, map_smul]
    change paretoMellin hilbertOne (z i) - a • paretoMellin f (z i) = _
    rw [paretoMellin_one _ (hhalf i), hzero, smul_zero, sub_zero]
  have hbound := (mellinPhysicalCapacity_bounds (hilbertOne - a • f) z hhalf hdet).2
  simp_rw [hsrc] at hbound
  rw [mellinInverseCapacity_zeroSource_product z hhalf hinj, norm_sub_sq_real,
    hilbertOne_norm_sq, real_inner_smul_right, hmean, mul_one, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hbound
  have ha : a * ‖f‖ ^ 2 = 1 := one_div_mul_cancel hn.ne'
  have he : a ^ 2 * ‖f‖ ^ 2 = a := by rw [sq, mul_assoc, ha, mul_one]
  rw [he] at hbound
  exact (div_le_iff₀ hn).mp (show a ≤ mellinZeroProduct z by linarith)

/-- Every finite set of nonzero prime resonances gives a simultaneous lower
bound on the squared error of the normalized prime trial with any mixed
correction whose conductors are all divisible by that prime. -/
theorem restricted_mixed_seed_product_floor {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : p.Prime) (m : ι → ℤ) (hm : Function.Injective m)
    (hnz : ∀ i, m i ≠ 0) (F : Finset ℕ) (hF : ∀ q ∈ F, 1 < q ∧ p ∣ q)
    {c : ThresholdHilbert} (hc : c ∈ PrimePowerSchur.mixedSpace F) :
    let f := (Real.log p)⁻¹ • (ramanujanPacketHilbert p - c)
    let z := fun i => primePacketResonance p (m i)
    1 ≤ mellinZeroProduct z * (1 + ‖hilbertOne - f‖ ^ 2) := by
  classical
  intro f z
  have hhalf (i : ι) : (1 / 2 : ℝ) < (z i).re := by
    rw [show (z i).re = 1 from primePacketResonance_re p hp.one_lt (m i)]
    norm_num
  have hinj : Function.Injective z := (primePacketResonance_injective p hp.one_lt).comp hm
  let K := singleSeedDilationClosure (ramanujanPacketHilbert p)
  have hle : PrimePowerSchur.mixedSpace F ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have hq := hF q.val (Finset.mem_filter.mp q.property).1
    exact ramanujanPacketHilbert_mem_singleSeed_of_dvd p q.val hp (by omega) hq.2
  have hf : f ∈ K := K.smul_mem _ (K.sub_mem
    (ramanujanPacketHilbert_mem_singleSeed_of_dvd p p hp hp.pos dvd_rfl) (hle hc))
  have hz (i : ι) : paretoMellin f (z i) = 0 := by
    apply paretoMellin_zero_on_singleSeedClosure _ _ (hhalf i) _ hf
    intro d hd
    rw [paretoMellin_dilation, primePacketResonance_mellin_zero p hp (m i) (hnz i), mul_zero]
  have hmean : inner ℝ hilbertOne f = 1 := by
    have hc0 : inner ℝ c hilbertOne = 0 :=
      ((PrimePowerSchur.mixedSpace F).mem_orthogonal _).mp
        (PrimePowerSchur.one_mem_mixed_orthogonal _) _ hc
    rw [real_inner_comm]
    dsimp only [f]
    rw [real_inner_smul_left, inner_sub_left, hc0, sub_zero, hilbert_inner_one,
      hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact inv_mul_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hnorm : 1 + ‖hilbertOne - f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sub_sq_real, hilbertOne_norm_sq, hmean]; ring
  rw [hnorm]
  exact mellinZeroProduct_mul_meanOne_energy_ge_one z hhalf hinj f hmean hz


open Filter Topology

private theorem resonance_factor (p : ℕ) (hp : 1 < p) (k : ℤ) (hk : k ≠ 0) :
    let z := primePacketResonance p k
    ‖(z - 1) / z‖ ^ 2 =
      (1 + (Real.log p / (2 * Real.pi)) ^ 2 / (k : ℝ) ^ 2)⁻¹ := by
  intro z
  let a : ℝ := Real.log p / (2 * Real.pi)
  let t : ℝ := (k : ℝ) / a
  have ha : 0 < a := div_pos (Real.log_pos (by exact_mod_cast hp)) (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have ht : t ≠ 0 := div_ne_zero hkR ha.ne'
  have hz : z = 1 + (t : ℂ) * Complex.I := by
    dsimp [z, primePacketResonance, t, a]
    push_cast
    field_simp
  rw [hz, add_sub_cancel_left, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_add,
    add_zero, sub_zero]
  change t * t / (1 + t * t) = (1 + a ^ 2 / (k : ℝ) ^ 2)⁻¹
  dsimp only [t]
  have hs : 0 < a ^ 2 + (k : ℝ) ^ 2 := by positivity
  field_simp [ha.ne', hkR]
  ring

/-- The positive and negative resonance of each order contribute equal factors. -/
theorem restricted_mixed_seed_euler_prefix (p : ℕ) (hp : p.Prime)
    (F : Finset ℕ) (hF : ∀ q ∈ F, 1 < q ∧ p ∣ q)
    {c : ThresholdHilbert} (hc : c ∈ PrimePowerSchur.mixedSpace F) (N : ℕ) :
    (∏ j ∈ Finset.range N, (1 + (Real.log p / (2 * Real.pi)) ^ 2 / ((j : ℝ) + 1) ^ 2)) ^ 2 ≤
      1 + ‖hilbertOne - (Real.log p)⁻¹ • (ramanujanPacketHilbert p - c)‖ ^ 2 := by
  let k : Fin N ⊕ Fin N → ℤ := Sum.elim (fun j => (j.val : ℤ) + 1)
    (fun j => -((j.val : ℤ) + 1))
  have hki : Function.Injective k := by
    rintro (i | i) (j | j) h <;> simp only [k, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))
  have hk0 : ∀ j, k j ≠ 0 := by
    rintro (j | j) <;> dsimp [k] <;> omega
  have h := restricted_mixed_seed_product_floor p hp k hki hk0 F hF hc
  let b (j : ℕ) : ℝ := 1 + (Real.log p / (2 * Real.pi)) ^ 2 / ((j : ℝ) + 1) ^ 2
  let B := ∏ j ∈ Finset.range N, b j
  have hpos : 0 < B := Finset.prod_pos (fun _ _ => by dsimp [b]; positivity)
  have hf (j : Fin N ⊕ Fin N) :
      ‖(primePacketResonance p (k j) - 1) / primePacketResonance p (k j)‖ ^ 2 =
      Sum.elim (fun i : Fin N => (b i.val)⁻¹) (fun i : Fin N => (b i.val)⁻¹) j := by
    rw [resonance_factor p hp.one_lt _ (hk0 j)]
    rcases j with j | j <;> simp [k, b]
    congr 1
    ring
  have hprod : mellinZeroProduct (fun j => primePacketResonance p (k j)) = (B ^ 2)⁻¹ := by
    unfold mellinZeroProduct
    simp_rw [hf]
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hB : (∏ i : Fin N, (b i.val)⁻¹) = B⁻¹ := by
      rw [Fin.prod_univ_eq_prod_range (fun j => (b j)⁻¹) N, Finset.prod_inv_distrib]
    rw [hB]
    simp [sq]
  change 1 ≤ mellinZeroProduct (fun j => primePacketResonance p (k j)) * _ at h
  rw [hprod, inv_mul_eq_div] at h
  simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos hpos)).mp h

private theorem tendsto_euler_sinh_prefix (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2))
      Filter.atTop (nhds (Real.sinh (Real.pi * a) / (Real.pi * a))) := by
  let z : ℂ := (a : ℂ) * Complex.I
  have hza : (Real.pi : ℂ) * z = ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
    dsimp [z]; push_cast; ring
  have hnz : (Real.pi : ℂ) * z ≠ 0 := by
    rw [hza]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ha.ne'))
      Complex.I_ne_zero
  have h := (Complex.tendsto_euler_sin_prod z).div_const ((Real.pi : ℂ) * z)
  have hf (j : ℕ) : 1 - z ^ 2 / ((j : ℂ) + 1) ^ 2 =
      ((1 + a ^ 2 / ((j : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    dsimp [z]
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have he (N : ℕ) : ((Real.pi : ℂ) * z *
      ∏ j ∈ Finset.range N, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2)) / ((Real.pi : ℂ) * z) =
      ((∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    rw [mul_div_cancel_left₀ _ hnz]
    push_cast
    simp_rw [hf]
    push_cast
    rfl
  have hlim : Complex.sin ((Real.pi : ℂ) * z) / ((Real.pi : ℂ) * z) =
      ((Real.sinh (Real.pi * a) / (Real.pi * a) : ℝ) : ℂ) := by
    rw [hza, Complex.sin_mul_I]
    push_cast
    rw [mul_div_mul_right _ _ Complex.I_ne_zero]
  have h' : Filter.Tendsto
      (fun N : ℕ => ((∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2) : ℝ) : ℂ))
      Filter.atTop (nhds ((Real.sinh (Real.pi * a) / (Real.pi * a) : ℝ) : ℂ)) := by
    simpa only [he, hlim] using h
  exact_mod_cast Complex.continuous_re.continuousAt.tendsto.comp h'

/-- Full common-prime obstruction: all harmonic orders together give a positive
error floor depending only on the common prime. -/
theorem restricted_mixed_seed_all_harmonics_floor (p : ℕ) (hp : p.Prime)
    (F : Finset ℕ) (hF : ∀ q ∈ F, 1 < q ∧ p ∣ q)
    {c : ThresholdHilbert} (hc : c ∈ PrimePowerSchur.mixedSpace F) :
    ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * (Real.log p) ^ 2) - 1 ≤
      ‖hilbertOne - (Real.log p)⁻¹ • (ramanujanPacketHilbert p - c)‖ ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  let L := Real.log (p : ℝ)
  have hl : 0 < L := Real.log_pos hp1
  let a := L / (2 * Real.pi)
  have ha : 0 < a := div_pos hl (by positivity)
  have h := le_of_tendsto_of_tendsto' ((tendsto_euler_sinh_prefix a ha).pow 2)
    tendsto_const_nhds (fun N => restricted_mixed_seed_euler_prefix p hp F hF hc N)
  have hpi : Real.pi * a = L / 2 := by dsimp [a]; field_simp
  rw [hpi] at h
  let x := Real.exp (L / 2)
  have hx : 0 < x := Real.exp_pos _
  have hxp : x ^ 2 = (p : ℝ) := by
    rw [sq, ← Real.exp_add, show L / 2 + L / 2 = L by ring, Real.exp_log hp0]
  have he : (Real.sinh (L / 2) / (L / 2)) ^ 2 =
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * L ^ 2) := by
    rw [Real.sinh_eq, Real.exp_neg]
    change (((x - x⁻¹) / 2) / (L / 2)) ^ 2 = _
    rw [← hxp]
    field_simp [hx.ne', hl.ne']
  rw [he] at h
  change ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * L ^ 2) - 1 ≤ _
  linarith



/-- Uniform squared error for the unnormalized conductor-two target if every
mixed correction is even. The bound already incorporates all even resonances. -/
theorem even_mixed_centered_parity_error_floor (F : Finset ℕ)
    (hF : ∀ q ∈ F, 1 < q ∧ 2 ∣ q) {c : ThresholdHilbert}
    (hc : c ∈ PrimePowerSchur.mixedSpace F) :
    1 / 2 - (Real.log 2) ^ 2 ≤
      ‖(ramanujanPacketHilbert 2 - c) - Real.log 2 • hilbertOne‖ ^ 2 := by
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  have h := restricted_mixed_seed_all_harmonics_floor 2 Nat.prime_two F hF hc
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_pow] at h
  have he : L • (hilbertOne - L⁻¹ • (ramanujanPacketHilbert 2 - c)) =
      L • hilbertOne - (ramanujanPacketHilbert 2 - c) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  change 1 / 2 - L ^ 2 ≤ ‖(ramanujanPacketHilbert 2 - c) - L • hilbertOne‖ ^ 2
  rw [norm_sub_rev, ← he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change 1 / (2 * L ^ 2) - 1 ≤ ‖hilbertOne - L⁻¹ • (ramanujanPacketHilbert 2 - c)‖ ^ 2 at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg L)
  calc
    _ = L ^ 2 * (1 / (2 * L ^ 2) - 1) := by field_simp [hL.ne']
    _ ≤ _ := hmul

/-- Regardless of the cutoff, the energy captured by an even-only window stays
below the full saturation target by at least one half minus log-two squared. -/
theorem even_mixed_projection_capture_ceiling (F : Finset ℕ)
    (hF : ∀ q ∈ F, 1 < q ∧ 2 ∣ q) :
    ‖(PrimePowerSchur.mixedSpace F).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 ≤
      Real.log 2 - 1 / 2 := by
  let K := PrimePowerSchur.mixedSpace F
  let z := ramanujanPacketHilbert 2
  let y := K.starProjection z
  have hy : y ∈ K := K.starProjection_apply_mem z
  have hzy : inner ℝ z y = ‖y‖ ^ 2 := by
    have ho := K.starProjection_inner_eq_zero z y hy
    change inner ℝ (z - y) y = 0 at ho
    rw [inner_sub_left, real_inner_self_eq_norm_sq, sub_eq_zero] at ho
    exact ho
  have hyn : inner ℝ y hilbertOne = 0 :=
    (K.mem_orthogonal _).mp (PrimePowerSchur.one_mem_mixed_orthogonal _) y hy
  have hzn : inner ℝ z hilbertOne = Real.log 2 := by
    dsimp only [z]
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hzsq : ‖z‖ ^ 2 = Real.log 2 := PrimePowerSchur.ramanujanPacketHilbert_two_norm_sq
  have h := even_mixed_centered_parity_error_floor F hF hy
  change 1 / 2 - (Real.log 2) ^ 2 ≤ ‖(z - y) - Real.log 2 • hilbertOne‖ ^ 2 at h
  rw [norm_sub_sq_real, norm_sub_sq_real, hzy, hzsq, real_inner_smul_right, inner_sub_left,
    hzn, hyn, sub_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq] at h
  change ‖y‖ ^ 2 ≤ _
  nlinarith only [h]


end RiemannResearch.RH.Pareto

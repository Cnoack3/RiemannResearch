import RiemannResearch.RH.DilationWaveletAsymptoticTargets
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RiemannResearch.RH.ParetoStepIsometry

/-!
Exact BinaryWaveletContinuousGramTarget, including the infinite unit-cell
integral decomposition and sparse arithmetic jump-series regrouping. The
primitive is the actual continuous integral, with all endpoint and convergence
terms established explicitly.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem binaryWaveletStep_measurable (m : ℕ) : Measurable (binaryWaveletStep m) :=
  (measurable_of_countable (dilationWaveletSequence 2 m)).comp Nat.measurable_floor

theorem binaryWaveletStep_abs_bound (m : ℕ) (x : ℝ) :
    |binaryWaveletStep m x| ≤ 1 := binary_wavelet_abs_le m _

theorem binaryWaveletStep_integrableOn_Icc (m : ℕ) (a b : ℝ) :
    IntegrableOn (binaryWaveletStep m) (Icc a b) := by
  have hI : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc a b) :=
    continuousOn_const.integrableOn_Icc
  apply hI.mono' (binaryWaveletStep_measurable m).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using binaryWaveletStep_abs_bound m x)

theorem binaryWaveletStep_intervalIntegrable (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (binaryWaveletStep m) volume a b := by
  rw [intervalIntegrable_iff]
  exact (binaryWaveletStep_integrableOn_Icc m (min a b) (max a b)).mono_set
    Ioc_subset_Icc_self

theorem binaryWaveletStep_on_cell (m k : ℕ) {x : ℝ}
    (hx : x ∈ Ico (k:ℝ) ((k:ℝ)+1)) :
    binaryWaveletStep m x = dilationWaveletSequence 2 m k := by
  have hkx : ⌊x⌋₊ = k := by simpa using! Nat.floor_eq_on_Ico k x hx
  rw [binaryWaveletStep, hkx]

/-- The actual primitive increment, including any partial final cell. -/
theorem binaryWaveletContinuousPrimitive_cell_increment (m k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
    (∫ t in (k:ℝ)..x, binaryWaveletStep m t) =
      (x-(k:ℝ))*dilationWaveletSequence 2 m k := by
  rw [intervalIntegral.integral_of_le hx.1, ← integral_Ico_eq_integral_Ioc]
  calc
    _ = ∫ t in Ico (k:ℝ) x, dilationWaveletSequence 2 m k := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      exact binaryWaveletStep_on_cell m k ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩
    _ = _ := by
      rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hx.1,
        intervalIntegral.integral_const]
      rfl

/-- Integer values of the ordinary continuous integral equal the existing
discrete triangular primitive. -/
theorem binaryWaveletContinuousPrimitive_nat (m k : ℕ) (hm : 0 < m) :
    binaryWaveletContinuousPrimitive m (k:ℝ) = binaryWaveletPrimitive m k := by
  induction k with
  | zero => simp [binaryWaveletContinuousPrimitive]
  | succ k ih =>
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (binaryWaveletStep_intervalIntegrable m 0 k)
      (binaryWaveletStep_intervalIntegrable m k ((k:ℝ)+1))
    have hc := binaryWaveletContinuousPrimitive_cell_increment m k
      (x := (k:ℝ)+1) ⟨by linarith, le_rfl⟩
    simp only [add_sub_cancel_left, one_mul] at hc
    rw [Nat.cast_add, Nat.cast_one]
    change (∫ t in (0:ℝ)..((k:ℝ)+1), binaryWaveletStep m t) =
      binaryWaveletPrimitive m (k+1)
    rw [← hi, hc]
    change binaryWaveletContinuousPrimitive m (k:ℝ) +
      dilationWaveletSequence 2 m k = _
    rw [ih]
    linarith [binaryWaveletPrimitive_step m hm k]

/-- The actual primitive is the affine interpolation of its genuine discrete
integer primitive; this supplies the exact local integration formula. -/
theorem binaryWaveletContinuousPrimitive_on_cell (m k : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
    binaryWaveletContinuousPrimitive m x = binaryWaveletPrimitive m k +
      (x-(k:ℝ))*dilationWaveletSequence 2 m k := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (binaryWaveletStep_intervalIntegrable m 0 k)
    (binaryWaveletStep_intervalIntegrable m k x)
  rw [binaryWaveletContinuousPrimitive, ← hi,
    binaryWaveletContinuousPrimitive_cell_increment m k hx]
  rw [show (∫ t in (0:ℝ)..(k:ℝ), binaryWaveletStep m t) =
    binaryWaveletPrimitive m k from binaryWaveletContinuousPrimitive_nat m k hm]

/-- Global bounds retain the actual nonnegative triangular primitive. -/
theorem binaryWaveletContinuousPrimitive_bounds (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ binaryWaveletContinuousPrimitive m x ∧
      binaryWaveletContinuousPrimitive m x ≤ m := by
  let k := ⌊x⌋₊
  have hlo : (k:ℝ) ≤ x := Nat.floor_le hx
  have hhi : x ≤ (k:ℝ)+1 := (Nat.lt_floor_add_one x).le
  rw [binaryWaveletContinuousPrimitive_on_cell m k hm ⟨hlo,hhi⟩]
  have h0 := binaryWaveletPrimitive_bounds m hm k
  have h1 := binaryWaveletPrimitive_bounds m hm (k+1)
  have hs := binaryWaveletPrimitive_step m hm k
  have ha : 0 ≤ x-(k:ℝ) := sub_nonneg.mpr hlo
  have hb : 0 ≤ 1-(x-(k:ℝ)) := by linarith
  have hlow0 := mul_nonneg hb h0.1
  have hlow1 := mul_nonneg ha h1.1
  have hhigh0 := mul_le_mul_of_nonneg_left h0.2 hb
  have hhigh1 := mul_le_mul_of_nonneg_left h1.2 ha
  have he : binaryWaveletPrimitive m k+(x-(k:ℝ))*dilationWaveletSequence 2 m k =
      (1-(x-(k:ℝ)))*binaryWaveletPrimitive m k+
        (x-(k:ℝ))*binaryWaveletPrimitive m (k+1) := by
    rw [show binaryWaveletPrimitive m (k+1) =
      binaryWaveletPrimitive m k+dilationWaveletSequence 2 m k by linarith]
    ring
  rw [he]
  constructor <;> nlinarith

/-- Direct rational antiderivative calculation. This exact identity is the
continuous correction to the discrete Gram sum on one unit cell. -/
theorem affine_primitive_inverse_cube_cell (P Q a : ℝ) (ha : 0 < a) :
    2*(∫ x in a..(a+1), (P+(x-a)*Q)/x^3) =
      P/a^2-(P+Q)/(a+1)^2+Q/(a*(a+1)) := by
  let H : ℝ → ℝ := fun x => (-Q)*x⁻¹-((P-a*Q)/2)*(x^2)⁻¹
  have hderiv : ∀ x ∈ uIcc a (a+1),
      HasDerivAt H ((P+(x-a)*Q)/x^3) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    have hd := ((hasDerivAt_inv hx0).const_mul (-Q)).sub
      ((((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx0)).const_mul ((P-a*Q)/2))
    convert! hd using 1 <;> dsimp [H] <;> field_simp <;> ring
  have hI : IntervalIntegrable (fun x : ℝ => (P+(x-a)*Q)/x^3)
      volume a (a+1) := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.add
      ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)).div
      (continuousOn_id.pow 3)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le ha hx.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hI]
  dsimp [H]
  field_simp
  <;> ring

/-- Actual cell formula with both endpoint values and the discrete Pareto
weight. No boundary contribution is omitted. -/
theorem binaryWaveletContinuousPrimitive_weighted_cell (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    2*(∫ x in (k:ℝ)..((k:ℝ)+1), binaryWaveletContinuousPrimitive m x / x^3) =
      binaryWaveletPrimitive m k/(k:ℝ)^2 -
        binaryWaveletPrimitive m (k+1)/((k:ℝ)+1)^2 +
        positiveWeight k*dilationWaveletSequence 2 m k := by
  have he : (∫ x in (k:ℝ)..((k:ℝ)+1), binaryWaveletContinuousPrimitive m x/x^3) =
      ∫ x in (k:ℝ)..((k:ℝ)+1),
        (binaryWaveletPrimitive m k+(x-(k:ℝ))*dilationWaveletSequence 2 m k)/x^3 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    dsimp only
    rw [binaryWaveletContinuousPrimitive_on_cell m k hm hx]
  rw [he, affine_primitive_inverse_cube_cell _ _ _ (by positivity)]
  have hs := binaryWaveletPrimitive_step m hm k
  have hb : binaryWaveletPrimitive m k+dilationWaveletSequence 2 m k =
      binaryWaveletPrimitive m (k+1) := by linarith
  rw [hb]
  unfold positiveWeight
  ring

private theorem continuousGram_mother_value (k : ℕ) :
    dilationWaveletSequence 2 1 k =
      if k % 4 = 1 then 1 else if k % 4 = 2 then -1 else 0 := by
  have hk : k % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : k % 4
  all_goals
    have h1 : k % 2 = (k % 4) % 2 := by omega
    have h2 : k / 2 % 2 = (k % 4) / 2 := by omega
    simp [dilationWaveletSequence, digitSequence, h1, h2, h]

private theorem continuousGram_mother_jump (j : ℕ) (hj : 0 < j) :
    dilationWaveletSequence 2 1 j-dilationWaveletSequence 2 1 (j-1) =
      binaryWaveletJump j := by
  rw [continuousGram_mother_value, continuousGram_mother_value]
  have hj4 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : j % 4
  all_goals
    have hp : (j-1) % 4 = (j % 4+3) % 4 := by omega
    norm_num [binaryWaveletJump,h,hp]

/-- Only the true integer-dilation boundaries carry jumps. -/
theorem binaryWavelet_integer_jump (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    dilationWaveletSequence 2 n k-dilationWaveletSequence 2 n (k-1) =
      if n ∣ k then binaryWaveletJump (k/n) else 0 := by
  by_cases hd : n ∣ k
  · rw [if_pos hd]
    obtain ⟨j,rfl⟩ := hd
    have hj : 0 < j := by nlinarith
    have hq : n*j/n = j := Nat.mul_div_cancel_left j hn
    have hprev : (n*j-1)/n = j-1 := by
      have hnj : n*j-1+1 = n*j := Nat.sub_add_cancel (by omega)
      apply Nat.div_eq_of_lt_le
      · have hsub : j-1+1 = j := by omega
        have hmul : n*(j-1)+n = n*j := by nlinarith
        rw [Nat.mul_comm (j-1) n]
        omega
      · have hsub : j-1+1 = j := by omega
        rw [hsub, Nat.mul_comm j n]
        omega
    rw [dilationWaveletSequence_two_pullback n,
      dilationWaveletSequence_two_pullback n, hq, hprev, continuousGram_mother_jump j hj]
  · rw [if_neg hd]
    have hlo : (k/n)*n < k := by
      refine lt_of_le_of_ne (Nat.div_mul_le_self k n) ?_
      intro heq
      apply hd
      exact ⟨k/n, by nlinarith⟩
    have hhi : k < (k/n+1)*n :=
      (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self (k/n))
    have hprev : (k-1)/n = k/n := by
      apply Nat.div_eq_of_lt_le <;> omega
    rw [dilationWaveletSequence_two_pullback n k,
      dilationWaveletSequence_two_pullback n (k-1), hprev]
    ring

/-- Finite signed endpoint algebra for the subsequent improper-integral limit.
The terminal boundary term remains explicit. -/
theorem binaryWavelet_continuousGram_finite_abel (m n N : ℕ) :
    (∑ k ∈ Finset.range N, dilationWaveletSequence 2 n k *
      (binaryWaveletPrimitive m k/(k:ℝ)^2 -
        binaryWaveletPrimitive m (k+1)/((k+1:ℕ):ℝ)^2)) =
      (∑ k ∈ Finset.range N, binaryWaveletPrimitive m (k+1)/((k+1:ℕ):ℝ)^2 *
        (dilationWaveletSequence 2 n (k+1)-dilationWaveletSequence 2 n k)) -
        binaryWaveletPrimitive m N/(N:ℝ)^2*dilationWaveletSequence 2 n N := by
  let A := fun k : ℕ => binaryWaveletPrimitive m k/(k:ℝ)^2
  let f := dilationWaveletSequence 2 n
  have h := RiemannResearch.Analysis.boundedPrimitive_abel_identity A f N
  have hz : A 0*f 0 = 0 := by simp [A]
  rw [hz,sub_zero] at h
  have hleft : (∑ k ∈ Finset.range N, f k*(A k-A (k+1))) =
      -(∑ k ∈ Finset.range N, (A (k+1)-A k)*f k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hright : (∑ k ∈ Finset.range N, A (k+1)*(f (k+1)-f k)) =
      -(∑ k ∈ Finset.range N, A (k+1)*(f k-f (k+1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change (∑ k ∈ Finset.range N, f k*(A k-A (k+1))) =
    (∑ k ∈ Finset.range N, A (k+1)*(f (k+1)-f k))-A N*f N
  rw [hleft,hright]
  linarith

private def gramEndpoint (m k : ℕ) : ℝ := binaryWaveletPrimitive m k/(k:ℝ)^2

private theorem gramEndpoint_nonneg (m k : ℕ) (hm : 0 < m) :
    0 ≤ gramEndpoint m k := div_nonneg (binaryWaveletPrimitive_bounds m hm k).1 (sq_nonneg _)

private theorem gramEndpoint_bound (m k : ℕ) (hm : 0 < m) :
    |gramEndpoint m k| ≤ (2*(m:ℝ))*positiveWeight k := by
  by_cases hk : k = 0
  · simp [hk,gramEndpoint,positiveWeight]
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hkpos : 0 < (k:ℝ) := by positivity
  rw [abs_of_nonneg (gramEndpoint_nonneg m k hm)]
  calc
    _ ≤ (m:ℝ)/(k:ℝ)^2 := div_le_div_of_nonneg_right
      (binaryWaveletPrimitive_bounds m hm k).2 (sq_nonneg _)
    _ ≤ _ := by
      unfold positiveWeight
      rw [show (2*(m:ℝ))*(1/((k:ℝ)*((k:ℝ)+1))) =
        (2*(m:ℝ))/((k:ℝ)*((k:ℝ)+1)) by ring]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m)
        (mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sub_nonneg.mpr hk1))
      nlinarith

private theorem gramEndpoint_summable (m : ℕ) (hm : 0 < m) :
    Summable (gramEndpoint m) := by
  apply (positiveWeight_summable.mul_left (2*(m:ℝ))).of_norm_bounded
  intro k
  simpa only [Real.norm_eq_abs] using gramEndpoint_bound m k hm

private theorem gramEndpoint_mul_summable (m : ℕ) (hm : 0 < m) (g : ℕ → ℝ)
    (hg : ∀ k, |g k| ≤ 1) : Summable (fun k => gramEndpoint m k*g k) := by
  apply (gramEndpoint_summable m hm).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gramEndpoint_nonneg m k hm)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg k) (gramEndpoint_nonneg m k hm)

private theorem gramEndpoint_succ_mul_summable (m : ℕ) (hm : 0 < m) (g : ℕ → ℝ)
    (hg : ∀ k, |g k| ≤ 1) : Summable (fun k => gramEndpoint m (k+1)*g k) := by
  have hs : Summable (fun k => gramEndpoint m (k+1)) :=
    (summable_nat_add_iff 1).mpr (gramEndpoint_summable m hm)
  apply hs.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gramEndpoint_nonneg m (k+1) hm)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg k)
    (gramEndpoint_nonneg m (k+1) hm)

private def gramDiscreteCorrection (m n k : ℕ) : ℝ := dilationWaveletSequence 2 n k *
  (gramEndpoint m k-gramEndpoint m (k+1))

private def gramIntegerJump (m n k : ℕ) : ℝ := gramEndpoint m k *
  (dilationWaveletSequence 2 n k-dilationWaveletSequence 2 n (k-1))

private theorem gramDiscreteCorrection_summable (m n : ℕ) (hm : 0 < m) :
    Summable (gramDiscreteCorrection m n) := by
  convert! (gramEndpoint_mul_summable m hm _ (binary_wavelet_abs_le n)).sub
    (gramEndpoint_succ_mul_summable m hm _ (binary_wavelet_abs_le n)) using 1
  funext k
  dsimp [gramDiscreteCorrection]
  ring

private theorem gramIntegerJump_summable (m n : ℕ) (hm : 0 < m) :
    Summable (gramIntegerJump m n) := by
  convert! (gramEndpoint_mul_summable m hm _ (binary_wavelet_abs_le n)).sub
    (gramEndpoint_mul_summable m hm (fun k => dilationWaveletSequence 2 n (k-1))
      (fun k => binary_wavelet_abs_le n (k-1))) using 1
  funext k
  dsimp [gramIntegerJump]
  ring

private theorem gramDiscreteCorrection_eq_jump (m n : ℕ) (hm : 0 < m) :
    (∑' k, gramDiscreteCorrection m n k) = ∑' k, gramIntegerJump m n k := by
  let f := dilationWaveletSequence 2 n
  have hp := gramEndpoint_mul_summable m hm f (binary_wavelet_abs_le n)
  have hq := gramEndpoint_succ_mul_summable m hm f (binary_wavelet_abs_le n)
  have hs : Summable (fun k => gramEndpoint m (k+1)*f (k+1)) :=
    (summable_nat_add_iff 1).mpr hp
  have hz : gramEndpoint m 0*f 0 = 0 := by simp [gramEndpoint]
  have hshift : (∑' k, gramEndpoint m (k+1)*f (k+1)) =
      ∑' k, gramEndpoint m k*f k := by
    have h := hp.tsum_eq_zero_add
    rw [hz,zero_add] at h
    exact h.symm
  have hc : (∑' k, gramDiscreteCorrection m n k) =
      (∑' k, gramEndpoint m k*f k)-(∑' k, gramEndpoint m (k+1)*f k) := by
    rw [← hp.tsum_sub hq]
    apply tsum_congr
    intro k
    dsimp [gramDiscreteCorrection,f]
    ring
  have hj : (∑' k, gramIntegerJump m n (k+1)) =
      (∑' k, gramEndpoint m (k+1)*f (k+1))-(∑' k, gramEndpoint m (k+1)*f k) := by
    rw [← hs.tsum_sub hq]
    apply tsum_congr
    intro k
    simp only [gramIntegerJump,Nat.add_sub_cancel,f]
    ring
  rw [(gramIntegerJump_summable m n hm).tsum_eq_zero_add]
  simp only [gramIntegerJump,gramEndpoint,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),div_zero,zero_mul,zero_add]
  change (∑' k, gramDiscreteCorrection m n k) = ∑' k, gramIntegerJump m n (k+1)
  rw [hc,hj,hshift]

private theorem gramIntegerJump_off_multiple (m n k : ℕ) (hn : 0 < n)
    (h : ¬ n ∣ k) : gramIntegerJump m n k = 0 := by
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    exact h (dvd_zero n)
  simp [gramIntegerJump,binaryWavelet_integer_jump n k hn hk,h]

private theorem gramIntegerJump_multiple (m n j : ℕ) (hn : 0 < n) :
    gramIntegerJump m n (n*(j+1)) =
      binaryWaveletPrimitive m (n*(j+1))*binaryWaveletJump (j+1)/
        (((j+1:ℕ):ℝ)*(n:ℝ))^2 := by
  have hk : 0 < n*(j+1) := by positivity
  rw [gramIntegerJump,binaryWavelet_integer_jump n _ hn hk,if_pos (dvd_mul_right n _)]
  have hdiv : n*(j+1)/n = j+1 := Nat.mul_div_cancel_left (j+1) hn
  rw [hdiv]
  dsimp [gramEndpoint]
  push_cast
  ring

private theorem gramIntegerJump_block (m n j : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gramIntegerJump m n (n*j+k)) = gramIntegerJump m n (n*j) := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    apply gramIntegerJump_off_multiple m n _ hn
    intro hd
    have hmod := Nat.mod_eq_zero_of_dvd hd
    have hk' := Finset.mem_range.mp hk
    have he : (n*j+k)%n = k := by simp [Nat.add_mod,Nat.mod_eq_of_lt hk']
    rw [he] at hmod
    exact hk0 hmod
  · intro h0
    exact (h0 (Finset.mem_range.mpr hn)).elim

private theorem gramIntegerJump_partial_reindex (m n N : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n*N), gramIntegerJump m n k) =
      ∑ j ∈ Finset.range N, gramIntegerJump m n (n*j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,gramIntegerJump_block m n N hn,
      Finset.sum_range_succ]

private theorem gramIntegerJump_reindex (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∑' k, gramIntegerJump m n k) =
      ∑' j, binaryWaveletContinuousPrimitive m (((j+1:ℕ):ℝ)*(n:ℝ))*
        binaryWaveletJump (j+1)/(((j+1:ℕ):ℝ)*(n:ℝ))^2 := by
  have hs := gramIntegerJump_summable m n hm
  have hinj : Function.Injective (fun j : ℕ => n*j) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hn h
  have hsm : Summable (fun j : ℕ => gramIntegerJump m n (n*j)) := by
    simpa only [Function.comp_def] using hs.comp_injective hinj
  have hcofinal : Filter.Tendsto (fun N : ℕ => n*N) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
    exact Nat.le_mul_of_pos_left N hn
  have heq : (∑' k, gramIntegerJump m n k) = ∑' j, gramIntegerJump m n (n*j) := by
    have ht := hs.hasSum.tendsto_sum_nat.comp hcofinal
    simp only [Function.comp_def,gramIntegerJump_partial_reindex m n _ hn] at ht
    exact tendsto_nhds_unique ht hsm.hasSum.tendsto_sum_nat
  rw [heq,hsm.tsum_eq_zero_add]
  simp only [Nat.mul_zero,gramIntegerJump,gramEndpoint,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),div_zero,zero_mul,zero_add]
  apply tsum_congr
  intro j
  change gramIntegerJump m n (n*(j+1)) = _
  rw [gramIntegerJump_multiple m n j hn]
  have hx : (((j+1:ℕ):ℝ)*(n:ℝ)) = ((n*(j+1):ℕ):ℝ) := by push_cast; ring
  rw [hx,binaryWaveletContinuousPrimitive_nat m (n*(j+1)) hm]

private def gramCell (k : ℕ) : Set ℝ := Ico ((k:ℝ)+1) ((k:ℝ)+2)

private theorem gramCell_floor (k : ℕ) {x : ℝ} (hx : x ∈ gramCell k) : ⌊x⌋₊=k+1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [gramCell,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hx

private theorem gramCell_disjoint : Pairwise (Function.onFun Disjoint gramCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (Nat.add_right_cancel ((gramCell_floor i hi).symm.trans (gramCell_floor j hj)))

private theorem gramCell_union : (⋃ k,gramCell k)=Ici (1:ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    change (k:ℝ)+1 ≤ x ∧ x < (k:ℝ)+2 at hk
    exact le_trans (by linarith [Nat.cast_nonneg (α := ℝ) k] : (1:ℝ) ≤ (k:ℝ)+1) hk.1
  · intro hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hk1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
    let k := ⌊x⌋₊-1
    have he : k+1=⌊x⌋₊ := Nat.sub_add_cancel hk1
    apply Set.mem_iUnion.mpr
    refine ⟨k,?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one x
    rw [←he] at hlo hhi
    simpa only [gramCell,Set.mem_Ico,Nat.cast_add,Nat.cast_one,add_assoc,
      one_add_one_eq_two] using And.intro hlo hhi

private def gramCorrectionIntegrand (m n : ℕ) (x : ℝ) : ℝ :=
  binaryWaveletContinuousPrimitive m x*binaryWaveletStep n x/x^3

private theorem gramCorrectionIntegrand_ae_measurable (m n : ℕ) (hm : 0 < m) :
    AEStronglyMeasurable (gramCorrectionIntegrand m n) (volume.restrict (Ioi 1)) := by
  let P := fun x : ℝ => binaryWaveletPrimitive m ⌊x⌋₊ +
    (x-(⌊x⌋₊:ℝ))*dilationWaveletSequence 2 m ⌊x⌋₊
  have hB : Measurable (fun x : ℝ => binaryWaveletPrimitive m ⌊x⌋₊) :=
    (measurable_of_countable (binaryWaveletPrimitive m)).comp Nat.measurable_floor
  have hcast : Measurable (fun x : ℝ => (⌊x⌋₊ : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp Nat.measurable_floor
  have hf : Measurable (fun x : ℝ => dilationWaveletSequence 2 m ⌊x⌋₊) :=
    (measurable_of_countable (dilationWaveletSequence 2 m)).comp Nat.measurable_floor
  have hP : Measurable P := hB.add ((measurable_id.sub hcast).mul hf)
  have hQ : Measurable (fun x => P x*binaryWaveletStep n x/x^3) :=
    (hP.mul (binaryWaveletStep_measurable n)).div (measurable_id.pow_const 3)
  apply hQ.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num) (le_of_lt (show 1 < x from hx))
  have hc : x ∈ Icc (⌊x⌋₊:ℝ) ((⌊x⌋₊:ℝ)+1) :=
    ⟨Nat.floor_le hx0,(Nat.lt_floor_add_one x).le⟩
  simp only [gramCorrectionIntegrand,P,binaryWaveletContinuousPrimitive_on_cell m _ hm hc]

private theorem gramCorrectionIntegrand_integrable (m n : ℕ) (hm : 0 < m) :
    IntegrableOn (gramCorrectionIntegrand m n) (Ioi 1) := by
  have hbase := paretoStepEnergy_integrable (fun _ => (1:ℝ))
    (by simpa using positiveWeight_summable)
  have hmajor : IntegrableOn (fun x : ℝ => (m:ℝ)/x^2) (Ioi 1) := by
    simpa only [one_pow,mul_one_div] using! hbase.const_mul (m:ℝ)
  apply hmajor.mono' (gramCorrectionIntegrand_ae_measurable m n hm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 < x := hx
  have hx0 : 0 < x := by linarith
  have hb := binaryWaveletContinuousPrimitive_bounds m hm hx0.le
  have hf := binaryWaveletStep_abs_bound n x
  rw [gramCorrectionIntegrand,Real.norm_eq_abs,abs_div,abs_mul,
    abs_of_nonneg hb.1,abs_of_pos (pow_pos hx0 3)]
  calc
    _ ≤ (m:ℝ)/x^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul hb.2 hf (abs_nonneg _) (Nat.cast_nonneg m)
      simpa using hh
    _ ≤ (m:ℝ)/x^2 := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by positivity)
      nlinarith [sq_nonneg x,mul_nonneg (sq_nonneg x) (show 0 ≤ x-1 by linarith)]

private theorem gramCorrectionIntegrand_cell (m n j : ℕ) (hm : 0 < m) :
    2*(∫ x in gramCell j,gramCorrectionIntegrand m n x) =
      gramDiscreteCorrection m n (j+1) +
        positiveWeight (j+1)*(dilationWaveletSequence 2 m (j+1)*dilationWaveletSequence 2 n (j+1)) := by
  have he : (∫ x in gramCell j,gramCorrectionIntegrand m n x) =
      dilationWaveletSequence 2 n (j+1)*
        ∫ x in ((j+1:ℕ):ℝ)..(((j+1:ℕ):ℝ)+1), binaryWaveletContinuousPrimitive m x/x^3 := by
    have hstep : (∫ x in gramCell j,gramCorrectionIntegrand m n x) =
        ∫ x in gramCell j,dilationWaveletSequence 2 n (j+1)*
          (binaryWaveletContinuousPrimitive m x/x^3) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      simp only [gramCorrectionIntegrand,binaryWaveletStep,gramCell_floor j hx]
      ring
    rw [hstep,integral_const_mul]
    congr 1
    unfold gramCell
    rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith)]
    congr 1 <;> push_cast <;> ring
  rw [he]
  have hc := binaryWaveletContinuousPrimitive_weighted_cell m (j+1) hm (by omega)
  have hh := congrArg (fun z : ℝ => dilationWaveletSequence 2 n (j+1)*z) hc
  dsimp [gramDiscreteCorrection,gramEndpoint]
  push_cast at hh ⊢
  nlinarith [hh]

private theorem gramCorrectionIntegrand_integral_series (m n : ℕ) (hm : 0 < m) :
    2*(∫ x in Ioi (1:ℝ),gramCorrectionIntegrand m n x) =
      (∑' k,gramIntegerJump m n k) +
        paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n) := by
  have hI : IntegrableOn (gramCorrectionIntegrand m n) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact gramCorrectionIntegrand_integrable m n hm
  have hg := weighted_summable_of_bounded
    (bounded_product (binary_wavelet_abs_le m) (binary_wavelet_abs_le n))
  have hc := gramDiscreteCorrection_summable m n hm
  have hgs : Summable (fun k => positiveWeight (k+1)*
      (dilationWaveletSequence 2 m (k+1)*dilationWaveletSequence 2 n (k+1))) :=
    (summable_nat_add_iff 1).mpr hg
  have hcs : Summable (fun k => gramDiscreteCorrection m n (k+1)) :=
    (summable_nat_add_iff 1).mpr hc
  have hi : (∫ x in Ioi (1:ℝ),gramCorrectionIntegrand m n x) =
      ∑' k, ∫ x in gramCell k,gramCorrectionIntegrand m n x := by
    rw [← integral_Ici_eq_integral_Ioi,← gramCell_union]
    exact integral_iUnion (fun _ => measurableSet_Ico) gramCell_disjoint
      (by simpa only [gramCell_union] using hI)
  rw [hi,← tsum_mul_left]
  simp_rw [gramCorrectionIntegrand_cell m n _ hm]
  rw [hcs.tsum_add hgs]
  have hc0 : gramDiscreteCorrection m n 0 = 0 := by
    simp [gramDiscreteCorrection,dilationWaveletSequence,digitSequence]
  have hg0 : positiveWeight 0*(dilationWaveletSequence 2 m 0*dilationWaveletSequence 2 n 0)=0 := by
    simp [positiveWeight]
  have hec := hc.tsum_eq_zero_add
  have heg := hg.tsum_eq_zero_add
  rw [hc0,zero_add] at hec
  rw [hg0,zero_add] at heg
  rw [←hec,←heg,gramDiscreteCorrection_eq_jump m n hm]
  rfl

private theorem binaryWaveletStep_below_scale (n : ℕ) (hn : 0 < n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x < n) : binaryWaveletStep n x = 0 := by
  have hk : ⌊x⌋₊ < n := by exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hx0) hx)
  rw [binaryWaveletStep,dilationWaveletSequence_two_pullback,Nat.div_eq_of_lt hk]
  simp [dilationWaveletSequence,digitSequence]

private theorem gramCorrectionIntegrand_lower_endpoint (m n : ℕ) (hn : 0 < n) :
    (∫ x in Ioi (1:ℝ),gramCorrectionIntegrand m n x) =
      ∫ x in Ioi (n:ℝ),gramCorrectionIntegrand m n x := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have he : gramCorrectionIntegrand m n =ᵐ[volume.restrict (Ioi (1:ℝ))]
      (Ioi (n:ℝ)).indicator (gramCorrectionIntegrand m n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi (1 : ℝ))).ae_ne (n : ℝ)] with x hx hxne
    change 1 < x at hx
    change x ≠ (n : ℝ) at hxne
    by_cases hnx : (n:ℝ) < x
    · rw [Set.indicator_of_mem (show x ∈ Ioi (n : ℝ) from hnx)]
    · have hxn : x < n := lt_of_le_of_ne (le_of_not_gt hnx) hxne
      have hx0 : 0 ≤ x := by linarith
      rw [Set.indicator_of_notMem (show x ∉ Ioi (n : ℝ) from hnx)]
      simp [gramCorrectionIntegrand, binaryWaveletStep_below_scale n hn hx0 hxn]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,Ioi_inter_Ioi,max_eq_left hn1]

/-- Exact continuous signed integration-by-parts identity for the actual
binary wavelets, including all arithmetic jumps and the full infinite tail. -/
theorem binaryWaveletContinuousGram_proved : BinaryWaveletContinuousGramTarget := by
  intro m n hm hn
  have h := gramCorrectionIntegrand_integral_series m n hm
  rw [gramIntegerJump_reindex m n hm hn,gramCorrectionIntegrand_lower_endpoint m n hn] at h
  dsimp [gramCorrectionIntegrand] at h
  push_cast at h ⊢
  linarith

end
end RiemannResearch.RH.Pareto

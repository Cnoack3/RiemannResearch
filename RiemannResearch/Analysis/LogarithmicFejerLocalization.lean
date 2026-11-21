import RiemannResearch.Analysis.LogarithmicFejerKernel

/-!
# Fourier localization of the logarithmic prime-pair variance

All frequencies here belong to the additive circle on the integer index.
The character distance from zero is `chord`. The estimates apply to the
actual annular von Mangoldt polynomial with both sites cut off.
-/

noncomputable section
open Finset Filter MeasureTheory AddCircle
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.FractionalFejer

/-- Chordal distance of the first additive character from the identity. -/
def chord (t : Circle₁) : ℝ := ‖(1 : ℂ) - fourier 1 t‖

def centralArc (δ : ℝ) : Set Circle₁ := {t | chord t < δ}

theorem measurableSet_centralArc (δ : ℝ) : MeasurableSet (centralArc δ) :=
  (isOpen_lt ((continuous_const.sub (fourier (T := (1 : ℝ)) 1).continuous).norm)
    continuous_const).measurableSet

private theorem continuous_dirichlet (m : ℕ) : Continuous (dirichlet m) :=
  continuous_finsetSum _ fun j _ => (fourier (j : ℤ)).continuous

private theorem continuous_kernel (m : ℕ) (r : ℝ) : Continuous (kernel m r) :=
  (((continuous_dirichlet m).norm.pow 2).const_mul _).add
    (((continuous_dirichlet (m+1)).norm.pow 2).const_mul _)

theorem continuous_polynomial (I : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (polynomial I a) :=
  continuous_finsetSum _ fun n _ => (fourier (n : ℤ)).continuous.const_mul _

theorem dirichlet_geometric (m : ℕ) (t : Circle₁) :
    (1 - fourier 1 t) * dirichlet m t = 1 - fourier (m : ℤ) t := by
  induction m with
  | zero => simp [dirichlet]
  | succ m ih =>
    rw [show dirichlet (m+1) t = dirichlet m t + fourier (m : ℤ) t from
      sum_range_succ _ _, mul_add, ih, Nat.cast_succ, fourier_add]
    ring

private theorem chord_mul_dirichlet_le (m : ℕ) (t : Circle₁) :
    chord t * ‖dirichlet m t‖ ≤ 2 := by
  calc
    _ = ‖(1 - fourier 1 t) * dirichlet m t‖ := (norm_mul _ _).symm
    _ = ‖1 - fourier (m : ℤ) t‖ := by rw [dirichlet_geometric]
    _ ≤ ‖(1 : ℂ)‖ + ‖fourier (m : ℤ) t‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, show ‖fourier (m : ℤ) t‖ = 1 from Circle.norm_coe _]; norm_num

/-- Uniform in the length and in the fractional interpolation. -/
theorem chord_sq_mul_kernel_le (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (t : Circle₁) :
    chord t ^ 2 * kernel H r t ≤ 4 := by
  have hb (j : ℕ) : (chord t * ‖dirichlet j t‖)^2 ≤ 4 := by
    have hn : 0 ≤ chord t * ‖dirichlet j t‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [sq_le_sq' (by linarith : -(2 : ℝ) ≤ chord t * ‖dirichlet j t‖)
      (chord_mul_dirichlet_le j t)]
  calc
    _ = (1-r)*(chord t * ‖dirichlet H t‖)^2 + r*(chord t * ‖dirichlet (H+1) t‖)^2 := by
      unfold kernel
      ring
    _ ≤ (1-r)*4 + r*4 := add_le_add
      (mul_le_mul_of_nonneg_left (hb _) (sub_nonneg.mpr hr')) (mul_le_mul_of_nonneg_left (hb _) hr)
    _ = 4 := by ring

theorem integral_polynomial_sq (I : Finset ℕ) (a : ℕ → ℝ) :
    (∫ t : Circle₁, ‖polynomial I a t‖^2 ∂haarAddCircle) = ∑ n ∈ I, (a n)^2 := by
  simpa [energy, kernel, dirichlet, fourier_zero] using energy_eq 0 1 I a

/-- Restricted Fejér energy, with the same probability Haar normalization as `energy`. -/
def energyOn (s : Set Circle₁) (H : ℕ) (r : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∫ t in s, kernel H r t * ‖polynomial I a t‖^2 ∂haarAddCircle

private theorem integrable_energy (H : ℕ) (r : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) :
    Integrable (fun t => kernel H r t * ‖polynomial I a t‖^2) haarAddCircle :=
  Continuous.integrable_of_hasCompactSupport
    ((continuous_kernel H r).mul ((continuous_polynomial I a).norm.pow 2))
    (HasCompactSupport.of_compactSpace _)

theorem energy_split_arc (δ : ℝ) (H : ℕ) (r : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) :
    energyOn (centralArc δ) H r I a + energyOn (centralArc δ)ᶜ H r I a = energy H r I a :=
  integral_add_compl (measurableSet_centralArc δ) (integrable_energy H r I a)

theorem energyOn_nonneg (s : Set Circle₁) (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (I : Finset ℕ) (a : ℕ → ℝ) : 0 ≤ energyOn s H r I a :=
  integral_nonneg fun t => mul_nonneg (kernel_nonneg hr hr' H t) (sq_nonneg _)

/-- Finite tail estimate, with an explicit constant and no arithmetic hypotheses. -/
theorem offArc_energy_le (δ : ℝ) (hδ : 0 ≤ δ) (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (I : Finset ℕ) (a : ℕ → ℝ) :
    δ^2 * energyOn (centralArc δ)ᶜ H r I a ≤ 4 * ∑ n ∈ I, (a n)^2 := by
  have hp : Integrable (fun t => ‖polynomial I a t‖^2) haarAddCircle :=
    ((continuous_polynomial I a).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold energyOn
  rw [← integral_const_mul, ← integral_polynomial_sq, ← integral_const_mul]
  calc
    _ ≤ ∫ t in (centralArc δ)ᶜ, 4 * ‖polynomial I a t‖^2 ∂haarAddCircle := by
      apply integral_mono_ae ((integrable_energy H r I a).restrict.const_mul _)
        ((hp.const_mul _).restrict)
      filter_upwards [ae_restrict_mem (μ := haarAddCircle) (measurableSet_centralArc δ).compl]
        with t ht
      have ht' : δ ≤ chord t := le_of_not_gt ht
      have hk := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ ht' 2)
        (kernel_nonneg hr hr' H t)).trans
        (chord_sq_mul_kernel_le H hr hr' t)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hk (sq_nonneg ‖polynomial I a t‖)
    _ ≤ _ := setIntegral_le_integral (hp.const_mul 4) (Eventually.of_forall fun t =>
      mul_nonneg (by norm_num) (sq_nonneg _))

/-- Exact mean of the squared geometric numerators, including the oscillatory term. -/
theorem chord_sq_mul_sum_dirichlet_sq (m : ℕ) (t : Circle₁) :
    chord t ^ 2 * (∑ j ∈ range m, ‖dirichlet j t‖^2) =
      2*(m : ℝ) - 2*(dirichlet m t).re := by
  have mode (j : ℕ) :
      chord t ^ 2 * ‖dirichlet j t‖^2 = 2 - 2*(fourier (j : ℤ) t).re := by
    rw [← mul_pow, chord, ← norm_mul, dirichlet_geometric]
    let z : ℂ := fourier (j : ℤ) t
    have hn : ‖z‖ = 1 := Circle.norm_coe _
    have hsq := Complex.sq_norm_sub_sq_re z
    rw [hn] at hsq
    change ‖1-z‖^2 = 2-2*z.re
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    nlinarith
  induction m with
  | zero => simp [dirichlet]
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih, mode, Nat.cast_succ,
      show dirichlet (m+1) t = dirichlet m t + fourier (m : ℤ) t from sum_range_succ _ _,
      Complex.add_re]
    ring

/-- Averages over shorter kernels control every fractional-width tail at resolution 1/m. -/
theorem kernel_le_dirichlet_average (m H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (t : Circle₁) (hmt : 4 ≤ (m : ℝ) * chord t) :
    (m : ℝ) * kernel H r t ≤ 4 * ∑ j ∈ range m, ‖dirichlet j t‖^2 := by
  have hc : 0 < chord t := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) m) hn]
  have hd : ‖dirichlet m t‖ ≤ (m : ℝ)/2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [chord_mul_dirichlet_le m t]
  have lower : (m : ℝ) ≤ chord t^2 * ∑ j ∈ range m, ‖dirichlet j t‖^2 := by
    rw [chord_sq_mul_sum_dirichlet_sq]
    linarith [Complex.re_le_norm (dirichlet m t)]
  calc
    _ ≤ (chord t^2 * ∑ j ∈ range m, ‖dirichlet j t‖^2) * kernel H r t :=
      mul_le_mul_of_nonneg_right lower (kernel_nonneg hr hr' H t)
    _ = (chord t^2 * kernel H r t) * ∑ j ∈ range m, ‖dirichlet j t‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (chord_sq_mul_kernel_le H hr hr' t)
      (sum_nonneg fun _ _ => sq_nonneg _)

theorem offArc_energy_le_short_energies (δ : ℝ) (m H : ℕ) (hm : 4 ≤ (m : ℝ) * δ)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (I : Finset ℕ) (a : ℕ → ℝ) :
    (m : ℝ) * energyOn (centralArc δ)ᶜ H r I a ≤
      4 * ∑ j ∈ range m, energy j 0 I a := by
  let g (j : ℕ) (t : Circle₁) := ‖dirichlet j t‖^2 * ‖polynomial I a t‖^2
  have hg (j : ℕ) : Integrable (g j) haarAddCircle :=
    (((continuous_dirichlet j).norm.pow 2).mul ((continuous_polynomial I a).norm.pow 2)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := (integrable_finsetSum (range m) fun j _ => hg j).const_mul (4 : ℝ)
  have he (j : ℕ) : (∫ t, g j t ∂haarAddCircle) = energy j 0 I a := by simp [energy, kernel, g]
  calc
    _ = ∫ t in (centralArc δ)ᶜ, (m : ℝ) * (kernel H r t * ‖polynomial I a t‖^2)
        ∂haarAddCircle := (integral_const_mul _ _).symm
    _ ≤ ∫ t in (centralArc δ)ᶜ, 4 * ∑ j ∈ range m, g j t ∂haarAddCircle := by
      apply integral_mono_ae ((integrable_energy H r I a).restrict.const_mul _) hs.restrict
      filter_upwards [ae_restrict_mem (μ := haarAddCircle) (measurableSet_centralArc δ).compl]
        with t ht
      have ht' : δ ≤ chord t := le_of_not_gt ht
      have hk := kernel_le_dirichlet_average m H hr hr' t
        (hm.trans (mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg m)))
      simpa only [g, mul_assoc, sum_mul] using
        mul_le_mul_of_nonneg_right hk (sq_nonneg ‖polynomial I a t‖)
    _ ≤ ∫ t, 4 * ∑ j ∈ range m, g j t ∂haarAddCircle :=
      setIntegral_le_integral hs (Eventually.of_forall fun _ =>
        mul_nonneg (by norm_num) (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = _ := by rw [integral_const_mul, integral_finsetSum _ fun j _ => hg j]; simp_rw [he]

/-- A bound at all shorter integer widths gives a 1/δ bound on the exterior integral. -/
theorem offArc_energy_le_of_short_bound {L δ G : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : 5 ≤ δ * L) (hG : 0 ≤ G) (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (I : Finset ℕ) (a : ℕ → ℝ)
    (hshort : ∀ j ≤ ⌊L⌋₊, energy j 0 I a ≤ (j : ℝ) * G) :
    energyOn (centralArc δ)ᶜ H r I a ≤ (20 / δ) * G := by
  let m := ⌈4 / δ⌉₊
  have hm : 4 ≤ (m : ℝ) * δ := (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have hm0 : 0 < (m : ℝ) := lt_of_not_ge fun hn => by
    linarith [mul_nonpos_of_nonpos_of_nonneg hn hδ.le]
  have hml : (m : ℝ) ≤ 5 / δ := by
    have ha : (m : ℝ) < 4 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    calc
      _ ≤ 4 / δ + 1 := ha.le
      _ ≤ _ := by
        apply (le_div_iff₀ hδ).mpr
        rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul]
        linarith
  have hw : m ≤ ⌊L⌋₊ := Nat.le_floor (hml.trans ((div_le_iff₀ hδ).mpr (by linarith)))
  have hs : (∑ j ∈ range m, energy j 0 I a) ≤ (m : ℝ) * ((m : ℝ) * G) := by
    calc
      _ ≤ ∑ _j ∈ range m, (m : ℝ) * G := by
        apply sum_le_sum
        intro j hj
        have hjm := (mem_range.mp hj).le
        exact (hshort j (hjm.trans hw)).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hG)
      _ = _ := by simp
  have h := (offArc_energy_le_short_energies δ m H hm hr hr' I a).trans
    (mul_le_mul_of_nonneg_left hs (by norm_num))
  calc
    _ ≤ 4 * (m : ℝ) * G := (mul_le_mul_iff_right₀ hm0).mp (by
      convert h using 1
      ring)
    _ ≤ (4 * (5 / δ)) * G := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hml (by norm_num)) hG
    _ = _ := by ring

/-- A singleton coefficient provides the constant spectral density. -/
theorem energy_singleton_zero (H : ℕ) (r : ℝ) :
    energy H r {0} (fun _ => 1) = (H : ℝ) + r := by
  have hz (h : ℕ) (hh : h ∈ Ioc 0 H) : correlation {0} (fun _ => 1) h = 0 := by
    simp [correlation, (mem_Ioc.mp hh).1.ne']
  rw [energy_eq, sum_eq_zero (s := Ioc 0 H) (fun h hh => by rw [hz h hh, mul_zero])]
  simp

/-- The signed local spectral discrepancy is the integral of the off-diagonal part. -/
theorem energyOn_sub_diagonal (s : Set Circle₁) (H : ℕ) (r : ℝ)
    (I : Finset ℕ) (a : ℕ → ℝ) :
    energyOn s H r I a - (∑ n ∈ I, (a n)^2) * energyOn s H r {0} (fun _ => 1) =
      ∫ t in s, kernel H r t * (‖polynomial I a t‖^2 - ∑ n ∈ I, (a n)^2) ∂haarAddCircle := by
  have hk : Integrable (kernel H r) haarAddCircle :=
    (continuous_kernel H r).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hone : energyOn s H r {0} (fun _ => 1) = ∫ t in s, kernel H r t ∂haarAddCircle := by
    simp [energyOn, polynomial]
  rw [hone, ← integral_const_mul, energyOn, ← integral_sub (integrable_energy H r I a).restrict
    (hk.restrict.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by ring

/-- An unweighted local cosine coefficient of a real spectral density. -/
def cosineMoment (s : Set Circle₁) (g : Circle₁ → ℝ) (h : ℕ) : ℝ :=
  ∫ t in s, (fourier (h : ℤ) t).re * g t ∂haarAddCircle

theorem integral_kernel_mul_eq_cosineMoments (s : Set Circle₁) (H : ℕ) (r : ℝ)
    (g : Circle₁ → ℝ) (hg : Continuous g) :
    (∫ t in s, kernel H r t * g t ∂haarAddCircle) =
      ((H : ℝ) + r) * cosineMoment s g 0 +
        ∑ h ∈ Ioc 0 H, (2 * ((H : ℝ) + r - h)) * cosineMoment s g h := by
  have hg' := (hg.integrable_of_hasCompactSupport (μ := haarAddCircle)
    (HasCompactSupport.of_compactSpace _)).restrict (s := s)
  have hi (h : ℕ) :
      Integrable (fun t : Circle₁ => (fourier (h : ℤ) t).re * g t) (haarAddCircle.restrict s) :=
    (Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_re.comp (fourier (h : ℤ)).continuous).mul hg)
      (HasCompactSupport.of_compactSpace _) (μ := haarAddCircle)).restrict
  have hzero : cosineMoment s g 0 = ∫ t in s, g t ∂haarAddCircle := by
    simp [cosineMoment]
  have hex (t : Circle₁) : kernel H r t * g t = ((H : ℝ) + r) * g t +
      ∑ h ∈ Ioc 0 H, (2 * ((H : ℝ) + r - h)) * ((fourier (h : ℤ) t).re * g t) := by
    rw [kernel_cosine_expansion, add_mul, sum_mul]
    simp only [mul_assoc]
  simp_rw [hex]
  rw [integral_add (hg'.const_mul _) (integrable_finsetSum _ fun h _ => (hi h).const_mul _),
    integral_const_mul, integral_finsetSum _ fun h _ => (hi h).const_mul _, hzero]
  simp only [integral_const_mul, cosineMoment]

/-- The exact operator bound for testing a fractional kernel is its value at zero. -/
theorem abs_integral_kernel_mul_le_modes (s : Set Circle₁) (H : ℕ) {r b : ℝ}
    (hr : 0 ≤ r) (g : Circle₁ → ℝ) (hg : Continuous g)
    (hb : ∀ h ≤ H, |cosineMoment s g h| ≤ b) :
    |∫ t in s, kernel H r t * g t ∂haarAddCircle| ≤ kernel H r 0 * b := by
  let w (h : ℕ) := 2 * ((H : ℝ) + r - h)
  have hw (h : ℕ) (hh : h ∈ Ioc 0 H) : 0 ≤ w h := by
    have hle : (h : ℝ) ≤ H := by exact_mod_cast (mem_Ioc.mp hh).2
    dsimp [w]
    linarith
  have hK := kernel_cosine_expansion H r 0
  simp only [fourier_eval_zero, Complex.one_re, mul_one] at hK
  rw [integral_kernel_mul_eq_cosineMoments s H r g hg]
  calc
    _ ≤ |((H : ℝ) + r) * cosineMoment s g 0| +
        |∑ h ∈ Ioc 0 H, w h * cosineMoment s g h| := abs_add_le _ _
    _ ≤ ((H : ℝ) + r) * b + ∑ h ∈ Ioc 0 H, w h * b := by
      apply add_le_add
      · have hp := add_nonneg (Nat.cast_nonneg (α := ℝ) H) hr
        rw [abs_mul, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (hb 0 (Nat.zero_le _)) hp
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
        intro h hh
        rw [abs_mul, abs_of_nonneg (hw h hh)]
        exact mul_le_mul_of_nonneg_left (hb h (mem_Ioc.mp hh).2) (hw h hh)
    _ = _ := by rw [hK, ← sum_mul, ← add_mul]

end RiemannResearch.Analysis.FractionalFejer

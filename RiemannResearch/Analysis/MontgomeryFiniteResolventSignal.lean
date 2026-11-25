import RiemannResearch.Analysis.FourierL1L2Plancherel
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryLocalMass

/-! # The finite positive-height rational zero signal

Angular-frequency Plancherel identifies the squared norm of the actual
finite rational zero signal in the BGSTB explicit formula with the complex
pair sum. Every positive zero at or below the cutoff appears with its multiplicity.
The rational statistic and angular normalization are from Baluyot, Goldston,
Suriajaya and Turnage-Butterbaugh, §2, <https://doi.org/10.4064/aa230612-20-3>.
The outgoing estimates below use the repository's unconditional local zero count.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped BigOperators FourierTransform
namespace RiemannResearch.Analysis.MontgomeryFiniteResolventSignal
open MontgomeryPoisson MontgomeryComplexGram MontgomeryHorizontalTransfer
open MontgomeryFormFactor ActualZeroOrdinate
variable {ι : Type*} [Fintype ι]

/-- Fourier transform of each bilateral exponential, in angular frequency. -/
def rationalTerm (z : ℂ) (t : ℝ) : ℂ := 2 / (1 - (z - (t : ℂ)*I)^2)

def signal (z c : ι → ℂ) (t : ℝ) : ℂ := ∑ i, c i * rationalTerm (z i) t

private theorem term_strip {z : ℂ} (hz : |z.re| < 1) (t : ℝ) :
    |(z - (t : ℂ)*I).re| < 1 := by simpa using hz

private theorem weighted_eq (z c : ι → ℂ) (s : ℝ) :
    weightedSignal z c s = ∑ i, c i * feature 1 (z i) s := by
  simp only [weightedSignal,complexSignal,Finset.mul_sum,feature,one_mul,
    Complex.exp_add,Complex.ofReal_exp]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedSignal_integrable (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    Integrable (weightedSignal z c) := by
  change Integrable (fun s => weightedSignal z c s)
  simp_rw [weighted_eq]
  exact integrable_finsetSum _ (fun i _ => (integrable_feature 1 _ (hz i)).const_mul (c i))

theorem fourier_weightedSignal (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) (w : ℝ) :
    𝓕 (weightedSignal z c) w = signal z c (2*Real.pi*w) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have hosc (s : ℝ) (i : ι) :
      Complex.exp (((-2*Real.pi*s*w : ℝ) : ℂ)*I) * feature 1 (z i) s =
        feature 1 (z i - ((2*Real.pi*w : ℝ) : ℂ)*I) s := by
    unfold feature
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he (s : ℝ) :
      Complex.exp (((-2*Real.pi*s*w : ℝ) : ℂ)*I) * weightedSignal z c s =
        ∑ i, c i * feature 1 (z i - ((2*Real.pi*w : ℝ) : ℂ)*I) s := by
    rw [weighted_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hosc]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => (integrable_feature 1 _
    (term_strip (hz i) (2*Real.pi*w))).const_mul (c i))]
  unfold signal rationalTerm
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_feature 1 _ (term_strip (hz i) (2*Real.pi*w))]
  norm_num

theorem signal_plancherel (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    (∫ t : ℝ, ‖signal z c t‖^2) = 2*Real.pi*(complexKernel z c).re := by
  have hp := RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable
    (weightedSignal_integrable z c hz) (weightedSignal_memLp z c hz)
  simp_rw [fourier_weightedSignal z c hz,weightedSignal_sq] at hp
  rw [complex_gram_re z c hz] at hp
  have hsc := Measure.integral_comp_mul_left (fun t : ℝ => ‖signal z c t‖^2) (2*Real.pi)
  have hc : 0 < 2*Real.pi := by positivity
  simp only [abs_of_pos (inv_pos.mpr hc),smul_eq_mul] at hsc
  rw [hp] at hsc
  calc
    _ = (2*Real.pi) * ((2*Real.pi)⁻¹ * ∫ t : ℝ, ‖signal z c t‖^2) := by field_simp
    _ = _ := by rw [← hsc]

/-- The actual positive-height complex-zero signal, with multiplicities. -/
def actualSignal (T u t : ℝ) : ℂ :=
  signal (fun i : Copies T => i.1.1 - 1/2)
    (fun i => Complex.exp ((u : ℂ)*(i.1.1 - 1/2))) t

private theorem centered_re (T : ℝ) (i : Copies T) :
    (i.1.1 - 1/2 : ℂ).re = i.1.1.re - 1/2 := by norm_num

/-- The exact statistic on the left of PositiveCutoffThirdSignalSource. -/
theorem actualSignal_plancherel (T u : ℝ) :
    (∫ t : ℝ, ‖actualSignal T u t‖^2) = 2*Real.pi*(actualComplexPairSum T u).re := by
  have hz (i : Copies T) : |(i.1.1 - 1/2 : ℂ).re| < 1 := by
    rw [centered_re]
    linarith [displacement_lt_half i.1.2]
  simpa only [actualSignal,actual_complex_kernel] using
    signal_plancherel (fun i : Copies T => i.1.1-1/2)
      (fun i => Complex.exp ((u : ℂ)*(i.1.1-1/2))) hz

/-- The real part of the resolvent denominator is at least 3/4+(Im z-t)²
throughout the full centered strip, including off-critical zeros. -/
theorem norm_rationalTerm_le_exact (z : ℂ) (hz : |z.re| ≤ 1/2) (t : ℝ) :
    ‖rationalTerm z t‖ ≤ 2/(3/4+(z.im-t)^2) := by
  let q := z - (t : ℂ)*I
  have hr : q.re = z.re := by simp [q]
  have hi : q.im = z.im-t := by simp [q]
  have hsq : z.re^2 ≤ (1/2 : ℝ)^2 :=
    (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hz 2)
  have hden : 3/4+(z.im-t)^2 ≤ ‖1-q^2‖ := by
    apply le_trans _ (Complex.re_le_norm _)
    rw [Complex.sub_re,Complex.one_re,pow_two q,Complex.mul_re,hr,hi]
    linarith
  change ‖(2:ℂ)/(1-q^2)‖ ≤ _
  rw [norm_div,Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

theorem norm_rationalTerm_le (z : ℂ) (hz : |z.re| ≤ 1 / 2) (t : ℝ) :
    ‖rationalTerm z t‖ ≤ 8/(1+(z.im-t)^2) := by
  apply (norm_rationalTerm_le_exact z hz t).trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (z.im-t)]

open MontgomeryLocalMass GaussianCellGeometry MarkedFourierTail

private theorem selected_window_sum_le (s : Finset ℤ) (rank : ℤ → ℕ)
    (hinj : Set.InjOn rank (s : Set ℤ)) {R : ℝ} (hR : 1 ≤ R) :
    ∑ a ∈ s, 1/(R + (rank a : ℝ))^2 ≤ 2/R := by
  classical
  have hs := summable_window_tail (fun _ => (1:ℝ)) hR (by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl)
  calc
    _ = ∑ n ∈ s.image rank, 1/(R + (n : ℝ))^2 := by rw [Finset.sum_image hinj]
    _ ≤ ∑' n : ℕ, 1/(R+(n : ℝ))^2 := hs.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ 2/R := by
      simpa using (window_tsum_tail_le (fun _ => (1:ℝ)) hR
        (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl))

private def cell (T : ℝ) (i : Copies T) := Int.floor (-copyOrdinate T i)

private theorem rational_window_bound {T u t R C : ℝ} (hu : 0 ≤ u) (hR : 1 ≤ R)
    (hC : 0 ≤ C) (rank : ℤ → ℕ)
    (hinj : Set.InjOn rank ((Finset.univ.image (cell T) : Finset ℤ) : Set ℤ))
    (hmass : ∀ a ∈ Finset.univ.image (cell T), occupancy Finset.univ (cell T) a ≤ C)
    (hd : ∀ i : Copies T, R+(rank (cell T i) : ℝ) ≤ 2+|copyOrdinate T i-t|) :
    ‖actualSignal T u t‖ ≤ 80 * Real.exp (u/2) * C/R := by
  classical
  let A := Real.exp (u/2)
  let s := (Finset.univ : Finset (Copies T))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hi (i : Copies T) :
      ‖Complex.exp ((u:ℂ)*(i.1.1-1/2)) * rationalTerm (i.1.1-1/2) t‖ ≤
        A * 40 * (1/(R+(rank (cell T i) : ℝ))^2) := by
    have hre := displacement_lt_half i.1.2
    have hweight : ‖Complex.exp ((u:ℂ)*(i.1.1-1/2))‖ ≤ A := by
      rw [Complex.norm_exp, Complex.re_ofReal_mul,centered_re]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ u*(1/2) := mul_le_mul_of_nonneg_left (abs_lt.mp hre).2.le hu
        _ = _ := by ring
    have hq := norm_rationalTerm_le (i.1.1 - 1/2) (by rw [centered_re]; exact hre.le) t
    have him : (i.1.1 - 1/2 : ℂ).im = copyOrdinate T i := by simp [copyOrdinate]
    rw [him] at hq
    let d := copyOrdinate T i-t
    let v := R+(rank (cell T i) : ℝ)
    have hpos : 0 < v := by dsimp [v]; linarith [Nat.cast_nonneg (α := ℝ) (rank (cell T i))]
    have htemp : v^2 ≤ (2+|d|)^2 := pow_le_pow_left₀ hpos.le (hd i) 2
    have hden : v^2 ≤ 5*(1+d^2) := by
      nlinarith only [htemp,sq_abs d,sq_nonneg (2*|d|-1)]
    have hb : 8/(1+d^2) ≤ 40 * (1/v^2) := by
      rw [mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hpos)).mpr
      linarith
    rw [norm_mul]
    exact (mul_le_mul hweight (hq.trans hb) (norm_nonneg _) hA).trans_eq (by ring)
  change ‖∑ i ∈ s, Complex.exp ((u:ℂ)*(i.1.1-1/2)) * rationalTerm (i.1.1-1/2) t‖ ≤ _
  calc
    _ ≤ ∑ i ∈ s, ‖Complex.exp ((u:ℂ)*(i.1.1-1/2)) * rationalTerm (i.1.1-1/2) t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, A * 40 * (1/(R+(rank (cell T i) : ℝ))^2) := Finset.sum_le_sum fun i _ => hi i
    _ = A*40 * ∑ a ∈ s.image (cell T), occupancy s (cell T) a * (1/(R+(rank a : ℝ))^2) := by
      rw [← Finset.mul_sum, sum_by_cells s (cell T) (fun a => 1/(R+(rank a : ℝ))^2)]
    _ ≤ A*40 * ∑ a ∈ s.image (cell T), C*(1/(R+(rank a : ℝ))^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (hmass a ha) (by positivity)
    _ ≤ A*40*(C*(2/R)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (selected_window_sum_le _ _ hinj hR) hC) (by positivity)
    _ = _ := by dsimp [A]; ring

/-- Both outside tails of the finite positive-height actual zero resolvent
decay by the distance from the window. The constant is uniform in T and u. -/
theorem exists_actualSignal_outside_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T u : ℝ, 0 ≤ T → 0 ≤ u →
      (∀ t : ℝ, t ≤ 0 → ‖actualSignal T u t‖ ≤
        K * Real.exp (u/2) * Real.log (T+3)/(1-t)) ∧
      (∀ t : ℝ, T ≤ t → ‖actualSignal T u t‖ ≤
        K * Real.exp (u/2) * Real.log (T+3)/(1+(t-T))) := by
  classical
  obtain ⟨C,hC,hmass⟩ := actual_cell_occupancy_bound
  refine ⟨80*C, by linarith, fun T u hT hu => ?_⟩
  have hmass' := hmass T hT
  have hCL : 0 ≤ C*Real.log (T+3) := mul_nonneg (by linarith)
    (Real.log_nonneg (by linarith))
  let cells := (Finset.univ : Finset (Copies T)).image (cell T)
  have hab (a : ℤ) (ha : a ∈ cells) : Int.floor (-T) ≤ a ∧ a ≤ -1 := by
    obtain ⟨i,hi,ha⟩ := Finset.mem_image.mp ha
    rw [← ha]
    have h := mem_cutoff.mp i.1.2
    have hn : -copyOrdinate T i < 0 := by exact neg_neg_of_pos h.2.1
    exact ⟨Int.floor_mono (neg_le_neg h.2.2), by
      have h' : Int.floor (-copyOrdinate T i) < (0:ℤ) := Int.floor_lt.mpr (by simpa using hn)
      change Int.floor (-copyOrdinate T i) ≤ -1
      omega⟩
  constructor
  · intro t ht
    let rank : ℤ → ℕ := fun a => (-a-1).toNat
    have inj : Set.InjOn rank (cells : Set ℤ) := by
      intro a ha b hb he
      have h1 := (hab a ha).2; have h2 := (hab b hb).2
      dsimp [rank] at he
      omega
    have hd (i : Copies T) : 1-t+(rank (cell T i) : ℝ) ≤ 2+|copyOrdinate T i-t| := by
      have hz := (mem_cutoff.mp i.1.2).2.1
      have hz' : 0 ≤ copyOrdinate T i-t := by change 0 < copyOrdinate T i at hz; linarith
      rw [abs_of_nonneg hz']
      have hneg := (hab (cell T i)
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).2
      have hev : ((rank (cell T i) : ℕ) : ℤ) = -cell T i-1 := Int.toNat_of_nonneg (by omega)
      have he : (rank (cell T i) : ℝ) = -(cell T i : ℝ)-1 := by exact_mod_cast hev
      have hfloor := Int.lt_floor_add_one (-copyOrdinate T i)
      rw [he]
      dsimp [cell]
      linarith
    exact (rational_window_bound hu (by linarith : 1 ≤ 1-t)
      hCL rank inj hmass' hd).trans_eq (by ring)
  · intro t ht
    let rank : ℤ → ℕ := fun a => (a-Int.floor (-T)).toNat
    have inj : Set.InjOn rank (cells : Set ℤ) := by
      intro a ha b hb he
      have h1 := (hab a ha).1; have h2 := (hab b hb).1
      dsimp [rank] at he
      omega
    have hd (i : Copies T) : 1+(t-T)+(rank (cell T i) : ℝ) ≤ 2+|copyOrdinate T i-t| := by
      have hz : copyOrdinate T i ≤ T := (mem_cutoff.mp i.1.2).2.2
      rw [abs_of_nonpos (by linarith : copyOrdinate T i-t ≤ 0)]
      have h0 := (hab (cell T i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)).1
      have hev : ((rank (cell T i) : ℕ) : ℤ) = cell T i-Int.floor (-T) := Int.toNat_of_nonneg (by omega)
      have he : (rank (cell T i) : ℝ) = (cell T i : ℝ)-(Int.floor (-T) : ℝ) := by exact_mod_cast hev
      have hfloor := Int.floor_le (-copyOrdinate T i)
      have hfloorT := Int.lt_floor_add_one (-T)
      rw [he]
      dsimp [cell]
      linarith
    exact (rational_window_bound hu (by linarith : 1 ≤ 1+(t-T))
      hCL rank inj hmass' hd).trans_eq (by ring)

private theorem actualSignal_sq_integrable (T u : ℝ) :
    Integrable (fun t : ℝ => ‖actualSignal T u t‖^2) := by
  let z : Copies T → ℂ := fun i => i.1.1 - 1/2
  let c : Copies T → ℂ := fun i => Complex.exp ((u:ℂ)*z i)
  have hz (i : Copies T) : |(z i).re| < 1 := by
    change |(i.1.1-1/2 : ℂ).re| < 1
    rw [centered_re]; linarith [displacement_lt_half i.1.2]
  let f := weightedSignal z c
  have h1 := weightedSignal_integrable z c hz
  have h2 := weightedSignal_memLp z c hz
  have he := RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable h1 h2
  have hm : MemLp (𝓕 f) 2 := (memLp_congr_ae he).mp
    (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  apply (integrable_comp_mul_right_iff _ (by positivity : 2*Real.pi ≠ 0)).mp
  simpa only [f,fourier_weightedSignal z c hz,actualSignal,z,c,mul_comm _ (2*Real.pi)] using hi

private theorem integral_Ioi_shift (g : ℝ → ℝ) (a b : ℝ) :
    (∫ t in Ioi a, g t) = ∫ r in Ioi b, g (r+(a-b)) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self (μ := volume) ((Ioi a).indicator g) (a-b)]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : b < r
  · rw [Set.indicator_of_mem (show r+(a-b) ∈ Ioi a by change a < r+(a-b); linarith),
      Set.indicator_of_mem (show r ∈ Ioi b from hr)]
  · rw [Set.indicator_of_notMem (show r+(a-b) ∉ Ioi a by change ¬ a < r+(a-b); linarith),
      Set.indicator_of_notMem (show r ∉ Ioi b from hr)]

private theorem shifted_endpoint_energy_le (g : ℝ → ℝ) {B : ℝ} (h0 : ∀ r, 0 ≤ g r)
    (hg : ∀ r : ℝ, 1 < r → g r ≤ (B/r)^2) :
    (∫ r in Ioi (1:ℝ), g r) ≤ B^2 := by
  have hm : IntegrableOn (fun r : ℝ => B^2 * r^(-2:ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) zero_lt_one).const_mul _
  calc
    _ ≤ ∫ r in Ioi (1:ℝ), B^2*r^(-2:ℝ) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall h0) hm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hp : 0 < r := zero_lt_one.trans hr
      rw [Real.rpow_neg hp.le,Real.rpow_two]
      exact (hg r hr).trans_eq (by rw [div_pow,div_eq_mul_inv])
    _ = B^2 := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
      norm_num

/-- The outgoing finite positive-height cutoff costs at most O(exp(u) log² T)
in squared norm. This is the entire difference between full-line finite
Plancherel and its integral over the observation interval. -/
theorem exists_finite_cutoff_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T u : ℝ, 0 ≤ T → 0 ≤ u →
      0 ≤ 2*Real.pi*(actualComplexPairSum T u).re -
        (∫ t in (0:ℝ)..T, ‖actualSignal T u t‖^2) ∧
      2*Real.pi*(actualComplexPairSum T u).re -
        (∫ t in (0:ℝ)..T, ‖actualSignal T u t‖^2) ≤
          C * Real.exp u * (Real.log (T+3))^2 := by
  obtain ⟨K,hK,h⟩ := exists_actualSignal_outside_bound
  refine ⟨2*K^2,by positivity,fun T u hT hu => ?_⟩
  let B := K*Real.exp (u/2)*Real.log (T+3)
  let E := fun t : ℝ => ‖actualSignal T u t‖^2
  obtain ⟨hm,hp⟩ := h T u hT hu
  have hlo : (∫ t in Iic (0:ℝ), E t) ≤ B^2 := by
    have hneg : (∫ t in Iic (0:ℝ), E t) = ∫ y in Ioi (0:ℝ), E (-y) := by
      simpa only [neg_zero,neg_neg] using integral_comp_neg_Iic 0 (fun v => E (-v))
    rw [hneg,integral_Ioi_shift (fun v => E (-v)) 0 1]
    apply shifted_endpoint_energy_le _ (fun r => sq_nonneg _)
    intro r hr
    have hh := hm (-(r+(0-1))) (by linarith)
    rw [show 1 - -(r+(0-1)) = r by ring] at hh
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hhi : (∫ t in Ioi T, E t) ≤ B^2 := by
    rw [integral_Ioi_shift E T 1]
    apply shifted_endpoint_energy_le _ (fun r => sq_nonneg _)
    intro r hr
    have hh := hp (r+(T-1)) (by linarith)
    rw [show 1+(r+(T-1)-T) = r by ring] at hh
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hi : Integrable E := actualSignal_sq_integrable T u
  have hre := intervalIntegral.integral_Iic_add_Ioi
    (b := T) hi.integrableOn hi.integrableOn
  have hl := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn : IntegrableOn E (Iic (0:ℝ)))
    (hi.integrableOn : IntegrableOn E (Iic T))
  have hsplit : 2*Real.pi*(actualComplexPairSum T u).re - (∫ t in (0:ℝ)..T, E t) =
      (∫ t in Iic (0:ℝ), E t) + ∫ t in Ioi T, E t := by
    rw [← actualSignal_plancherel]
    change (∫ t : ℝ, E t) - _ = _
    linarith only [hre,hl]
  change 0 ≤ 2*Real.pi*(actualComplexPairSum T u).re - (∫ t in (0:ℝ)..T, E t) ∧ _
  rw [hsplit]
  constructor
  · exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _))
  · apply (add_le_add hlo hhi).trans_eq
    have hExp : Real.exp (u/2)^2 = Real.exp u := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    dsimp [B]
    simp only [mul_pow,hExp]; ring

open Filter
open scoped Topology

/-- At every fixed 0 ≤ α < 1, the finite signal's outgoing cutoff is
o(T log T). The full-zero replacement on the inside of the interval remains
a distinct arithmetic task. -/
theorem finite_cutoff_normalized_tendsto_zero {α : ℝ} (hα : 0 ≤ α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => (2*Real.pi*(actualComplexPairSum T (α*Real.log T)).re -
      (∫ t in (0:ℝ)..T, ‖actualSignal T (α*Real.log T) t‖^2))/(T*Real.log T)) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := exists_finite_cutoff_energy_bound
  have hlog := (isLittleO_log_rpow_atTop (by linarith : 0 < 1-α)).tendsto_div_nhds_zero
  apply squeeze_zero_norm' _ (by simpa using hlog.const_mul (4*C))
  filter_upwards [eventually_ge_atTop (3:ℝ)] with T hT
  have h1 : 1 < T := by linarith
  have ht := zero_lt_one.trans h1
  have hL := Real.log_pos h1
  obtain ⟨hn,hb⟩ := h T (α*Real.log T) ht.le (mul_nonneg hα hL.le)
  rw [Real.norm_of_nonneg (div_nonneg hn (mul_pos ht hL).le)]
  have hlo : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
  have hlu : Real.log (T+3) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T^2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (T-3)])
      _ = _ := by simp [Real.log_pow]
  have hexp : Real.exp (α*Real.log T) = T^α := by rw [Real.rpow_def_of_pos ht,mul_comm]
  rw [hexp] at hb
  have hr : T^α * T^(1-α) = T := by
    rw [← Real.rpow_add ht,show α+(1-α)=1 by ring,Real.rpow_one]
  have hp := Real.rpow_pos_of_pos ht (1-α)
  calc
    _ ≤ (C*T^α*(2*Real.log T)^2)/(T*Real.log T) := by
      apply div_le_div_of_nonneg_right _ (mul_pos ht hL).le
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo hlu 2) (by positivity))
    _ = (4*C)*(Real.log T/T^(1-α)) := by
      field_simp [ht.ne',hL.ne',hp.ne']
      have hCeq := congrArg (fun v : ℝ => 4*C*v) hr
      nlinarith only [hCeq]

end RiemannResearch.Analysis.MontgomeryFiniteResolventSignal

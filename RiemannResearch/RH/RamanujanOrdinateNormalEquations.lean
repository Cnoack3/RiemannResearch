import RiemannResearch.RH.RamanujanOrdinateRate
import RiemannResearch.RH.RamanujanNormalDefect
import RiemannResearch.RH.RamanujanSaturationCriteria
import Mathlib.Topology.Instances.Matrix

/-!
# Recovering the Pareto normal equations from actual zero ordinates

At stage `n` the conductors are `2,...,n+1`. The sample height is common to
all zero sums. Both the Gram matrix and the source use the complete Pareto
law. Every loss in this module is measured in the true arithmetic dictionary.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanOrdinateNormalEquations
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.Analysis.FiniteHilbertGram

def rawRow (p : ℕ) (T : ℝ) (q k : ℕ) : ℝ := (periodicOrdinatePacket p q T k).re

def roundedRow (p : ℕ) (T : ℝ) (q k : ℕ) : ℝ :=
  (round (rawRow p T q k) : ℝ)

def source (n : ℕ) (row : ℕ → ℕ → ℝ) (i : Fin n) : ℝ :=
  paretoMean (row (i.val + 2))

def gram (n : ℕ) (row : ℕ → ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => paretoInner (row (i.val + 2)) (row (j.val + 2))

def coefficients (n : ℕ) (row : ℕ → ℕ → ℝ) : Fin n → ℝ :=
  (gram n row)⁻¹.mulVec (source n row)

def capturedMass (n : ℕ) (row : ℕ → ℕ → ℝ) : ℝ :=
  dotProduct (source n row) (coefficients n row)

def arithmeticLoss (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  ‖hilbertOne - Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2

/-- Exact simultaneous recovery includes every entry of the inverse system. -/
theorem exists_cofinal_rounded_normal_equations :
    ∃ H : ℕ → ℝ, StrictMono H ∧ Tendsto H atTop atTop ∧
      ∀ n p T, p.Prime → H (max p (n+1)) ≤ T →
        gram n (roundedRow p T) = finitePacketGram n ∧
        source n (roundedRow p T) = (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val+2)) ∧
        coefficients n (roundedRow p T) = packetCoefficients n ∧
        capturedMass n (roundedRow p T) = packetMass n := by
  obtain ⟨H,hm,ht,h⟩ := exists_cofinal_round_periodicOrdinatePacket
  refine ⟨H,hm,ht,?_⟩
  intro n p T hp hT
  have hr (i : Fin n) : roundedRow p T (i.val+2) = ramanujanPacket (i.val+2) := by
    funext k
    exact (h (max p (n+1)) T hT p (le_max_left _ _) hp (i.val+2)
      (le_trans (by omega) (le_max_right p (n+1))) (by omega) k).1
  have hG : gram n (roundedRow p T) = finitePacketGram n := by
    ext i j
    rw [gram, hr i, hr j, finitePacketGram_apply]
  have hb : source n (roundedRow p T) = (fun i : Fin n =>
      ArithmeticFunction.vonMangoldt (i.val+2)) := by
    funext i
    rw [source, hr, paretoMean_ramanujanPacket]
  have ha : coefficients n (roundedRow p T) = packetCoefficients n := by
    rw [coefficients, hG, hb, packetCoefficients_eq_inverseGram]
  refine ⟨hG,hb,ha,?_⟩
  rw [capturedMass, ha, hb, packetCoefficients_eq_inverseGram, packetMass_eq_inverseGram]

/-- Any prime schedule and any heights above the common cutoff have the same
saturation criterion. The forward RH implication uses no converse theorem. -/
theorem exists_ordinate_mass_criterion :
    ∃ H : ℕ → ℝ, StrictMono H ∧ Tendsto H atTop atTop ∧
      ∀ (p : ℕ → ℕ) (T : ℕ → ℝ), (∀ n, (p n).Prime) →
        (∀ n, H (max (p n) (n+1)) ≤ T n) →
        (Tendsto (fun n => capturedMass n (roundedRow (p n) (T n))) atTop (𝓝 1) ↔
          limitEnergy = 0) ∧
        (Tendsto (fun n => capturedMass n (roundedRow (p n) (T n))) atTop (𝓝 1) →
          RiemannHypothesis) ∧
        ((RiemannHypothesis → BaezDuarte.NaturalApproximation) →
          (Tendsto (fun n => capturedMass n (roundedRow (p n) (T n))) atTop (𝓝 1) ↔
            RiemannHypothesis)) := by
  obtain ⟨H,hm,ht,h⟩ := exists_cofinal_rounded_normal_equations
  refine ⟨H,hm,ht,?_⟩
  intro p T hp hT
  have he : (fun n => capturedMass n (roundedRow (p n) (T n))) = packetMass :=
    funext fun n => (h n (p n) (T n) (hp n) (hT n)).2.2.2
  rw [he]
  exact ⟨packet_cofinal_mass_iff id tendsto_id, packet_riemannHypothesis_of_saturation,
    fun hBD => (packet_cofinal_rh_equivalences hBD id tendsto_id).1⟩

private theorem abs_mean_sub_le {f g : ℕ → ℝ} {B D : ℝ}
    (hg : ∀ k, |g k| ≤ B) (he : ∀ k, |f k - g k| ≤ D) :
    |paretoMean f - paretoMean g| ≤ D := by
  have hf (k : ℕ) : |f k| ≤ D + B := calc
    |f k| = |(f k - g k) + g k| := by rw [sub_add_cancel]
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (he k) (hg k))
  rw [← paretoMean_sub hf hg]
  have hs := weighted_summable_of_bounded he
  have hbound (k : ℕ) : ‖positiveWeight k * (f k - g k)‖ ≤ positiveWeight k * D := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (positiveWeight_nonneg k)]
    exact mul_le_mul_of_nonneg_left (he k) (positiveWeight_nonneg k)
  change ‖∑' k, positiveWeight k * (f k - g k)‖ ≤ D
  calc
    _ ≤ ∑' k, ‖positiveWeight k * (f k - g k)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k, positiveWeight k * D :=
      hs.norm.tsum_le_tsum hbound (positiveWeight_summable.mul_right D)
    _ = D := by rw [tsum_mul_right, positiveWeight_tsum, one_mul]

private theorem raw_row_bound {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ k,
      |rawRow p T q k - ramanujanPacket q k| ≤ C * horizontalLogRate T := by
  obtain ⟨C,hC,h⟩ := eventually_periodicOrdinatePacket_uniform hp hq
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT
  intro k
  exact (Complex.abs_re_le_norm
    (periodicOrdinatePacket p q T k - (ramanujanPacket q k : ℂ))).trans (hT.1 k)

/-- The complete empirical mark approximates von Mangoldt, also at mixed conductors. -/
theorem raw_source_error_isBigO {p : ℕ} (hp : p.Prime) (n : ℕ) (i : Fin n) :
    Asymptotics.IsBigO atTop (fun T : ℝ =>
      source n (rawRow p T) i - ArithmeticFunction.vonMangoldt (i.val+2)) horizontalLogRate := by
  obtain ⟨C,hC,h⟩ := raw_row_bound (q := i.val+2) hp (by omega)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [h] with T hT
  rw [source, ← paretoMean_ramanujanPacket, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (abs_mean_sub_le (ramanujanPacket_abs_le _) hT).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) hC.le)

/-- Every full Gram entry has the same first-order rate. -/
theorem raw_gram_error_isBigO {p : ℕ} (hp : p.Prime) (n : ℕ) (i j : Fin n) :
    Asymptotics.IsBigO atTop (fun T : ℝ =>
      gram n (rawRow p T) i j - finitePacketGram n i j) horizontalLogRate := by
  let q := i.val+2
  let s := j.val+2
  obtain ⟨A,hA,ha⟩ := raw_row_bound (q := q) hp (by dsimp [q]; omega)
  obtain ⟨C,hC,hc⟩ := raw_row_bound (q := s) hp (by dsimp [s]; omega)
  obtain ⟨B,hB⟩ : ∃ B : ℝ, ∀ k, |ramanujanPacket q k| ≤ B := ⟨_,ramanujanPacket_abs_le _⟩
  obtain ⟨D,hD⟩ : ∃ D : ℝ, ∀ k, |ramanujanPacket s k| ≤ D := ⟨_,ramanujanPacket_abs_le _⟩
  have hB0 := (abs_nonneg _).trans (hB 0)
  have hD0 := (abs_nonneg _).trans (hD 0)
  have hz : Tendsto (fun T => A * horizontalLogRate T) atTop (𝓝 0) := by
    simpa using horizontalLogRate_tendsto_zero.const_mul A
  apply Asymptotics.IsBigO.of_bound (A*D + (1+B)*C)
  filter_upwards [ha,hc,hz.eventually_le_const (by norm_num : (0:ℝ) < 1)] with T hi hj hsmall
  have hprod (k : ℕ) :
      |rawRow p T q k * rawRow p T s k - ramanujanPacket q k * ramanujanPacket s k| ≤
        (A*D+(1+B)*C)*horizontalLogRate T := by
    have hf : |rawRow p T q k| ≤ 1+B := calc
      _ = |(rawRow p T q k - ramanujanPacket q k) + ramanujanPacket q k| := by rw [sub_add_cancel]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ((hi k).trans hsmall) (hB k))
    rw [show rawRow p T q k * rawRow p T s k - ramanujanPacket q k * ramanujanPacket s k =
      (rawRow p T q k - ramanujanPacket q k) * ramanujanPacket s k +
      rawRow p T q k * (rawRow p T s k - ramanujanPacket s k) by ring]
    calc
      _ ≤ _ := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ (A*horizontalLogRate T)*D + (1+B)*(C*horizontalLogRate T) :=
        add_le_add (mul_le_mul (hi k) (hD k) (abs_nonneg _) ((abs_nonneg _).trans (hi k)))
          (mul_le_mul hf (hj k) (abs_nonneg _) (by linarith))
      _ = _ := by ring
  rw [finitePacketGram_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (abs_mean_sub_le (bounded_product hB hD) hprod).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

private theorem raw_gram_tendsto {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Tendsto (fun T => gram n (rawRow p T)) atTop (𝓝 (finitePacketGram n)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (raw_gram_error_isBigO hp n i j).trans_tendsto horizontalLogRate_tendsto_zero
  simpa only [sub_add_cancel, zero_add] using h.add_const (finitePacketGram n i j)

private theorem raw_source_tendsto {p : ℕ} (hp : p.Prime) (n : ℕ) (i : Fin n) :
    Tendsto (fun T => source n (rawRow p T) i) atTop
      (𝓝 (ArithmeticFunction.vonMangoldt (i.val+2))) := by
  have h := (raw_source_error_isBigO hp n i).trans_tendsto horizontalLogRate_tendsto_zero
  simpa only [sub_add_cancel, zero_add] using h.add_const (ArithmeticFunction.vonMangoldt (i.val+2))

theorem eventually_raw_gram_det_pos {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop, 0 < (gram n (rawRow p T)).det := by
  have hdet : Tendsto (fun T => (gram n (rawRow p T)).det) atTop (𝓝 (finitePacketGram n).det) :=
    (continuous_id.matrix_det.continuousAt.tendsto).comp (raw_gram_tendsto hp n)
  exact hdet.eventually_const_lt (gramMatrix_det_pos (finitePacket_independent n))

theorem raw_coefficients_tendsto {p : ℕ} (hp : p.Prime) (n : ℕ) (i : Fin n) :
    Tendsto (fun T => coefficients n (rawRow p T) i) atTop (𝓝 (packetCoefficients n i)) := by
  have hG := raw_gram_tendsto hp n
  have hdet : Tendsto (fun T => (gram n (rawRow p T)).det) atTop (𝓝 (finitePacketGram n).det) :=
    (continuous_id.matrix_det.continuousAt.tendsto).comp hG
  have hadj : Tendsto (fun T => (gram n (rawRow p T)).adjugate) atTop
      (𝓝 (finitePacketGram n).adjugate) :=
    (continuous_id.matrix_adjugate.continuousAt.tendsto).comp hG
  have hinv (j : Fin n) : Tendsto (fun T => (gram n (rawRow p T))⁻¹ i j) atTop
      (𝓝 ((finitePacketGram n)⁻¹ i j)) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact (hdet.inv₀ (ne_of_gt (gramMatrix_det_pos (finitePacket_independent n)))).mul
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hadj i) j)
  rw [packetCoefficients_eq_inverseGram]
  unfold coefficients Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ fun j _ => (hinv j).mul (raw_source_tendsto hp n j)

/-- The two errors driving the actual normal defect are the empirical mark
error and the signed Gram perturbation applied to the fitted coefficients. -/
theorem eventually_raw_normal_defect {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ i : Fin n,
      RamanujanNormalDefect.paretoDefect n (coefficients n (rawRow p T)) i =
        (source n (rawRow p T) i - ArithmeticFunction.vonMangoldt (i.val+2)) -
        ∑ j, (gram n (rawRow p T) i j - finitePacketGram n i j) *
          coefficients n (rawRow p T) j := by
  filter_upwards [eventually_raw_gram_det_pos hp n] with T hpos
  have he : (gram n (rawRow p T)).mulVec (coefficients n (rawRow p T)) =
      source n (rawRow p T) := by
    rw [coefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hpos.ne'),
      Matrix.one_mulVec]
  intro i
  have hi := congrFun he i
  change (∑ j, gram n (rawRow p T) i j * coefficients n (rawRow p T) j) = _ at hi
  rw [RamanujanNormalDefect.paretoDefect_arithmetic]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hi]
  ring

theorem raw_normal_defect_isBigO {p : ℕ} (hp : p.Prime) (n : ℕ) (i : Fin n) :
    Asymptotics.IsBigO atTop (fun T : ℝ =>
      RamanujanNormalDefect.paretoDefect n (coefficients n (rawRow p T)) i) horizontalLogRate := by
  have hs : Asymptotics.IsBigO atTop (fun T : ℝ =>
      ∑ j, (gram n (rawRow p T) i j - finitePacketGram n i j) *
        coefficients n (rawRow p T) j) horizontalLogRate := by
    apply Asymptotics.IsBigO.sum
    intro j _
    simpa only [mul_one] using (raw_gram_error_isBigO hp n i j).mul
      ((raw_coefficients_tendsto hp n j).isBigO_one ℝ)
  apply ((raw_source_error_isBigO hp n i).sub hs).congr' _ Filter.EventuallyEq.rfl
  exact (eventually_raw_normal_defect hp n).mono fun _ h => (h i).symm

/-- Exact quadratic excess in the true Pareto problem for any sample height.
The inverse here is the complete arithmetic Gram inverse. -/
theorem arithmeticLoss_sub_optimum (n : ℕ) (a : Fin n → ℝ) :
    arithmeticLoss n a - (1 - packetMass n) =
      dotProduct (RamanujanNormalDefect.paretoDefect n a)
        ((finitePacketGram n)⁻¹.mulVec (RamanujanNormalDefect.paretoDefect n a)) := by
  have h := RamanujanNormalDefect.pareto_trial_error n a
  rw [arithmeticLoss, h, add_sub_cancel_left]
  exact defectEnergy_inverseGram (finitePacket_independent n) hilbertOne a

/-- Fixed-stage excess squared loss is second order even when both the matrix
and the right-hand side are fitted from unrounded, actual zero ordinates. -/
theorem raw_excess_loss_isBigO_sq {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Asymptotics.IsBigO atTop (fun T : ℝ =>
      arithmeticLoss n (coefficients n (rawRow p T)) - (1 - packetMass n))
      (fun T => horizontalLogRate T ^ 2) := by
  simp only [arithmeticLoss_sub_optimum, Matrix.mulVec, dotProduct]
  apply Asymptotics.IsBigO.sum
  intro i _
  have hi : Asymptotics.IsBigO atTop (fun T : ℝ =>
      ∑ j : Fin n, (finitePacketGram n)⁻¹ i j *
        RamanujanNormalDefect.paretoDefect n (coefficients n (rawRow p T)) j)
      horizontalLogRate := by
    apply Asymptotics.IsBigO.sum
    intro j _
    exact (raw_normal_defect_isBigO hp n j).const_mul_left _
  simpa only [pow_two] using (raw_normal_defect_isBigO hp n i).mul hi

private theorem excess_nonneg (n : ℕ) (a : Fin n → ℝ) :
    0 ≤ arithmeticLoss n a - (1 - packetMass n) := by
  rw [arithmeticLoss, packet_completion, add_sub_cancel_left]
  exact sq_nonneg _

/-- A single growing height schedule attains any prescribed positive accuracy
at every cutoff. Its true losses converge to the infinite Pareto residual. -/
theorem exists_cofinal_raw_loss (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ H : ℕ → ℝ, Tendsto H atTop atTop ∧
      ∀ T : ℕ → ℝ, (∀ n, H n ≤ T n) →
        (∀ n, 0 ≤ arithmeticLoss n (coefficients n (rawRow (p n) (T n))) - (1-packetMass n) ∧
          arithmeticLoss n (coefficients n (rawRow (p n) (T n))) - (1-packetMass n) ≤ ε n) ∧
        Tendsto (fun n => arithmeticLoss n (coefficients n (rawRow (p n) (T n)))) atTop
          (𝓝 limitEnergy) := by
  have hrate : Tendsto (fun T => horizontalLogRate T ^ 2) atTop (𝓝 0) := by
    simpa using horizontalLogRate_tendsto_zero.pow 2
  have hsmall (n : ℕ) : ∀ᶠ T : ℝ in atTop,
      arithmeticLoss n (coefficients n (rawRow (p n) T)) - (1-packetMass n) ≤ ε n :=
    ((raw_excess_loss_isBigO_sq (hp n) n).trans_tendsto hrate).eventually_le_const (hε n)
  choose b hb using fun n => eventually_atTop.mp (hsmall n)
  refine ⟨fun n => max (n:ℝ) (b n),
    tendsto_atTop_mono (fun n => le_max_left (n:ℝ) (b n)) tendsto_natCast_atTop_atTop,?_⟩
  intro T hT
  have he (n : ℕ) := hb n (T n) ((le_max_right _ _).trans (hT n))
  refine ⟨fun n => ⟨excess_nonneg n _, he n⟩,?_⟩
  have hz : Tendsto (fun n => arithmeticLoss n (coefficients n (rawRow (p n) (T n))) -
      (1-packetMass n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => excess_nonneg n _) he hε0
  have hlim : Tendsto (fun n => 1 - packetMass n) atTop (𝓝 limitEnergy) := by
    exact (show energy = (fun n => 1-packetMass n) from funext packet_energy_eq_original) ▸
      energy_tendsto
  simpa only [sub_add_cancel, zero_add] using hz.add hlim

/-- A height witness uses only raw normal equations and true Pareto loss. -/
def VanishingOrdinateLoss (p : ℕ → ℕ) : Prop :=
  ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
    Tendsto (fun n => arithmeticLoss n (coefficients n (rawRow (p n) (T n)))) atTop (𝓝 0)

theorem vanishingOrdinateLoss_iff (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) :
    VanishingOrdinateLoss p ↔ limitEnergy = 0 := by
  constructor
  · rintro ⟨T,_,hT⟩
    have hz : Tendsto (fun n => 1-packetMass n) atTop (𝓝 0) :=
      squeeze_zero (fun n => (sub_pos.mpr (packetMass_bounds n).2).le)
        (fun n => sub_nonneg.mp (excess_nonneg n _)) hT
    have hlim : Tendsto (fun n => 1-packetMass n) atTop (𝓝 limitEnergy) := by
      exact (show energy = (fun n => 1-packetMass n) from funext packet_energy_eq_original) ▸
      energy_tendsto
    exact tendsto_nhds_unique hlim hz
  · intro he
    obtain ⟨H,ht,h⟩ := exists_cofinal_raw_loss p hp (fun n => 1 / ((n:ℝ)+1))
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨H,ht,by simpa only [he] using (h H (fun _ => le_rfl)).2⟩

theorem riemannHypothesis_of_vanishingOrdinateLoss (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime)
    (h : VanishingOrdinateLoss p) : RiemannHypothesis :=
  packet_riemannHypothesis_of_saturation
    ((packet_cofinal_mass_iff id tendsto_id).mpr ((vanishingOrdinateLoss_iff p hp).mp h))

theorem vanishingOrdinateLoss_iff_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime) :
    VanishingOrdinateLoss p ↔ RiemannHypothesis :=
  (vanishingOrdinateLoss_iff p hp).trans ((packet_cofinal_mass_iff id tendsto_id).symm.trans
    (packet_cofinal_rh_equivalences hBD id tendsto_id).1)

/-- Raw ordinate mass converges without rounding the source or the matrix. -/
theorem raw_mass_tendsto {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Tendsto (fun T => capturedMass n (rawRow p T)) atTop (𝓝 (packetMass n)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ =>
    (raw_source_tendsto hp n i).mul (raw_coefficients_tendsto hp n i))
  simpa only [capturedMass, dotProduct, packetMass, mul_comm] using h

/-- Each finite centered determinant retains the entire complementary mass. -/
def centeredGram (n : ℕ) (row : ℕ → ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gram n row - Matrix.vecMulVec (source n row) (source n row)

theorem centered_det (n : ℕ) (row : ℕ → ℕ → ℝ) (hG : IsUnit (gram n row).det) :
    (centeredGram n row).det = (gram n row).det * (1 - capturedMass n row) := by
  have h : centeredGram n row =
      gram n row + Matrix.vecMulVec (-source n row) (source n row) := by
    ext i j
    simp [centeredGram, Matrix.vecMulVec, sub_eq_add_neg]
  rw [h, Matrix.det_add_outer _ hG, Matrix.mulVec_neg]
  simp [capturedMass, coefficients, dotProduct, sub_eq_add_neg]

theorem raw_centered_det_ratio_tendsto {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Tendsto (fun T => (centeredGram n (rawRow p T)).det / (gram n (rawRow p T)).det)
      atTop (𝓝 (1-packetMass n)) := by
  have h : Tendsto (fun T => 1-capturedMass n (rawRow p T)) atTop (𝓝 (1-packetMass n)) :=
    tendsto_const_nhds.sub (raw_mass_tendsto hp n)
  apply h.congr'
  filter_upwards [eventually_raw_gram_det_pos hp n] with T ht
  rw [centered_det _ _ (isUnit_iff_ne_zero.mpr ht.ne')]
  field_simp [ht.ne']

/-- Only the zero-ordinate data and the known Pareto weights occur in this
test. For each tolerance one fixed conductor cutoff works at arbitrarily
large heights. -/
def RawMassSaturation (p : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ᶠ T : ℝ in atTop, 1-ε < capturedMass n (rawRow p T)

theorem rawMassSaturation_iff {p : ℕ} (hp : p.Prime) :
    RawMassSaturation p ↔ limitEnergy = 0 := by
  have hup (n : ℕ) : packetMass n ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto
      ((eventually_ge_atTop n).mono (fun _ h => packetMass_monotone h))
  have hnonneg : 0 ≤ limitEnergy := by
    exact sq_nonneg _
  constructor
  · intro hs
    by_contra hne
    have hpos : 0 < limitEnergy := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n,hn⟩ := hs (limitEnergy/2) (by positivity)
    have hlo : 1-limitEnergy/2 ≤ packetMass n := by
      by_contra! hlt
      exact hn (((raw_mass_tendsto hp n).eventually_lt_const hlt).mono
        (fun _ h => not_lt_of_ge h.le))
    linarith [hup n]
  · intro he ε hε
    have hm := (packet_cofinal_mass_iff id tendsto_id).mpr he
    obtain ⟨n,hn⟩ := (hm.eventually_const_lt (by linarith : 1-ε < 1)).exists
    exact ⟨n,((raw_mass_tendsto hp n).eventually_const_lt hn).frequently⟩

theorem riemannHypothesis_of_rawMassSaturation {p : ℕ} (hp : p.Prime)
    (h : RawMassSaturation p) : RiemannHypothesis :=
  packet_riemannHypothesis_of_saturation
    ((packet_cofinal_mass_iff id tendsto_id).mpr ((rawMassSaturation_iff hp).mp h))

theorem rawMassSaturation_iff_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) {p : ℕ} (hp : p.Prime) :
    RawMassSaturation p ↔ RiemannHypothesis :=
  (rawMassSaturation_iff hp).trans ((packet_cofinal_mass_iff id tendsto_id).symm.trans
    (packet_cofinal_rh_equivalences hBD id tendsto_id).1)

end RiemannResearch.RH.RamanujanOrdinateNormalEquations

/--
info: 'RiemannResearch.RH.RamanujanOrdinateNormalEquations.exists_ordinate_mass_criterion' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.RamanujanOrdinateNormalEquations.exists_ordinate_mass_criterion

/--
info: 'RiemannResearch.RH.RamanujanOrdinateNormalEquations.raw_excess_loss_isBigO_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.RamanujanOrdinateNormalEquations.raw_excess_loss_isBigO_sq

/--
info: 'RiemannResearch.RH.RamanujanOrdinateNormalEquations.exists_cofinal_raw_loss' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.RamanujanOrdinateNormalEquations.exists_cofinal_raw_loss

/--
info: 'RiemannResearch.RH.RamanujanOrdinateNormalEquations.vanishingOrdinateLoss_iff_riemannHypothesis' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.RamanujanOrdinateNormalEquations.vanishingOrdinateLoss_iff_riemannHypothesis

/--
info: 'RiemannResearch.RH.RamanujanOrdinateNormalEquations.riemannHypothesis_of_rawMassSaturation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.RamanujanOrdinateNormalEquations.riemannHypothesis_of_rawMassSaturation

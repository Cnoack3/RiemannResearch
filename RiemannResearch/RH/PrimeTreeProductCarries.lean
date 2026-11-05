import RiemannResearch.RH.PrimeTreeHaarCarryMean
import RiemannResearch.RH.PrimeTreeUniformCarry
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.Linarith

/-! # The infinite carry on the full product of prime residue grids

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§§3.1–3.2. Every finite floor is a locally constant cylinder. Finite CRT
representatives approximate each input in the product topology, extending
the physical uniform remainder to every product input. Any probability
law on the inputs inherits the estimate at every Lebesgue exponent. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic ArithmeticCumulative

def gridDiagonal (n : ℕ) : PrimeGrid := fun i => ⟨n % primeAt i, Nat.mod_lt _ (primeAt_prime i).pos⟩

private def representative (ω : PrimeGrid) (K : ℕ) :
    {n : ℕ // ∀ i ∈ Finset.range K, n ≡ (ω i).val [MOD primeAt i]} :=
  Nat.chineseRemainderOfFinset (fun i => (ω i).val) primeAt (Finset.range K)
    (fun i _ => (primeAt_prime i).ne_zero) (by
      intro i _ m _ him
      exact (Nat.coprime_primes (primeAt_prime i) (primeAt_prime m)).mpr
        ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.ne him))

private theorem representatives_tendsto (ω : PrimeGrid) :
    Tendsto (fun K => gridDiagonal (representative ω K).val) atTop (𝓝 ω) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with K hK
  apply Fin.ext
  symm
  have h := (representative ω K).property i (Finset.mem_range.mpr hK)
  simpa only [gridDiagonal, Nat.ModEq, Nat.mod_eq_of_lt (ω i).isLt] using h

theorem gridDiagonal_dense : DenseRange gridDiagonal := fun ω =>
  mem_closure_of_tendsto (representatives_tendsto ω)
    (Eventually.of_forall fun _ => Set.mem_range_self _)

private def gridRatio (k : ℕ) (ω : PrimeGrid) : ℝ := rawDigit k ω / (primeAt k : ℝ)

/-- Composite normalized residue computed from the prime-coordinate input. -/
def gridHead (j : ℕ) : ℕ → PrimeGrid → ℝ
  | 0, ω => gridRatio 0 ω
  | k+1, ω => Int.fract (((oddChain j).a k : ℝ) * gridHead j k ω +
      ((oddChain j).b k : ℝ) * gridRatio (k+1) ω)

/-- The weighted integer floor on a single edge of the product chain. -/
def gridFloor (j k : ℕ) (ω : PrimeGrid) : ℝ :=
  (oddChain j).w (k+1) * (⌊((oddChain j).a k : ℝ) * gridHead j k ω +
    ((oddChain j).b k : ℝ) * gridRatio (k+1) ω⌋ : ℤ)

def gridPartial (j K : ℕ) (ω : PrimeGrid) : ℝ :=
  ∑ k ∈ Finset.range K, gridFloor j k ω

private theorem gridRatio_local (k : ℕ) : IsLocallyConstant (gridRatio k) :=
  (IsLocallyConstant.of_discrete (fun x : Fin (primeAt k) => (x.val : ℝ) / primeAt k)).comp_continuous
    (continuous_apply k)

private theorem gridHead_local (j k : ℕ) : IsLocallyConstant (gridHead j k) := by
  induction k with
  | zero => exact gridRatio_local 0
  | succ k ih =>
    exact ih.comp₂ (gridRatio_local (k+1))
      (fun x y => Int.fract (((oddChain j).a k : ℝ)*x + ((oddChain j).b k : ℝ)*y))

private theorem gridFloor_local (j k : ℕ) : IsLocallyConstant (gridFloor j k) :=
  (gridHead_local j k).comp₂ (gridRatio_local (k+1)) (fun x y =>
    (oddChain j).w (k+1) * (⌊((oddChain j).a k : ℝ)*x + ((oddChain j).b k : ℝ)*y⌋ : ℤ))

private theorem gridPartial_continuous (j K : ℕ) : Continuous (gridPartial j K) :=
  by
    change Continuous (fun ω => ∑ k ∈ Finset.range K, gridFloor j k ω)
    induction K with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact continuous_const
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add (gridFloor_local j k).continuous

private theorem gridHead_diagonal (j k n : ℕ) :
    gridHead j k (gridDiagonal n) = residueFraction ((oddChain j).D k) n := by
  let t := oddChain j
  induction k with
  | zero =>
    simp [gridHead, gridRatio, rawDigit, gridDiagonal, oddChain, firstChain, primorialAt,
      primeAt, residueFraction]
  | succ k ih =>
    have hD := (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (t.modulus_growth k)
    have hp : 0 < t.p k := lt_of_lt_of_le (by decide : 0 < 2) (t.radix_ge k)
    have h := real_decomposition (t.D k) (t.p k) (t.a k) (t.b k) 0 n hD hp
      (by simpa using t.bezout k)
    rw [gridHead, ih]
    change Int.fract ((t.a k : ℝ) * residueFraction (t.D k) n +
      (t.b k : ℝ) * residueFraction (t.p k) n) = residueFraction (t.D (k+1)) n
    rw [t.next, Int.fract]
    unfold carry at h
    linarith

theorem gridFloor_diagonal (j k n : ℕ) :
    gridFloor j k (gridDiagonal n) = (oddChain j).carryTerm n k := by
  rw [gridFloor, gridHead_diagonal]
  rfl

private theorem signal_continuous (j : ℕ) : Continuous (haarCarryReadout j) := by
  have hd (i : ℕ) : Continuous (rawDigit i) :=
    (continuous_of_discreteTopology (f := fun x : Fin (primeAt i) => (x.val : ℝ))).comp
      (continuous_apply i)
  have hs : Continuous (fun ω : PrimeGrid => ∑' k, (oddChain j).edgeMass k * rawDigit (k+1) ω) :=
    continuous_tsum (fun k => continuous_const.mul (hd (k+1))) (oddChain_firstMoment j) (by
      intro k ω
      rw [norm_mul, Real.norm_of_nonneg ((oddChain_probability j).2 k).le]
      exact mul_le_mul_of_nonneg_left (rawDigit_norm (k+1) ω) ((oddChain_probability j).2 k).le)
  exact ((hd 0).sub hs).div_const _

/-- The same sharp uniform remainder holds simultaneously at all prime-grid inputs. -/
theorem grid_uniform_remainder (j K : ℕ) (hK : 0 < K) (ω : PrimeGrid) :
    |haarCarryReadout j ω - gridPartial j K ω| ≤ 3 * (oddChain j).w K := by
  have hc := ((signal_continuous j).sub (gridPartial_continuous j K)).abs
  apply le_of_tendsto (hc.continuousAt.tendsto.comp (representatives_tendsto ω))
  apply Eventually.of_forall
  intro N
  let n := (representative ω N).val
  change |haarCarryReadout j (gridDiagonal n) - gridPartial j K (gridDiagonal n)| ≤ _
  rw [show haarCarryReadout j (gridDiagonal n) = ∑' k, (oddChain j).carryTerm n k from
    haarCarryReadout_diagonal j n, gridPartial]
  simp only [gridFloor_diagonal]
  exact (oddChain j).carry_uniform_remainder (fun k => (oddWeight_pos j k).le)
    (oddWeight_step j) (oddChain_inverse j) radix_le_prefix K hK n

private theorem grid_weights_summable (j : ℕ) : Summable (oddChain j).w := by
  let t := oddChain j
  have hw (k : ℕ) : 0 ≤ t.w k := (oddWeight_pos j k).le
  have hg := summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_norm_bounded (hg.mul_left (t.w 1))
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (hw _)]
  exact t.futureWeight_bound hw (oddChain_inverse j) 1 (by decide) k

private theorem grid_weight_tends (j : ℕ) :
    Tendsto (fun K => 3 * (oddChain j).w K) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds (x := (3 : ℝ))).mul (grid_weights_summable j).tendsto_atTop_zero

/-- A summable numerical majorant for the absolute values of all product
floors, uniform in the entire input. -/
theorem grid_floor_normal_convergence (j : ℕ) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ k ω, ‖gridFloor j k ω‖ ≤ B k := by
  let t := oddChain j
  have hw (k : ℕ) : 0 ≤ t.w k := (oddWeight_pos j k).le
  have hwS := grid_weights_summable j
  have hpS : Summable (fun k => |t.w (k+1) * (t.b k : ℝ)|) :=
    (summable_nat_add_iff 1).mp
      (t.primeWeight_tail hw (oddWeight_step j) (oddChain_inverse j) radix_le_prefix 1 (by decide)).1
  refine ⟨fun k => t.w k + |t.w (k+1) * (t.b k : ℝ)| + t.w (k+1),
    (hwS.add hpS).add ((summable_nat_add_iff 1).mpr hwS), ?_⟩
  intro k ω
  apply le_of_tendsto ((gridFloor_local j k).continuous.norm.continuousAt.tendsto.comp
    (representatives_tendsto ω))
  apply Eventually.of_forall
  intro N
  let n := (representative ω N).val
  change ‖gridFloor j k (gridDiagonal n)‖ ≤ _
  rw [gridFloor_diagonal, Real.norm_eq_abs, t.carry_step]
  have ha (l : ℕ) : |t.parentTerm n l| ≤ t.w l := by
    rw [NormalizedCarryChain.parentTerm, abs_mul, abs_of_nonneg (hw _)]
    exact mul_le_of_le_one_right (hw _) (residueFraction_abs_le_one _ _)
  have hb : |t.primeTerm n k| ≤ |t.w (k+1) * (t.b k : ℝ)| := by
    rw [NormalizedCarryChain.primeTerm, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (residueFraction_abs_le_one _ _)
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (ha k) hb)) (ha (k+1)))

theorem grid_uniform (j : ℕ) : TendstoUniformly (gridPartial j) (haarCarryReadout j) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(grid_weight_tends j).eventually_lt_const hε, eventually_gt_atTop 0] with K hK hK0 ω
  rw [Real.dist_eq]
  exact (grid_uniform_remainder j K hK0 ω).trans_lt hK

/-- Uniformity gives all Lq estimates, including infinity. A measurable input
can be the Haar grid itself or the diagonal physical integer. -/
theorem grid_eLpNorm_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : X → PrimeGrid) (_hξ : Measurable ξ) (q : ℝ≥0∞) (j K : ℕ) (hK : 0 < K) :
    eLpNorm (fun x => haarCarryReadout j (ξ x) - gridPartial j K (ξ x)) q μ ≤
      ENNReal.ofReal (3 * (oddChain j).w K) := by
  have hb : ∀ᵐ x ∂μ, ‖haarCarryReadout j (ξ x) - gridPartial j K (ξ x)‖ ≤
      3 * (oddChain j).w K :=
    Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using grid_uniform_remainder j K hK (ξ x)
  simpa using eLpNorm_le_of_ae_bound (p := q) hb

theorem grid_eLpNorm_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : X → PrimeGrid) (hξ : Measurable ξ) (q : ℝ≥0∞) (j : ℕ) :
    Tendsto (fun K => eLpNorm (fun x => haarCarryReadout j (ξ x) - gridPartial j K (ξ x)) q μ)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun K => ENNReal.ofReal (3 * (oddChain j).w K)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (grid_weight_tends j)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_gt_atTop 0] with K hK
  exact grid_eLpNorm_bound μ ξ hξ q j K hK

theorem haar_eLpNorm_tendsto (q : ℝ≥0∞) (j : ℕ) :
    Tendsto (fun K => eLpNorm (fun ω => haarCarryReadout j ω - gridPartial j K ω) q primeGridHaar)
      atTop (𝓝 0) :=
  grid_eLpNorm_tendsto primeGridHaar id measurable_id q j

theorem physical_eLpNorm_tendsto (μ : Measure ℕ) [IsProbabilityMeasure μ] (q : ℝ≥0∞) (j : ℕ) :
    Tendsto (fun K => eLpNorm (fun n => (∑' k, (oddChain j).carryTerm n k) -
      ∑ k ∈ Finset.range K, (oddChain j).carryTerm n k) q μ) atTop (𝓝 0) := by
  have hd (n : ℕ) : haarCarryReadout j (gridDiagonal n) = ∑' k, (oddChain j).carryTerm n k :=
    haarCarryReadout_diagonal j n
  simpa only [hd, gridPartial, gridFloor_diagonal] using
    grid_eLpNorm_tendsto μ gridDiagonal (measurable_of_countable _) q j

end RiemannResearch.RH.CanonicalPrimeCarry

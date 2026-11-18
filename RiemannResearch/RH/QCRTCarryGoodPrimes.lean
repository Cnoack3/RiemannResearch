import RiemannResearch.Analysis.LogarithmicWeights
import RiemannResearch.RH.QCRTCarrySourceBudget
import RiemannResearch.RH.QFirstCarrySchur
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Prime sets certifying the one-divisor carry estimate

The stages in `QCRTCarrySourceBudget` first treat 5. We include the separately
computed period-six block at 3 and use actual prime numbers as indices.
Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
the Riemann hypothesis*, Remark 8, DOI 10.1007/BF02829783, supplies the
squarefree closure criterion behind the imported implication. The variable
threshold uses the Abel–Dini logarithmic comparison (Knopp, §39, Thm. 173).
The divergence of the reciprocal sum of the accepted primes is open.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCarryGoodPrimes

open QCRTCarrySourceBudget QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.LogarithmicWeights

/-- Maximum one-divisor score at the actual incoming prime. At 3 there is
only the old divisor 2, computed from the complete period-six Gram. -/
def primeScore (p : ℕ) : ℝ :=
  if p = 3 then (QFirstCarrySchur.eta ^ 2 / QFirstCarrySchur.omega) /
    QFirstCarrySchur.baseError ^ 2
  else if 4 ≤ p then bestBudget (p - 4) else 0

@[simp] theorem primeScore_add_four (n : ℕ) : primeScore (n + 4) = bestBudget n := by
  simp [primeScore, show n + 4 ≠ 3 by omega, show 4 ≤ n + 4 by omega]

theorem primeScore_nonneg (p : ℕ) : 0 ≤ primeScore p := by
  unfold primeScore
  split
  · exact div_nonneg (by linarith [QFirstCarrySchur.gain_bounds.1]) (sq_nonneg _)
  · split
    · exact bestBudget_nonneg _
    · exact le_rfl

theorem primeScore_three_bounds : 2.950256 ≤ primeScore 3 ∧ primeScore 3 ≤ 2.950261 := by
  have h := QFirstCarrySchur.base_error_bounds
  have he : 0 < QFirstCarrySchur.baseError := by linarith [h.1]
  have lo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.068685281) h.1 2
  have hi := pow_le_pow_left₀ he.le h.2 2
  rw [show primeScore 3 = (QFirstCarrySchur.eta ^ 2 / QFirstCarrySchur.omega) /
    QFirstCarrySchur.baseError ^ 2 from rfl]
  constructor
  · rw [le_div_iff₀ (sq_pos_of_pos he)]
    nlinarith only [hi, QFirstCarrySchur.gain_bounds.1]
  · rw [div_le_iff₀ (sq_pos_of_pos he)]
    nlinarith only [lo, QFirstCarrySchur.gain_bounds.2]

/-- Under failure of RH the total best one-divisor score on actual primes is finite. -/
theorem summable_primeScore_of_not_RH (hn : ¬ RiemannHypothesis) : Summable primeScore := by
  apply (summable_nat_add_iff 4).mp
  simp only [primeScore_add_four]
  apply (summable_iff_not_tendsto_nat_atTop_of_nonneg bestBudget_nonneg).mpr
  exact fun h => hn (riemannHypothesis_of_best_singletons h)

/-- A positive threshold on the maximum really is witnessed by a single old divisor. -/
theorem le_bestBudget_iff_exists_divisor (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ≤ bestBudget n ↔ ∃ d : DivisorIndex n, x ≤ selectedBudget n {d} := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := bestBudget_attained n
    have hne : s.Nonempty := by
      by_contra hn
      have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst s
      have he : selectedBudget n ∅ = 0 := by simp [selectedBudget, sourceMass, blockTrace]
      linarith
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp
      (Nat.le_antisymm hcard (Finset.card_pos.mpr hne))
    refine ⟨d, ?_⟩
    simpa only [hd] using h.trans_eq hs.symm
  · rintro ⟨d, hd⟩
    exact hd.trans (singleton_le_best n d)

/-- Reciprocal mass at a member of a set of natural numbers, zero elsewhere. -/
def reciprocalOn (A : Set ℕ) : ℕ → ℝ := A.indicator (fun p : ℕ => 1 / (p : ℝ))

@[simp] theorem reciprocalOn_mem {A : Set ℕ} {p : ℕ} (hp : p ∈ A) :
    reciprocalOn A p = 1 / (p : ℝ) := Set.indicator_of_mem hp _

@[simp] theorem reciprocalOn_notMem {A : Set ℕ} {p : ℕ} (hp : p ∉ A) :
    reciprocalOn A p = 0 := Set.indicator_of_notMem hp _

theorem reciprocalOn_nonneg (A : Set ℕ) (p : ℕ) : 0 ≤ reciprocalOn A p := by
  by_cases hp : p ∈ A
  · rw [reciprocalOn_mem hp]
    positivity
  · rw [reciprocalOn_notMem hp]

/-- The canonical fixed-threshold set, with the physical stage at 3 included. -/
def goodPrimes (c : ℝ) : Set ℕ :=
  {p | p.Prime ∧ 3 ≤ p ∧ c / (p : ℝ) ≤ primeScore p}

theorem mem_goodPrimes_iff_divisor (n : ℕ) {c : ℝ} (hc : 0 < c) :
    n + 4 ∈ goodPrimes c ↔ (n + 4).Prime ∧
      ∃ d : DivisorIndex n, c / ((n + 4 : ℕ) : ℝ) ≤ selectedBudget n {d} := by
  change ((n + 4).Prime ∧ 3 ≤ n + 4 ∧ _) ↔ _
  simp only [show 3 ≤ n + 4 by omega, true_and, primeScore_add_four]
  rw [le_bestBudget_iff_exists_divisor n (div_pos hc (by positivity))]

theorem three_mem_goodPrimes_one : 3 ∈ goodPrimes 1 := by
  refine ⟨by decide, by decide, ?_⟩
  linarith [primeScore_three_bounds.1]

private theorem rh_of_weight_le_with_loss {w loss : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hd : ¬ Summable w) (hl : Summable loss) {c : ℝ} (hc : 0 < c)
    (h : ∀ p, c * w p ≤ primeScore p + loss p) : RiemannHypothesis := by
  by_contra hn
  have hb := ((summable_primeScore_of_not_RH hn).add hl).mul_left c⁻¹
  apply hd (Summable.of_nonneg_of_le hw _ hb)
  intro p
  calc
    w p = c⁻¹ * (c * w p) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (h p) (inv_nonneg.mpr hc.le)

theorem riemannHypothesis_of_goodPrimes {c : ℝ} (hc : 0 < c)
    (hd : ¬ Summable (reciprocalOn (goodPrimes c))) : RiemannHypothesis := by
  apply rh_of_weight_le_with_loss (reciprocalOn_nonneg _) hd
    (loss := fun _ => 0) (by simp) hc
  intro p
  by_cases hp : p ∈ goodPrimes c
  · simpa [reciprocalOn_mem hp, div_eq_mul_inv] using hp.2.2
  · simp [reciprocalOn_notMem hp, primeScore_nonneg]

/-- An independent prime set and a finite number of logarithmic weakenings
are allowed. The total score shortfall may be summable. -/
theorem riemannHypothesis_of_iteratedLogFloor (A : Set ℕ) (k : ℕ) {c : ℝ}
    (hc : 0 < c) (hd : ¬ Summable (reciprocalOn A)) {loss : ℕ → ℝ} (hl : Summable loss)
    (h : ∀ p, c * iteratedLogWeight k (reciprocalOn A) p ≤ primeScore p + loss p) :
    RiemannHypothesis :=
  rh_of_weight_le_with_loss (iteratedLogWeight_nonneg (reciprocalOn_nonneg A) k)
    (not_summable_iteratedLogWeight (reciprocalOn_nonneg A) hd k) hl hc h

/-- Euler's theorem discharges the divergence hypothesis for every finite
logarithmic iteration on the set of all primes. -/
theorem not_summable_iterated_prime_reciprocals (k : ℕ) :
    ¬ Summable (iteratedLogWeight k (reciprocalOn {p : ℕ | p.Prime})) :=
  not_summable_iteratedLogWeight (reciprocalOn_nonneg _) not_summable_one_div_on_primes k

/-- On all sufficiently large primes it suffices to pay the first shrinking
floor. Euler supplies the divergent mass and the finite prefix is absorbed. -/
theorem riemannHypothesis_of_eventual_prime_log_floor {c : ℝ} (hc : 0 < c) (N : ℕ)
    (h : ∀ p : ℕ, N ≤ p → p.Prime →
      c * ((1 / (p : ℝ)) / (1 + prefixMass (reciprocalOn {q : ℕ | q.Prime}) p)) ≤
        primeScore p) : RiemannHypothesis := by
  let primes : Set ℕ := {p : ℕ | p.Prime}
  let w := reciprocalOn primes
  let loss := fun p => if p < N then c * logWeight w p else 0
  have hl : Summable loss := by
    apply (summable_nat_add_iff N).mp
    have hz : (fun p => loss (p + N)) = fun _ : ℕ => (0 : ℝ) := by
      funext p
      simp [loss, show ¬ p + N < N by omega]
    rw [hz]
    exact summable_zero
  apply riemannHypothesis_of_iteratedLogFloor primes 1 hc not_summable_one_div_on_primes hl
  intro p
  change c * logWeight w p ≤ primeScore p + loss p
  by_cases hN : p < N
  · rw [show loss p = c * logWeight w p from if_pos hN]
    linarith [primeScore_nonneg p]
  · rw [show loss p = 0 from if_neg hN, add_zero]
    refine (mul_le_mul_of_nonneg_left (logWeight_le (reciprocalOn_nonneg primes) p) hc.le).trans ?_
    by_cases hp : p ∈ primes
    · rw [reciprocalOn_mem hp]
      exact h p (by omega) hp
    · rw [reciprocalOn_notMem hp, zero_div, mul_zero]
      exact primeScore_nonneg p

/-- Admission when the reciprocal mass of earlier accepted primes is `mass`. -/
def admits (c : ℝ) (p : ℕ) (mass : ℝ) : Prop :=
  p.Prime ∧ 3 ≤ p ∧ c * ((1 / (p : ℝ)) / (1 + mass)) ≤ primeScore p

/-- Scan the natural numbers in increasing order and add the reciprocal of
each prime whose actual carry score passes the current test. -/
def adaptiveMass (c : ℝ) : ℕ → ℝ := by
  classical
  exact Nat.rec 0 (fun p mass =>
    mass + if admits c p mass then 1 / (p : ℝ) else 0)

/-- A set of actual primes specified only by scores at the current and earlier primes. -/
def adaptiveGoodPrimes (c : ℝ) : Set ℕ := {p | admits c p (adaptiveMass c p)}

theorem adaptiveMass_succ (c : ℝ) (p : ℕ) :
    adaptiveMass c (p + 1) = adaptiveMass c p + reciprocalOn (adaptiveGoodPrimes c) p := by
  classical
  change adaptiveMass c p + (if admits c p (adaptiveMass c p) then 1 / (p : ℝ) else 0) = _
  by_cases hp : p ∈ adaptiveGoodPrimes c
  · rw [if_pos (show admits c p (adaptiveMass c p) from hp), reciprocalOn_mem hp]
  · rw [if_neg (show ¬ admits c p (adaptiveMass c p) from hp), reciprocalOn_notMem hp]

theorem adaptiveMass_eq_prefix (c : ℝ) (N : ℕ) :
    adaptiveMass c N = prefixMass (reciprocalOn (adaptiveGoodPrimes c)) N := by
  induction N with
  | zero => simp [adaptiveMass]
  | succ n ih => rw [adaptiveMass_succ, prefixMass_succ, ih]

theorem mem_adaptiveGoodPrimes_iff_divisor (n : ℕ) {c : ℝ} (hc : 0 < c) :
    n + 4 ∈ adaptiveGoodPrimes c ↔ (n + 4).Prime ∧ ∃ d : DivisorIndex n,
      c * ((1 / ((n + 4 : ℕ) : ℝ)) / (1 + adaptiveMass c (n + 4))) ≤
        selectedBudget n {d} := by
  have hmass : 0 ≤ adaptiveMass c (n + 4) := by
    rw [adaptiveMass_eq_prefix]
    exact prefixMass_nonneg (reciprocalOn_nonneg _) _
  have hw : 0 < c * ((1 / ((n + 4 : ℕ) : ℝ)) / (1 + adaptiveMass c (n + 4))) :=
    mul_pos hc (div_pos (by positivity) (by linarith))
  change ((n + 4).Prime ∧ 3 ≤ n + 4 ∧ _ ≤ primeScore (n + 4)) ↔ _
  simp only [show 3 ≤ n + 4 by omega, true_and, primeScore_add_four]
  rw [le_bestBudget_iff_exists_divisor n hw]

/-- The score test uses a set's own earlier reciprocal mass. -/
def SelfQualified (c : ℝ) (A : Set ℕ) : Prop :=
  ∀ p ∈ A, admits c p (prefixMass (reciprocalOn A) p)

theorem selfQualified_adaptiveGoodPrimes (c : ℝ) : SelfQualified c (adaptiveGoodPrimes c) := by
  intro p hp
  rwa [← adaptiveMass_eq_prefix]

private theorem admits_mono {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y)
    {p : ℕ} (h : admits c p x) : admits c p y := by
  refine ⟨h.1, h.2.1, le_trans ?_ h.2.2⟩
  apply mul_le_mul_of_nonneg_left _ hc
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- The recursion gives the greatest set passing its own mass-dependent test. -/
theorem adaptiveGoodPrimes_maximal {A : Set ℕ} {c : ℝ} (hc : 0 ≤ c) (hA : SelfQualified c A) :
    A ⊆ adaptiveGoodPrimes c := by
  have hmass (n : ℕ) : prefixMass (reciprocalOn A) n ≤ adaptiveMass c n := by
    induction n with
    | zero => simp [adaptiveMass]
    | succ n ih =>
      rw [prefixMass_succ, adaptiveMass_succ]
      apply add_le_add ih
      by_cases hp : n ∈ A
      · have hg : n ∈ adaptiveGoodPrimes c :=
          admits_mono hc (prefixMass_nonneg (reciprocalOn_nonneg A) n) ih (hA n hp)
        rw [reciprocalOn_mem hp, reciprocalOn_mem hg]
      · rw [reciprocalOn_notMem hp]
        exact reciprocalOn_nonneg _ _
  intro p hp
  exact admits_mono hc (prefixMass_nonneg (reciprocalOn_nonneg A) p) (hmass p) (hA p hp)

/-- Existence of a divergent set passing its own threshold is exactly the
divergence of one specified set of primes. -/
theorem adaptive_diverges_iff_exists {c : ℝ} (hc : 0 ≤ c) :
    (¬ Summable (reciprocalOn (adaptiveGoodPrimes c))) ↔
      ∃ A : Set ℕ, SelfQualified c A ∧ ¬ Summable (reciprocalOn A) := by
  constructor
  · intro hd
    exact ⟨adaptiveGoodPrimes c, selfQualified_adaptiveGoodPrimes c, hd⟩
  · rintro ⟨A, hA, hd⟩ hs
    apply hd (Summable.of_nonneg_of_le (reciprocalOn_nonneg A) _ hs)
    intro p
    by_cases hp : p ∈ A
    · rw [reciprocalOn_mem hp, reciprocalOn_mem (adaptiveGoodPrimes_maximal hc hA hp)]
    · rw [reciprocalOn_notMem hp]
      exact reciprocalOn_nonneg _ _

theorem goodPrimes_subset_adaptiveGoodPrimes {c : ℝ} (hc : 0 ≤ c) :
    goodPrimes c ⊆ adaptiveGoodPrimes c := by
  apply adaptiveGoodPrimes_maximal hc
  intro p hp
  apply admits_mono hc (x := 0) le_rfl (prefixMass_nonneg (reciprocalOn_nonneg _) _)
  exact ⟨hp.1, hp.2.1, by simpa [div_eq_mul_inv] using hp.2.2⟩

private theorem logWeight_score_le {A : Set ℕ} {c : ℝ} (hc : 0 ≤ c) (hA : SelfQualified c A)
    (p : ℕ) : c * logWeight (reciprocalOn A) p ≤ primeScore p := by
  refine (mul_le_mul_of_nonneg_left (logWeight_le (reciprocalOn_nonneg A) p) hc).trans ?_
  by_cases hp : p ∈ A
  · rw [reciprocalOn_mem hp]
    exact (hA p hp).2.2
  · simp only [reciprocalOn_notMem hp, zero_div, mul_zero]
    exact primeScore_nonneg p

/-- Quantitative certificate at every cutoff, including the boundary term at zero. -/
theorem log_mass_le_score_sum {A : Set ℕ} {c : ℝ} (hc : 0 ≤ c) (hA : SelfQualified c A)
    (N : ℕ) : c * Real.log (1 + prefixMass (reciprocalOn A) N) ≤ prefixMass primeScore N := by
  rw [← logWeight_sum]
  unfold prefixMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p _ => logWeight_score_le hc hA p)

theorem riemannHypothesis_of_adaptiveGoodPrimes {c : ℝ} (hc : 0 < c)
    (hd : ¬ Summable (reciprocalOn (adaptiveGoodPrimes c))) : RiemannHypothesis := by
  apply riemannHypothesis_of_iteratedLogFloor _ 1 hc hd (loss := fun _ => 0) (by simp)
  intro p
  simpa only [iteratedLogWeight, add_zero] using
    logWeight_score_le hc.le (selfQualified_adaptiveGoodPrimes c) p

/-- A single raw residual pairing on each prime of any set with divergent
reciprocal mass suffices at the logarithmically reduced arithmetic scale. -/
theorem riemannHypothesis_of_raw_pairings_on_primes (A : Set ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ 4 ≤ p) (hd : ¬ Summable (reciprocalOn A))
    {C : ℝ} (hC : 0 < C)
    (hsource : ∀ n, n + 4 ∈ A → ∃ d : DivisorIndex n,
      C * middleError n ^ 2 /
        (((n + 4 : ℕ) : ℝ) ^ 2 * (d.val : ℝ) * (1 + prefixMass (reciprocalOn A) (n + 4)))
        ≤ rawPairing n d ^ 2) : RiemannHypothesis := by
  let c := C * ZetaTwoProbability.zetaTwo / (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)
  have hc : 0 < c := div_pos (mul_pos hC ZetaTwoProbability.zetaTwo_pos) cZero_pos
  apply riemannHypothesis_of_adaptiveGoodPrimes hc
  apply (adaptive_diverges_iff_exists hc.le).mpr
  refine ⟨A, ?_, hd⟩
  intro p hp
  obtain ⟨hprime, h4⟩ := hA p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 4 := ⟨p - 4, by omega⟩
  obtain ⟨d, hs⟩ := hsource n hp
  let m := 1 + prefixMass (reciprocalOn A) (n + 4)
  have hm : 0 < m := by
    dsimp [m]
    linarith [prefixMass_nonneg (reciprocalOn_nonneg A) (n + 4)]
  have hdpos : (0 : ℝ) < d.val := Nat.cast_pos.mpr (by have := d.property.2; omega)
  have hb : 0 < divisorMass n {d} := by
    simpa only [divisorMass, Finset.sum_singleton] using one_div_pos.mpr hdpos
  have hfloor : (C / m) * middleError n ^ 2 * divisorMass n {d} / ((n + 4 : ℕ) : ℝ) ^ 2 ≤
      sourceMass n {d} := by
    simp only [divisorMass, sourceMass, Finset.sum_singleton, score_eq_neg_rawPairing, neg_sq]
    refine le_trans (le_of_eq ?_) hs
    dsimp [m]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  refine ⟨hprime, by omega, ?_⟩
  rw [primeScore_add_four]
  change c * ((1 / ((n + 4 : ℕ) : ℝ)) / m) ≤ bestBudget n
  calc
    _ = ((C / m) * ZetaTwoProbability.zetaTwo /
        (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) / ((n + 4 : ℕ) : ℝ) := by
      dsimp [c]
      simp only [div_eq_mul_inv, one_mul]
      ring
    _ ≤ selectedBudget n {d} := prime_budget_of_source_floor n hprime {d} (div_pos hC hm) hb hfloor
    _ ≤ bestBudget n := singleton_le_best n d

end RiemannResearch.RH.QCRTCarryGoodPrimes

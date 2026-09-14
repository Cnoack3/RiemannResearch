import RiemannResearch.RH.ArithmeticChargeEscape

/-!
# Every rough squarefree dilation is necessary

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
section 8. The aggregate mass at dilation q is c₂,q+c₃,q in the usual
two-array presentation. Arbitrary signs and repeated generator indices are
allowed, so the theorem is independent of the chosen finite presentation.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators Topology
open Filter PositiveSeedCone FiniteSeedComponentCharge
noncomputable section

def dilationCoefficientMass {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (c : ι → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ s, if m i = q then c i else 0

/-- At a rough dilation the incoming seed edges are absent, so the actual
Möbius charge equals the sum of both seed coefficients at that dilation. -/
theorem rough_singleton_charge_eq_dilationMass {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3) (hm : ∀ i ∈ s, 0 < m i) :
    componentCharge {q} (seedCombination s a m c) = dilationCoefficientMass s m c q := by
  rw [componentCharge_seedCombination]
  unfold dilationCoefficientMass
  apply Finset.sum_congr rfl
  intro i hi
  have ha0 : 0 < a i := by rcases ha i hi with h | h <;> omega
  have had : a i ∣ 6 := by rcases ha i hi with h | h <;> simp [h]
  have hnot : a i * m i ≠ q := by
    intro he
    have hcop : Nat.Coprime (a i) q := (Nat.Coprime.of_dvd_right had hc).symm
    have hone := hcop.eq_one_of_dvd ⟨m i, he.symm⟩
    rcases ha i hi with h | h <;> omega
  rw [componentCharge_generator {q} (a i) (m i)
    (by intro d hd; have he := Finset.mem_singleton.mp hd; simpa only [he] using hq) ha0 (hm i hi)]
  simp only [Finset.mem_singleton, hnot, if_false, sub_zero]
  split_ifs <;> ring

/-- Every successful signed legal sequence has coefficient mass tending to
μ(q)/q at every positive dilation q coprime to 6. -/
theorem rough_dilationCoefficientMass_tendsto {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hp : ∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (𝓝 1)) :
    Tendsto (fun j => dilationCoefficientMass (s j) (m j) (c j) q) atTop
      (𝓝 ((ArithmeticFunction.moebius q : ℝ) / (q : ℝ))) := by
  have ht := componentCharge_tendsto_target
    (F := fun j => seedCombination (s j) (a j) (m j) (c j))
    (by intro j; simp [seedCombination, TwoSeedThreshold.certificateGenerator]) hp {q}
    (by intro d hd; have he := Finset.mem_singleton.mp hd; simpa only [he] using hq)
  simpa only [rough_singleton_charge_eq_dilationMass q hq hc _ _ _ _ (ha _) (hm _),
    componentSignal, Finset.sum_singleton] using ht

/-- Omitting even one rough squarefree dilation rules out approximation. -/
theorem omitted_rough_squarefree_dilation_no_pointwise_limit {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6) (hsq : Squarefree q)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (homit : ∀ j i, i ∈ s j → m j i ≠ q) :
    ¬ (∀ n, 0 < n → Tendsto
      (fun j => seedCombination (s j) (a j) (m j) (c j) n) atTop (𝓝 1)) := by
  intro hp
  have ht := rough_dilationCoefficientMass_tendsto q hq hc s a m c ha hm hp
  have hz (j : ℕ) : dilationCoefficientMass (s j) (m j) (c j) q = 0 := by
    unfold dilationCoefficientMass
    apply Finset.sum_eq_zero
    intro i hi
    simp [homit j i hi]
  simp only [hz] at ht
  have he := tendsto_nhds_unique ht
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hmu : (ArithmeticFunction.moebius q : ℝ) ≠ 0 := by
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
  exact (div_ne_zero hmu (by positivity : (q : ℝ) ≠ 0)) he

end
end RiemannResearch.RH.Pareto

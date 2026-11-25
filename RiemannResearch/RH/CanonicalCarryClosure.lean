import RiemannResearch.RH.PhysicalPrimePowerCarryProjection
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.NumberTheory.PrimePowerCRTDecomposition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Closure of the unprojected canonical mixed carries

Source: the Compact Orbit question on finite CRT presentations and Hilbert
completion. Take a common auxiliary prime congruent to one modulo two
prime-power conductors. A signed combination of their canonical floor carries
cancels its shared column. Two limit passages then recover each prime-power atom.
Unlike the corrected mixed-packet dictionary, the unprojected canonical carries
have dense span in the full closed residue space for both physical measures.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.CanonicalCarryClosure
open PhysicalPrimePowerCarryProjection
open RiemannResearch.NumberTheory.PrimePowerCRT

/-- A pair consisting of a prime power and a larger prime congruent to one
has an explicit canonical mixed carry. -/
theorem canonicalVector_pair_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : ℕ → H) {a p k t : ℕ} (hp : p.Prime) (hk : 0 < k) (ha : a = p ^ k)
    (ht : t.Prime) (hlt : a < t) (hmod : t ≡ 1 [MOD a]) :
    (1 < a * t ∧ (a * t).primeFactors.card ≠ 1) ∧
      canonicalVector g (a * t) =
        g a + ((((a : ℝ) - 1) * (t : ℝ) + 1) / (a : ℝ)) • g t - g (a * t) := by
  classical
  have hpa : p ≤ a := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [ha, pow_succ]
    exact Nat.le_mul_of_pos_left p (pow_pos hp.pos j)
  have ha1 : 1 < a := hp.one_lt.trans_le hpa
  have ha0 : 0 < a := by omega
  have hne : p ≠ t := (hpa.trans_lt hlt).ne
  have hfac : (a * t).primeFactors = {p, t} := by
    rw [Nat.primeFactors_mul ha0.ne' ht.ne_zero, ha, Nat.primeFactors_prime_pow hk.ne' hp,
      ht.primeFactors]
    simp
  have hmP : modulus (a * t) p = a := by
    rw [modulus, Nat.factorization_mul ha0.ne' ht.ne_zero, Finsupp.add_apply, ha,
      hp.factorization_pow, ht.factorization]
    simp [hne]
  have hmT : modulus (a * t) t = t := by
    rw [modulus, Nat.factorization_mul ha0.ne' ht.ne_zero, Finsupp.add_apply, ha,
      hp.factorization_pow, ht.factorization]
    simp [Ne.symm hne]
  have hda : a * t / a = t := Nat.mul_div_cancel_left t ha0
  have hdt : a * t / t = a := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel_left a ht.pos
  have hinP : p ∈ (a * t).primeFactors := by rw [hfac]; simp
  have hinT : t ∈ (a * t).primeFactors := by rw [hfac]; simp
  have hcpb := (coefficient_bounds hinP).2
  have hctb := (coefficient_bounds hinT).2
  rw [hmP] at hcpb
  rw [hmT] at hctb
  have hmz : (t : ZMod a) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff t 1 a).mpr hmod
  have hc := coefficient_inverse (d := a * t) (Nat.mul_ne_zero ha0.ne' ht.ne_zero) hp
  rw [hmP, hda, hmz, one_mul] at hc
  have hcp : coefficient (a * t) p = 1 := by
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hcpb, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt ha1] using hv
  obtain ⟨z, hz⟩ := cleared_reciprocal_identity (a * t) (Nat.mul_ne_zero ha0.ne' ht.ne_zero)
  have hpout : p ∉ ({t} : Finset ℕ) := by simpa using hne
  simp only [hfac, Finset.sum_insert hpout, Finset.sum_singleton, hmP, hmT, hda, hdt, hcp,
    Nat.cast_one, mul_one, Nat.cast_mul] at hz
  have hta : (t : ℤ) ≤ (a : ℤ) * (t : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_left t ha0
  have hco : (coefficient (a * t) t : ℤ) ≤ (t : ℤ) := by exact_mod_cast hctb.le
  have htZ : (1 : ℤ) < t := by exact_mod_cast ht.one_lt
  have hzpos : 0 < z := by
    by_contra! hbad
    nlinarith only [hz, htZ, mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℤ) ≤ (a : ℤ) * t by positivity) hbad,
      mul_nonneg (show (0 : ℤ) ≤ a by positivity)
        (show (0 : ℤ) ≤ coefficient (a * t) t by positivity)]
  have hzlt : z < 2 := by
    by_contra! hbad
    nlinarith only [hz, hta, mul_le_mul_of_nonneg_left hco (show (0 : ℤ) ≤ a by positivity),
      mul_le_mul_of_nonneg_left hbad (show (0 : ℤ) ≤ (a : ℤ) * t by positivity)]
  have hz1 : z = 1 := by omega
  rw [hz1, mul_one] at hz
  have hre : (t : ℝ) + (a : ℝ) * (coefficient (a * t) t : ℝ) =
      1 + (a : ℝ) * (t : ℝ) := by exact_mod_cast hz
  have hct : (coefficient (a * t) t : ℝ) =
      (((a : ℝ) - 1) * (t : ℝ) + 1) / (a : ℝ) := by
    apply (eq_div_iff (show (a : ℝ) ≠ 0 by exact_mod_cast ha0.ne')).2
    linarith
  constructor
  · refine ⟨by nlinarith [Nat.le_mul_of_pos_left t ha0, ht.one_lt], ?_⟩
    rw [hfac, Finset.card_insert_of_notMem hpout, Finset.card_singleton]
    decide
  · simp only [canonicalVector, hfac, Finset.sum_insert hpout, Finset.sum_singleton, hmP, hmT,
      hcp, Nat.cast_one, one_smul, hct]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Closed span of the literal canonical mixed carries before any projection. -/
abbrev rawClosure (g : ℕ → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun d : MixedConductor =>
    canonicalVector g d.val))).topologicalClosure

def asympWeight (a : ℕ) : ℝ := 1 - (a : ℝ)⁻¹

def rowWeight (a t : ℕ) : ℝ := asympWeight a + (a : ℝ)⁻¹ / (t : ℝ)

private theorem rowWeight_tendsto (a : ℕ) {t : ℕ → ℕ} (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => rowWeight a (t n)) atTop (𝓝 (asympWeight a)) := by
  have hd : Tendsto (fun n => ((t n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hz : Tendsto (fun n => (a : ℝ)⁻¹ / (t n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have hc : Tendsto (fun _ : ℕ => asympWeight a) atTop (𝓝 (asympWeight a)) := tendsto_const_nhds
  simpa only [rowWeight, add_zero] using hc.add hz

private theorem mul_escape_left (a : ℕ) (ha : 0 < a) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) : Tendsto (fun n => a * t n) atTop atTop := by
  apply tendsto_atTop_mono _ ht
  intro n
  simpa only [one_mul] using Nat.mul_le_mul_right (t n) (show 1 ≤ a from ha)

private theorem balanced_limit (g : ℕ → H) (hg : Tendsto g atTop (𝓝 0))
    (a b : PrimePowerConductor) {t : ℕ → ℕ} (ht : Tendsto t atTop atTop)
    (hm : ∀ n, rowWeight b.val (t n) • (g a.val - g (a.val * t n)) -
      rowWeight a.val (t n) • (g b.val - g (b.val * t n)) ∈ rawClosure g) :
    asympWeight b.val • g a.val - asympWeight a.val • g b.val ∈ rawClosure g := by
  have hdiff (c : PrimePowerConductor) :
      Tendsto (fun n => g c.val - g (c.val * t n)) atTop (𝓝 (g c.val)) := by
    have hc : Tendsto (fun _ : ℕ => g c.val) atTop (𝓝 (g c.val)) := tendsto_const_nhds
    simpa only [sub_zero, Function.comp_apply] using
      hc.sub (hg.comp (mul_escape_left _ (lt_trans Nat.zero_lt_one c.property.1) ht))
  have h := ((rowWeight_tendsto b.val ht).smul (hdiff a)).sub
    ((rowWeight_tendsto a.val ht).smul (hdiff b))
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto h (Eventually.of_forall hm)

private theorem primePower_mem_of_balanced_limits (g : ℕ → H) (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ a b : PrimePowerConductor,
      asympWeight b.val • g a.val - asympWeight a.val • g b.val ∈ rawClosure g)
    (a : PrimePowerConductor) : g a.val ∈ rawClosure g := by
  let b : ℕ → PrimePowerConductor := fun n =>
    ⟨2 ^ (n + 1), (primePowerConductor_iff _).2 ⟨2, n + 1, Nat.prime_two, Nat.succ_pos _, rfl⟩⟩
  have hb : Tendsto (fun n => (b n).val) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))).comp (tendsto_add_atTop_nat 1)
  have hcast : Tendsto (fun n => ((b n).val : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hb
  have hinv : Tendsto (fun n => ((b n).val : ℝ)⁻¹) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => (1 : ℝ) / ((b n).val : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hcast
    simpa only [one_div] using hh
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hv : Tendsto (fun n => asympWeight (b n).val) atTop (𝓝 1) := by
    simpa only [asympWeight, sub_zero] using hone.sub hinv
  have hx : Tendsto (fun _ : ℕ => g a.val) atTop (𝓝 (g a.val)) := tendsto_const_nhds
  have hw : Tendsto (fun _ : ℕ => asympWeight a.val) atTop (𝓝 (asympWeight a.val)) :=
    tendsto_const_nhds
  have hlim := (hv.smul hx).sub (hw.smul (hg.comp hb))
  have hclosed : IsClosed (rawClosure g : Set H) := Submodule.isClosed_topologicalClosure _
  have hmem : (1 : ℝ) • g a.val - asympWeight a.val • (0 : H) ∈ rawClosure g :=
    hclosed.mem_of_tendsto hlim
      (Eventually.of_forall (fun n => h a (b n)))
  simpa only [one_smul, smul_zero, sub_zero] using hmem

private theorem modulus_is_power {d p : ℕ} (hp : p ∈ d.primeFactors) :
    1 < modulus d p ∧ (modulus d p).primeFactors.card = 1 := by
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpos := hprime.factorization_pos_of_dvd (Nat.mem_primeFactors.mp hp).2.2
    (Nat.mem_primeFactors.mp hp).2.1
  exact (primePowerConductor_iff _).2 ⟨p, _, hprime, hpos, rfl⟩

private theorem full_atom_mem (g : ℕ → H) {d : ℕ} (hd : 1 < d) : g d ∈ fullClosure g :=
  (Submodule.span ℝ _).le_topologicalClosure
    (Submodule.subset_span ⟨(⟨d, hd⟩ : UniversalAtomCarry.Atom), rfl⟩)

private theorem rawClosure_le_full (g : ℕ → H) : rawClosure g ≤ fullClosure g := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  unfold canonicalVector
  apply (fullClosure g).sub_mem _ (full_atom_mem g d.property.1)
  apply (fullClosure g).sum_mem
  intro p hp
  exact (fullClosure g).smul_mem _ (full_atom_mem g (modulus_is_power hp).1)

/-- Conductor cancellation first recovers every prime-power atom in the closed
span of the raw carries. Each remaining atom is its canonical CRT row minus
its own raw carry. -/
theorem carryClosure_eq_fullClosure_of_balanced_rows (g : ℕ → H)
    (hg : Tendsto g atTop (𝓝 0))
    (hrows : ∀ a b : PrimePowerConductor, ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧
      ∀ n, rowWeight b.val (t n) • (g a.val - g (a.val * t n)) -
        rowWeight a.val (t n) • (g b.val - g (b.val * t n)) ∈ rawClosure g) :
    rawClosure g = fullClosure g := by
  have hpowers (a : PrimePowerConductor) : g a.val ∈ rawClosure g := by
    apply primePower_mem_of_balanced_limits g hg _ a
    intro a b
    obtain ⟨t, ht, hm⟩ := hrows a b
    exact balanced_limit g hg a b ht hm
  apply le_antisymm (rawClosure_le_full g)
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change g d.val ∈ rawClosure g
  by_cases hp : d.val.primeFactors.card = 1
  · exact hpowers ⟨d.val, d.property, hp⟩
  · have hc : canonicalVector g d.val ∈ rawClosure g :=
      (Submodule.span ℝ _).le_topologicalClosure
        (Submodule.subset_span ⟨(⟨d.val, d.property, hp⟩ : MixedConductor), rfl⟩)
    let s := ∑ p ∈ d.val.primeFactors, (coefficient d.val p : ℝ) • g (modulus d.val p)
    have hs : s ∈ rawClosure g := by
      apply (rawClosure g).sum_mem
      intro p hp'
      exact (rawClosure g).smul_mem _ (hpowers ⟨_, modulus_is_power hp'⟩)
    change s - g d.val ∈ rawClosure g at hc
    simpa only [sub_sub_cancel] using (rawClosure g).sub_mem hs hc


private theorem common_auxiliary_primes (a b : PrimePowerConductor) :
    ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ ∀ n,
      (t n).Prime ∧ a.val < t n ∧ b.val < t n ∧
      t n ≡ 1 [MOD a.val] ∧ t n ≡ 1 [MOD b.val] := by
  have ha : 0 < a.val := Nat.zero_lt_of_lt a.property.1
  have hb : 0 < b.val := Nat.zero_lt_of_lt b.property.1
  choose t ht using (fun n : ℕ => Nat.exists_prime_gt_modEq_one
    (n + a.val + b.val) (Nat.mul_pos ha hb).ne')
  refine ⟨t, tendsto_atTop.2 (fun m => ?_), fun n => ?_⟩
  · filter_upwards [eventually_ge_atTop m] with n hn
    have := (ht n).2.1
    omega
  · obtain ⟨hp, hn, hmod⟩ := ht n
    exact ⟨hp, by omega, by omega, hmod.of_dvd (dvd_mul_right a.val b.val),
      hmod.of_dvd (dvd_mul_left b.val a.val)⟩

private theorem row_scalar (a t : ℕ) (ha : 0 < a) (ht : 0 < t) :
    (((((a : ℝ) - 1) * t + 1) / a) / t) = rowWeight a t := by
  unfold rowWeight asympWeight
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

/-- With a common auxiliary prime, the two scaled rows cancel its atom exactly. -/
theorem common_prime_balanced_rows (g : ℕ → H) (a b : PrimePowerConductor) :
    ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ ∀ n,
      rowWeight b.val (t n) • (g a.val - g (a.val * t n)) -
      rowWeight a.val (t n) • (g b.val - g (b.val * t n)) ∈ rawClosure g := by
  obtain ⟨p, k, hp, hk, ha⟩ := (primePowerConductor_iff a.val).1 a.property
  obtain ⟨r, l, hr, hl, hb⟩ := (primePowerConductor_iff b.val).1 b.property
  obtain ⟨t, ht, haux⟩ := common_auxiliary_primes a b
  refine ⟨t, ht, fun n => ?_⟩
  obtain ⟨hprime, hat, hbt, hmoda, hmodb⟩ := haux n
  obtain ⟨hmA, hA⟩ := canonicalVector_pair_eq g hp hk ha hprime hat hmoda
  obtain ⟨hmB, hB⟩ := canonicalVector_pair_eq g hr hl hb hprime hbt hmodb
  have hmem (d : MixedConductor) : canonicalVector g d.val ∈ rawClosure g :=
    (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨d, rfl⟩)
  have hcomb := (rawClosure g).sub_mem
    ((rawClosure g).smul_mem (rowWeight b.val (t n)) (hmem ⟨a.val * t n, hmA⟩))
    ((rawClosure g).smul_mem (rowWeight a.val (t n)) (hmem ⟨b.val * t n, hmB⟩))
  change rowWeight b.val (t n) • canonicalVector g (a.val * t n) -
    rowWeight a.val (t n) • canonicalVector g (b.val * t n) ∈ rawClosure g at hcomb
  rw [hA, hB] at hcomb
  rw [← row_scalar a.val (t n) (Nat.zero_lt_of_lt a.property.1) hprime.pos,
    ← row_scalar b.val (t n) (Nat.zero_lt_of_lt b.property.1) hprime.pos] at hcomb ⊢
  convert hcomb using 1
  module

/-- The closed span of the actual unprojected canonical floor carries contains all
atoms whenever the normalized atoms tend to zero as the conductor escapes. -/
theorem rawClosure_eq_fullClosure (g : ℕ → H) (hg : Tendsto g atTop (𝓝 0)) :
    rawClosure g = fullClosure g :=
  carryClosure_eq_fullClosure_of_balanced_rows g hg (common_prime_balanced_rows g)

open ZetaTwoParetoTransfer ZetaTwoHilbert

/-- The actual Pareto normalized residues tend to zero as the conductor escapes. -/
theorem pAtom_tendsto_zero : Tendsto pAtom atTop (𝓝 0) := by
  have hq : Tendsto qResidue atTop (𝓝 0) := qResidue_tendsto_zero id tendsto_id
  have ht : Tendsto (fun d : ℕ => toParetoCLM (qResidue d)) atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using
      (toParetoCLM.continuous.continuousAt.tendsto.comp hq)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact toPareto_qResidue d hd

/-- In either physical norm the closed span of the unprojected canonical mixed
carries is the full legal residue space. -/
theorem physical_rawCarry_closures :
    rawClosure pAtom = Pareto.CoefficientStabilization.closedSpace ∧
    rawClosure qResidue = QFullResidueProjection.closure :=
  ⟨(rawClosure_eq_fullClosure pAtom pAtom_tendsto_zero).trans physical_full_closures.1,
    (rawClosure_eq_fullClosure qResidue (qResidue_tendsto_zero id tendsto_id)).trans
      physical_full_closures.2⟩

/-- A continuous linear map killing every canonical mixed carry kills the full
legal space. The codomain may be any real normed space. -/
theorem canonical_kernel_contains_full
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℕ → H)
    (hd : rawClosure g = fullClosure g)
    (T : H →L[ℝ] F) (hz : ∀ d : MixedConductor, T (canonicalVector g d.val) = 0) :
    fullClosure g ≤ T.ker := by
  rw [← hd]
  apply Submodule.topologicalClosure_minimal _ _ T.isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact hz d

private theorem pAtom_two_ne_zero : pAtom 2 ≠ 0 := by
  change Pareto.CoefficientStabilization.residueAtom 0 ≠ 0
  exact Pareto.CoefficientStabilization.residueAtom_linearIndependent.ne_zero 0

private theorem qResidue_two_ne_zero : qResidue 2 ≠ 0 := by
  intro hz
  apply pAtom_two_ne_zero
  calc
    pAtom 2 = toParetoCLM (qResidue 2) := (toPareto_qResidue 2 (by decide)).symm
    _ = 0 := by rw [hz, map_zero]

/-- Already fixing the single conductor-two atom is incompatible with killing
every raw canonical mixed carry. -/
theorem no_continuous_carry_retraction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (g : ℕ → H)
    (hd : rawClosure g = fullClosure g) (hn : g 2 ≠ 0) :
    ¬ ∃ T : H →L[ℝ] H, T (g 2) = g 2 ∧
      ∀ d : MixedConductor, T (canonicalVector g d.val) = 0 := by
  rintro ⟨T, hfix, hz⟩
  have hm : g 2 ∈ fullClosure g :=
    (Submodule.span ℝ _).le_topologicalClosure
      (Submodule.subset_span ⟨(⟨2, by decide⟩ : UniversalAtomCarry.Atom), rfl⟩)
  have ht : T (g 2) = 0 := canonical_kernel_contains_full g hd T hz hm
  exact hn (hfix.symm.trans ht)

theorem no_physical_prime_retraction :
    (¬ ∃ T : Pareto.ThresholdHilbert →L[ℝ] Pareto.ThresholdHilbert,
      T (pAtom 2) = pAtom 2 ∧
        ∀ d : MixedConductor, T (canonicalVector pAtom d.val) = 0) ∧
    (¬ ∃ T : QHilbert →L[ℝ] QHilbert, T (qResidue 2) = qResidue 2 ∧
        ∀ d : MixedConductor, T (canonicalVector qResidue d.val) = 0) :=
  ⟨no_continuous_carry_retraction pAtom
      (rawClosure_eq_fullClosure pAtom pAtom_tendsto_zero) pAtom_two_ne_zero,
    no_continuous_carry_retraction qResidue
      (rawClosure_eq_fullClosure qResidue (qResidue_tendsto_zero id tendsto_id))
      qResidue_two_ne_zero⟩

theorem riemannHypothesis_iff_one_mem_canonicalCarryClosure :
    RiemannHypothesis ↔ Pareto.hilbertOne ∈ rawClosure pAtom := by
  rw [physical_rawCarry_closures.1]
  exact Pareto.PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.trans
    Pareto.BaezDuarte.naturalApproximation_iff_one_mem

section ClosedRelation

/-- The finite graph columns assign each prime atom to itself and each raw
canonical mixed carry to zero. -/
def selectorGraph (g : ℕ → H) : Submodule ℝ (H × H) :=
  Submodule.span ℝ
    (Set.range (fun a : PrimePowerConductor => (g a.val, g a.val)) ∪
      Set.range (fun d : MixedConductor => (canonicalVector g d.val, (0 : H))))

/-- The closure of the selector graph is a full Cartesian product. Its vertical
fiber at zero is the entire closed prime-power span. -/
theorem selectorGraph_closure_eq_product (g : ℕ → H) (hd : rawClosure g = fullClosure g) :
    (selectorGraph g).topologicalClosure = (fullClosure g).prod (powerClosure g) := by
  let G := (selectorGraph g).topologicalClosure
  have hG : IsClosed (G : Set (H × H)) := Submodule.isClosed_topologicalClosure _
  have hprime (a : PrimePowerConductor) : g a.val ∈ powerClosure g :=
    (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨a, rfl⟩)
  have hcarry (d : MixedConductor) : canonicalVector g d.val ∈ fullClosure g := by
    rw [← hd]
    exact (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨d, rfl⟩)
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _
      ((Submodule.isClosed_topologicalClosure _).prod (Submodule.isClosed_topologicalClosure _))
    apply Submodule.span_le.mpr
    rintro _ (⟨a, rfl⟩ | ⟨d, rfl⟩)
    · exact ⟨powerClosure_le_full g (hprime a), hprime a⟩
    · exact ⟨hcarry d, Submodule.zero_mem _⟩
  · let first : H →L[ℝ] (H × H) := (ContinuousLinearMap.id ℝ H).prod 0
    let second : H →L[ℝ] (H × H) := (0 : H →L[ℝ] H).prod (ContinuousLinearMap.id ℝ H)
    have hfirst : fullClosure g ≤ G.comap first.toLinearMap := by
      rw [← hd]
      apply Submodule.topologicalClosure_minimal _ _ (hG.preimage first.continuous)
      apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact (selectorGraph g).le_topologicalClosure
        (Submodule.subset_span (Or.inr ⟨d, rfl⟩))
    have hsecond : powerClosure g ≤ G.comap second.toLinearMap := by
      apply Submodule.topologicalClosure_minimal _ _ (hG.preimage second.continuous)
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      have hdg : (g a.val, g a.val) ∈ G := (selectorGraph g).le_topologicalClosure
        (Submodule.subset_span (Or.inl ⟨a, rfl⟩))
      have hh : (g a.val, (0 : H)) ∈ G := hfirst (powerClosure_le_full g (hprime a))
      change ((0 : H), g a.val) ∈ G
      simpa only [Prod.mk_sub_mk, sub_self, sub_zero] using G.sub_mem hdg hh
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx0 : (x, (0 : H)) ∈ G := hfirst hx
    have h0y : ((0 : H), y) ∈ G := hsecond hy
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using G.add_mem hx0 h0y

end ClosedRelation

/-- Below the auxiliary odd prime, the canonical carry at twice the prime
equals the rounded-up half of the physical coordinate. -/
theorem two_prime_carry_coordinate {t : ℕ} (ht : t.Prime) (hlt : 2 < t)
    (hmod : t ≡ 1 [MOD 2]) {m : ℕ} (hm : m < t) :
    Pareto.hilbertSequence (canonicalVector pAtom (2 * t)) m =
      ((m % 2 : ℕ) : ℝ) / 2 + (m : ℝ) / 2 := by
  have h := (canonicalVector_pair_eq pAtom (a := 2) Nat.prime_two
    (by decide : 0 < 1) (by norm_num : 2 = 2 ^ 1) ht hlt hmod).2
  change Pareto.hilbertSequenceLinear _ m = _
  rw [h]
  have h2t : 0 < 2 * t := by have := ht.pos; omega
  have hmt : m < 2 * t := by omega
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, pAtom_sequence 2 (by decide), pAtom_sequence t ht.pos,
    pAtom_sequence (2 * t) h2t, ArithmeticCumulative.residueFraction,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hmt, Nat.cast_mul, Nat.cast_ofNat]
  have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne_zero
  field_simp [htr]
  ring

/-- A growing physical head gives a complete Pareto norm lower bound. -/
private theorem physical_head_norm_sq_lower (v : Pareto.ThresholdHilbert) {t : ℕ} (ht : 0 < t)
    (hh : ∀ m : ℕ, m < t → (m : ℝ) / 2 ≤ Pareto.hilbertSequence v m) :
    ((t : ℝ) - 1) / 8 ≤ ‖v‖ ^ 2 := by
  have hpoint (m : ℕ) (hm : m ∈ Finset.Ico 1 t) :
      (1 : ℝ) / 8 ≤ Pareto.positiveWeight m * Pareto.hilbertSequence v m ^ 2 := by
    obtain ⟨hm1, hmt⟩ := Finset.mem_Ico.mp hm
    have hr1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hr : 0 < (m : ℝ) := by linarith
    have hseq := hh m hmt
    calc
      _ ≤ (m : ℝ) / (4 * ((m : ℝ) + 1)) :=
        (le_div_iff₀ (by positivity)).2 (by linarith)
      _ = Pareto.positiveWeight m * ((m : ℝ)/2)^2 := by
        unfold Pareto.positiveWeight
        field_simp [hr.ne', show (m : ℝ) + 1 ≠ 0 by positivity]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (by positivity) ((show 0 ≤ (m : ℝ) / 2 by positivity).trans hseq)).2 hseq)
        (Pareto.positiveWeight_nonneg m)
  rw [Pareto.hilbert_norm_weighted_sq]
  calc
    _ = ∑ _m ∈ Finset.Ico 1 t, (1 : ℝ) / 8 := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub ht,
        Nat.cast_one]
      ring
    _ ≤ _ := (Finset.sum_le_sum hpoint).trans
      ((Pareto.hilbertSequence_square_summable v).sum_le_tsum (Finset.Ico 1 t)
        (fun m _ => mul_nonneg (Pareto.positiveWeight_nonneg m) (sq_nonneg _)))

theorem two_prime_carry_norm_sq_lower {t : ℕ} (ht : t.Prime) (hlt : 2 < t)
    (hmod : t ≡ 1 [MOD 2]) :
    ((t : ℝ) - 1) / 8 ≤ ‖canonicalVector pAtom (2 * t)‖ ^ 2 := by
  apply physical_head_norm_sq_lower _ ht.pos
  intro m hm
  rw [two_prime_carry_coordinate ht hlt hmod hm]
  exact le_add_of_nonneg_left (by positivity)

/-- The prime row contains the head of the carry and a nonnegative physical
atom, so the same squared lower bound holds before subtracting this atom. -/
theorem two_prime_row_norm_sq_lower {t : ℕ} (ht : t.Prime) (hlt : 2 < t)
    (hmod : t ≡ 1 [MOD 2]) :
    ((t : ℝ) - 1) / 8 ≤ ‖pAtom (2 * t) + canonicalVector pAtom (2 * t)‖ ^ 2 := by
  apply physical_head_norm_sq_lower _ ht.pos
  intro m hm
  have hadd : Pareto.hilbertSequence (pAtom (2 * t) + canonicalVector pAtom (2 * t)) m =
      Pareto.hilbertSequence (pAtom (2 * t)) m +
      Pareto.hilbertSequence (canonicalVector pAtom (2 * t)) m := by
    change Pareto.hilbertSequenceLinear (_ + _) m = _
    exact congrFun (map_add Pareto.hilbertSequenceLinear _ _) m
  have hnonneg : 0 ≤ Pareto.hilbertSequence (pAtom (2 * t)) m := by
    change 0 ≤ Pareto.hilbertSequenceLinear (pAtom (2 * t)) m
    rw [pAtom_sequence _ (by omega : 0 < 2 * t)]
    unfold ArithmeticCumulative.residueFraction
    positivity
  rw [hadd, two_prime_carry_coordinate ht hlt hmod hm]
  linarith [show (0 : ℝ) ≤ (m % 2 : ℕ) by positivity]

open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer

/-- The norm of the prime row on a two-prime atom amplifies that atom by at
least `sqrt(t(t-1)/8)`, in the complete physical Pareto metric. -/
theorem two_prime_oblique_amplification_sq {t : ℕ} (ht : t.Prime) (hlt : 2 < t)
    (hmod : t ≡ 1 [MOD 2]) :
    ((t : ℝ) * ((t : ℝ) - 1) / 8) * ‖pAtom (2 * t)‖ ^ 2 ≤
      ‖pAtom (2 * t) + canonicalVector pAtom (2 * t)‖ ^ 2 := by
  let h := pAtom (2 * t)
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht.pos
  have htone : (1 : ℝ) ≤ t := by exact_mod_cast ht.one_lt.le
  have hcast : 0 < 2 * t := by omega
  have hp : h = toPareto (qResidue (2 * t)) := (toPareto_qResidue _ hcast).symm
  have hsmall : ‖h‖ ^ 2 ≤ 1 / (t : ℝ) := by
    rw [hp]
    refine (toPareto_norm_sq_le _).trans
      ((mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div (2 * t) (by omega))
          zetaTwo_pos.le).trans_eq ?_)
    push_cast
    field_simp [zetaTwo_pos.ne', htr.ne']
  have hscale : (t : ℝ) * ‖h‖ ^ 2 ≤ 1 := by
    have hh := (le_div_iff₀ htr).1 hsmall
    simpa only [mul_comm] using hh
  calc
    _ = (((t : ℝ) - 1) / 8) * ((t : ℝ) * ‖h‖ ^ 2) := by dsimp only [h]; ring
    _ ≤ ((t : ℝ) - 1) / 8 := mul_le_of_le_one_right (by linarith) hscale
    _ ≤ _ := two_prime_row_norm_sq_lower ht hlt hmod

end RiemannResearch.RH.CanonicalCarryClosure

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.physical_rawCarry_closures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.physical_rawCarry_closures

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.selectorGraph_closure_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.selectorGraph_closure_eq_product

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.two_prime_oblique_amplification_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.two_prime_oblique_amplification_sq

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.riemannHypothesis_iff_one_mem_canonicalCarryClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.riemannHypothesis_iff_one_mem_canonicalCarryClosure

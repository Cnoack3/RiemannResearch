import RiemannResearch.Probability.CountableProductConditioning
import RiemannResearch.RH.IntegerDPPLiftFactorization

/-!
# Conditional independent integer lifts of selected residue classes

Source: the user's arithmetic projection DPP construction. Distinct labelled
conductor classes identify a countable partition into full configurations.
The checked determinant factorization and ordinary countable additivity
normalize this partition, giving the actual conditional joint point masses.
No independent-lift, density, RH, or coupling provider is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.ProductConditioning

abbrev residueLiftFiber (L r : ℕ) := {k : ℕ | (k + 1) % L = (r + 1) % L}

abbrev residueLiftTuple {n : ℕ} (L : ℕ) (r : Fin n → ℕ) :=
  (i : Fin n) → residueLiftFiber L (r i)

def residueClassWeight (L r : ℕ) : ℝ := ∑' k : residueLiftFiber L r, paretoWeight k.val

def liftConfigurationEvent {n : ℕ} (L : ℕ) (r : Fin n → ℕ)
    (f : residueLiftTuple L r) : Set (ℕ → Bool) :=
  {x | {i | x i = true} = Set.range (fun i => (f i).val)}

/-- Exactly one occupied integer in each listed residue class, and no others. -/
def residueClassPatternEvent {n : ℕ} (L : ℕ) (r : Fin n → ℕ) : Set (ℕ → Bool) :=
  ⋃ f : residueLiftTuple L r, liftConfigurationEvent L r f

private def liftEmbedding {n : ℕ} (L : ℕ) (r : Fin n → ℕ)
    (hsep : Function.Injective (fun i => (r i + 1) % L))
    (f : residueLiftTuple L r) : Fin n ↪ ℕ :=
  ⟨fun i => (f i).val, by
    intro i j hij
    apply hsep
    calc
      _ = ((f i).val + 1) % L := (f i).property.symm
      _ = ((f j).val + 1) % L := congrArg (fun k : ℕ => (k + 1) % L) hij
      _ = _ := (f j).property⟩

private theorem lift_range_injective {n : ℕ} (L : ℕ) (r : Fin n → ℕ)
    (hsep : Function.Injective (fun i => (r i + 1) % L)) :
    Function.Injective (fun f : residueLiftTuple L r =>
      Set.range (fun i => (f i).val)) := by
  intro f g h
  change Set.range (fun i => (f i).val) = Set.range (fun i => (g i).val) at h
  funext i
  apply Subtype.ext
  have hm : (f i).val ∈ Set.range (fun j => (g j).val) := by
    rw [← h]
    exact ⟨i, rfl⟩
  obtain ⟨j, hji⟩ := hm
  have hij : i = j := by
    apply hsep
    calc
      _ = ((f i).val + 1) % L := (f i).property.symm
      _ = ((g j).val + 1) % L := congrArg (fun k : ℕ => (k + 1) % L) hji.symm
      _ = _ := (g j).property
  subst j
  exact hji.symm

private theorem configurationEvent_measurable (S : Set ℕ) :
    MeasurableSet {x : ℕ → Bool | {i | x i = true} = S} := by
  let z : ℕ → Bool := fun i => decide (i ∈ S)
  have he : {x : ℕ → Bool | {i | x i = true} = S} = {z} := by
    ext x
    constructor
    · intro hx
      apply Set.mem_singleton_iff.mpr
      funext i
      have hm : x i = true ↔ i ∈ S := (Set.ext_iff.mp hx) i
      by_cases hi : i ∈ S
      · have hxi := hm.mpr hi
        simpa [z, hi] using hxi
      · have hxi : x i ≠ true := fun hh => hi (hm.mp hh)
        cases hb : x i <;> simp_all [z]
    · intro hx
      have hx' := Set.mem_singleton_iff.mp hx
      subst x
      ext i
      simp [z]
  rw [he]
  exact measurableSet_singleton z

theorem residueClassWeight_pos (L r : ℕ) : 0 < residueClassWeight L r := by
  have hs : Summable (fun k : residueLiftFiber L r => paretoWeight k.val) :=
    paretoWeight_hasSum.summable.subtype _
  have hb := hs.sum_le_tsum ({⟨r, rfl⟩} : Finset (residueLiftFiber L r))
    (fun k hk => (paretoWeight_pos k.val).le)
  have hr : paretoWeight r ≤ residueClassWeight L r := by
    simpa only [Finset.sum_singleton, residueClassWeight] using hb
  exact lt_of_lt_of_le (paretoWeight_pos r) hr

theorem residueLiftWeight_tsum_one (L r : ℕ) :
    (∑' k : residueLiftFiber L r, paretoWeight k.val / residueClassWeight L r) = 1 := by
  rw [tsum_div_const]
  change residueClassWeight L r / residueClassWeight L r = 1
  exact div_self (ne_of_gt (residueClassWeight_pos L r))

/-- Given the selected classes, every complete lift tuple has the product of
the individually normalized Pareto probabilities. Since the tuple space is
countable, these joint point masses specify the conditional independent law. -/
theorem integerLaw_conditional_residue_lifts (n L : ℕ) (r : Fin n → ℕ)
    (hL : ∀ d : Fin n, d.val + 2 ∣ L)
    (hsep : Function.Injective (fun i => (r i + 1) % L))
    (hpos : 0 < (integerLaw n).real (residueClassPatternEvent L r))
    (f : residueLiftTuple L r) :
    (integerLaw n).real (liftConfigurationEvent L r f) /
        (integerLaw n).real (residueClassPatternEvent L r) =
      ∏ i, paretoWeight (f i).val / residueClassWeight L (r i) := by
  let C : ℝ := Matrix.det (Matrix.of (fun i j => normalizedIntegerKernel n (r i) (r j)))
  have hdisj : Pairwise (fun f g : residueLiftTuple L r =>
      Disjoint (liftConfigurationEvent L r f) (liftConfigurationEvent L r g)) := by
    intro f g hfg
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hfg (lift_range_injective L r hsep (hx.symm.trans hy))
  have hmeas (f : residueLiftTuple L r) : MeasurableSet (liftConfigurationEvent L r f) :=
    configurationEvent_measurable _
  have hmass (f : residueLiftTuple L r) :
      (integerLaw n).real (liftConfigurationEvent L r f) = C * ∏ i, paretoWeight (f i).val := by
    let e := liftEmbedding L r hsep f
    have hres (i : Fin n) (d : Fin n) :
        ((f i).val + 1) % (d.val + 2) = (r i + 1) % (d.val + 2) := by
      have hh := congrArg (fun k : ℕ => k % (d.val + 2)) (f i).property
      simpa only [Nat.mod_mod_of_dvd ((f i).val + 1) (hL d),
        Nat.mod_mod_of_dvd (r i + 1) (hL d)] using hh
    have he : Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j)) =
        Matrix.of (fun i j => normalizedIntegerKernel n (r i) (r j)) := by
      ext i j
      exact normalizedIntegerKernel_residue_congr n (e i) (r i) (e j) (r j)
        (hres i) (hres j)
    calc
      _ = (∏ i, paretoWeight (e i)) *
          Matrix.det (Matrix.of (fun i j => normalizedIntegerKernel n (e i) (e j))) :=
        integerLaw_full_configuration_weight_factorization n e
      _ = (∏ i, paretoWeight (e i)) * C := by rw [he]
      _ = _ := mul_comm _ _
  have h := conditional_product_partition (μ := integerLaw n) n
    (fun i => residueLiftFiber L (r i)) (liftConfigurationEvent L r) hdisj hmeas
    (fun i k => paretoWeight k.val) (fun i k => (paretoWeight_pos k.val).le) C hmass hpos f
  exact h

end RiemannResearch.RH.Pareto.IntegerDPP

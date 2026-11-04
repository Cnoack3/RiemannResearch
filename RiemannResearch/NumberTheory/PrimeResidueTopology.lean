/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Algebra.Order.Field
import Lean.Elab.Tactic.Omega
/-!
# Infinite prime-residue CRT and continuous extension

Finite CRT gives arbitrarily large positive representatives for every finite
prime-residue cylinder. Consequently every point of the infinite product is
the limit of a cofinal sequence of positive integers.

The extension theorem uses the congruence uniformity induced by this embedding,
not the discrete uniformity on the natural numbers. It proves the precise
universal extension property for maps to every complete Hausdorff uniform space.
Uniform continuity of any particular arithmetic function is a separate premise.

Sources for the standard construction and terminology:
* Mathlib's finite CRT, `Nat.chineseRemainderOfFinset`.
* Bourbaki, General Topology, and I. M. James, Topologies and Uniformities,
  as cited in Mathlib.Topology.UniformSpace.Completion:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Completion.html.
* T. Tao, An Epsilon of Room I (AMS, 2010), Exercise 1.10.28, for
  finite-coordinate uniform approximation on compact products.

The factorial recurrence and constant-limit consequence are elementary
applications of this topology. The product here has factors ZMod p, not Z_p;
it is the squarefree congruence completion, not the full profinite integers.
The product is packaged as an AbstractCompletion and canonically identified
with Mathlib's completion. No inverse-system categorical IsLimit is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimeResidueTopology

theorem factorial_shift_cofinal (n : ℕ) :
    Tendsto (fun k : ℕ => n + k.factorial) atTop atTop :=
  tendsto_atTop_mono (fun k => (Nat.self_le_factorial k).trans (Nat.le_add_left _ _))
    tendsto_id

theorem factorial_shift_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => fun p : Nat.Primes =>
      ((n + k.factorial : ℕ) : ZMod p.val)) atTop
      (𝓝 (fun p : Nat.Primes => (n : ZMod p.val))) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop p.val] with k hk
  simp only [Nat.cast_add,
    (ZMod.natCast_eq_zero_iff k.factorial p.val).2
      (Nat.dvd_factorial p.property.pos hk), add_zero]

theorem continuous_trace_limit_constant
    (F : C((p : Nat.Primes) → ZMod p.val, ℝ)) {a : ℕ → ℝ} {L : ℝ}
    (hF : ∀ n : ℕ, 1 ≤ n → F (fun p => (n : ZMod p.val)) = a n)
    (ha : Tendsto a atTop (𝓝 L)) (n : ℕ) :
    F (fun p => (n : ZMod p.val)) = L := by
  have htrace : Tendsto (fun k : ℕ => F (fun p => ((n + k.factorial : ℕ) : ZMod p.val)))
      atTop (𝓝 (F (fun p => (n : ZMod p.val)))) :=
    F.continuous.continuousAt.tendsto.comp (factorial_shift_tendsto n)
  have hvalue : Tendsto (fun k : ℕ => F (fun p => ((n + k.factorial : ℕ) : ZMod p.val)))
      atTop (𝓝 L) := by
    apply (ha.comp (factorial_shift_cofinal n)).congr'
    exact Eventually.of_forall (fun k : ℕ => (hF (n + k.factorial)
      (by have := Nat.factorial_pos k; omega)).symm)
  exact tendsto_nhds_unique htrace hvalue


theorem finite_crt_large (S : Finset Nat.Primes)
    (x : (p : Nat.Primes) → ZMod p.val) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ p ∈ S, (n : ZMod p.val) = x p := by
  classical
  let (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩
  have hcop : Set.Pairwise (↑S : Set Nat.Primes)
      (fun p q => Nat.Coprime p.val q.val) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes p.property q.property).2
      (fun he => hpq (Subtype.ext he))
  let a := Nat.chineseRemainderOfFinset (fun p => (x p).val)
    (fun p : Nat.Primes => p.val) S (fun p hp => p.property.ne_zero) hcop
  let M := ∏ p ∈ S, p.val
  have hM : 0 < M := Finset.prod_pos (fun p hp => p.property.pos)
  refine ⟨a.val + (N+1)*M, ?_, ?_⟩
  · have hbound := Nat.mul_le_mul_left (N+1) (Nat.succ_le_iff.mpr hM)
    simp only [Nat.mul_one] at hbound
    omega
  · intro p hp
    have hzero : (M : ZMod p.val) = 0 :=
      (ZMod.natCast_eq_zero_iff M p.val).2 (Finset.dvd_prod_of_mem _ hp)
    have ha : (a.val : ZMod p.val) = x p := by
      rw [← ZMod.natCast_zmod_val (x p)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (a.property p hp)
    simpa only [Nat.cast_add, Nat.cast_mul, hzero, mul_zero, add_zero] using ha

theorem exists_cofinal_crt_sequence (x : (p : Nat.Primes) → ZMod p.val) :
    ∃ a : ℕ → ℕ, (∀ k, k < a k) ∧ Tendsto a atTop atTop ∧
      Tendsto (fun k => fun p : Nat.Primes => (a k : ZMod p.val)) atTop (𝓝 x) := by
  classical
  choose a ha hm using
    (fun k => finite_crt_large ((Finset.range (k+1)).subtype Nat.Prime) x k)
  refine ⟨a, ha, tendsto_atTop_mono (fun k => (ha k).le) tendsto_id, ?_⟩
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop p.val] with k hk
  exact (hm k p (Finset.mem_subtype.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))).symm

theorem dense_positive_integers :
    DenseRange (fun n : {n : ℕ // 1 ≤ n} =>
      fun p : Nat.Primes => (n.val : ZMod p.val)) := by
  intro x
  obtain ⟨a, ha, htop, hcrt⟩ := exists_cofinal_crt_sequence x
  exact mem_closure_of_tendsto hcrt (Eventually.of_forall (fun k =>
    ⟨⟨a k, by have := ha k; omega⟩, rfl⟩))


theorem continuous_extension_unique
    (F G : C((p : Nat.Primes) → ZMod p.val, ℝ))
    (h : ∀ n : ℕ, 1 ≤ n →
      F (fun p => (n : ZMod p.val)) = G (fun p => (n : ZMod p.val))) : F = G := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨a, ha, htop, hcrt⟩ := exists_cofinal_crt_sequence x
  have hf := F.continuous.continuousAt.tendsto.comp hcrt
  have hg := G.continuous.continuousAt.tendsto.comp hcrt
  have he : (fun k => F (fun p => (a k : ZMod p.val))) =
      (fun k => G (fun p => (a k : ZMod p.val))) := by
    funext k
    exact h _ (by have := ha k; omega)
  simp only [Function.comp_def] at hf hg
  rw [he] at hf
  exact tendsto_nhds_unique hf hg


section UniformExtension
local instance residueUniformSpace (p : Nat.Primes) : UniformSpace (ZMod p.val) := ⊥

def positiveEmbedding (n : {n : ℕ // 1 ≤ n}) : (p : Nat.Primes) → ZMod p.val :=
  fun _ => n.val

@[instance_reducible] def positiveCongruenceUniformity : UniformSpace {n : ℕ // 1 ≤ n} :=
  UniformSpace.comap positiveEmbedding inferInstance

local instance : UniformSpace {n : ℕ // 1 ≤ n} := positiveCongruenceUniformity
local instance : TopologicalSpace {n : ℕ // 1 ≤ n} :=
  positiveCongruenceUniformity.toTopologicalSpace

def CRTUniformContinuous {Y : Type*} [UniformSpace Y]
    (f : {n : ℕ // 1 ≤ n} → Y) : Prop :=
  UniformContinuous f

/-- The prime-residue product realizes the abstract completion universal object. -/
def positiveCRTCompletion : AbstractCompletion {n : ℕ // 1 ≤ n} where
  space := (p : Nat.Primes) → ZMod p.val
  coe := positiveEmbedding
  uniformStruct := inferInstance
  complete := by
    let (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩
    infer_instance
  separation := inferInstance
  isUniformInducing := ⟨rfl⟩
  dense := dense_positive_integers

/-- Canonical equivalence with Mathlib's completion, from its universal property. -/
def positiveCRTCompletionEquiv :
    UniformSpace.Completion {n : ℕ // 1 ≤ n} ≃ᵤ ((p : Nat.Primes) → ZMod p.val) :=
  UniformSpace.Completion.cPkg.compareEquiv positiveCRTCompletion

variable {Y : Type*} [UniformSpace Y] [CompleteSpace Y] [T0Space Y]

theorem exists_unique_extension_of_uniformContinuous
    (f : {n : ℕ // 1 ≤ n} → Y) (hf : CRTUniformContinuous f) :
    ∃! F : C((p : Nat.Primes) → ZMod p.val, Y),
      ∀ n, F (positiveEmbedding n) = f n := by
  have he : IsUniformInducing positiveEmbedding := ⟨rfl⟩
  have hd : DenseRange positiveEmbedding := dense_positive_integers
  let F : C((p : Nat.Primes) → ZMod p.val, Y) :=
    ⟨(he.isDenseInducing hd).extend f,
      (uniformContinuous_uniformly_extend he hd hf).continuous⟩
  refine ⟨F, ?_, ?_⟩
  · intro n
    exact uniformly_extend_of_ind he hd hf n
  · intro G hG
    apply ContinuousMap.coe_injective
    exact (uniformly_extend_unique he hd hG G.continuous).symm

theorem exists_extension_iff_uniformContinuous
    (f : {n : ℕ // 1 ≤ n} → Y) :
    (∃ F : C((p : Nat.Primes) → ZMod p.val, Y),
      ∀ n, F (positiveEmbedding n) = f n) ↔ CRTUniformContinuous f := by
  constructor
  · rintro ⟨F, hF⟩
    let (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩
    have he : IsUniformInducing positiveEmbedding := ⟨rfl⟩
    have hu := (CompactSpace.uniformContinuous_of_continuous F.continuous).comp
      he.uniformContinuous
    have heq : (fun n => F (positiveEmbedding n)) = f := funext hF
    change UniformContinuous f
    simpa only [Function.comp_def, heq] using hu
  · intro hf
    exact (exists_unique_extension_of_uniformContinuous f hf).exists
end UniformExtension

end RiemannResearch.NumberTheory.PrimeResidueTopology

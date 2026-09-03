# Serre II — E7 affine corestriction/twist-edge continuation handoff

Date: 2026-09-02

Continuation updated: 2026-09-03

Base repository checkpoint: `6520d5c6cd4b068a6e4e2a6bae337145e6c55518`

## Status

A significant exact reduction has been reached and formally checked. The full E7 case of Serre II is **not** proved. The hard index-eight trialitarian boundary is now reduced, in characteristic different from two, to a concrete affine incidence problem for quaternion classes in one corestriction fibre.

The key correction to the preceding handoff is that existence of a quaternion point in the prescribed corestriction fibre is not an extra open problem in the intended `cd₂(F) ≤ 2`, characteristic-not-two setting. Lam–Leep–Tignol, Theorem 5.12, supplies it.

## Exact field-theoretic reduction

Let `F` have characteristic different from two and `cd₂(F) ≤ 2`. Let `α, β ∈ Br₂(F)` satisfy `ind(α) = ind(β) = ind(α + β) = 4`.

For every quadratic field `K = F(√d)`, Lam–Leep–Tignol, Theorem 5.12, gives a quaternion `r₀ ∈ Br₂(K)` with `cor(r₀) = α`: its obstruction `α ∪ (d) ∈ H³(F, μ₂)` vanishes under `cd₂(F) ≤ 2`.

Arason exactness gives `ker(cor) = im(res)`, hence `cor⁻¹(α) = r₀ + res Br₂(F)`. Define

```text
L_K(r₀) = {γ ∈ Br₂(F) | r₀ + res(γ) is quaternion over K}.
```

The desired prescribed linked factorization is exactly

```text
∃ γ,  γ ∈ L_K(r₀)  and  γ + β ∈ L_K(r₀).
```

This `β`-edge condition is independent of the basepoint. Conjugation gives `L_K(r₀) + α = L_K(r₀)`, so every edge occurs in an affine square with directions `α` and `β`.

Primary source: [Lam–Leep–Tignol, Theorem 5.12](https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf).

## Split branch and global bridge

For `K = F × F`, the linked lift is exactly the earlier four-quaternion completion problem; the split branch adds no flexibility. The corrected dependent witness allows the field, transfer model, quaternion predicate, and constructor to vary with each hard triple.

## Finite obstruction model

A checked finite `F₂³` transfer model has the hard `(4,4,4)` row, `ker(cor) = im(res)`, a quaternion basepoint over `α`, and an ordinary two-quaternion factorization of `res(β)`, but no prescribed-corestriction linked lift.

This is not a field/Brauer counterexample. It proves that the additive, index, exactness, and ordinary-factorization axioms alone cannot force the missing edge.

## Embedded-β affine-slot normal form

Assume characteristic different from two and choose a quadratic field `K/F` embedded in the division representative `D_β`. Then `ind(β_K) = 2`. The desired quaternion factorization exists exactly when there are `e,t ∈ K×` and `x,c ∈ F×` with

```text
β_K = (e,t)_K,
α   = (N(e),x)_F + (-c,N(e+c))_F.
```

Writing `n = N(e)` and `τ = Tr(e)`, the second line is `α = (n,x)_F + (-c,n + cτ + c²)_F`. The square class of `e` is nontrivial and non-descended. The audited identity is

```text
cor(e,e+c) = (N(e),c) + (-c,N(e+c)).
```

Conversely take `z = (x/c)(e+c)`, `r = (e,z)`, and `s = (e,zt)`.

For the third quaternion, put `E = K(√e)`, `E′ = K(√σe)`, and `L = EE′`. A compatible hard solution forces `[L:F] = 8`, makes `L/F` dihedral, and makes `L` a maximal subfield of the degree-eight division representative of the total class. Within this ansatz, compatibility reduces to one `E/K` norm condition and one `K/F` norm condition. Existence is still open.

## Lean artifacts

New modules:

```text
RiemannResearch/E7/E7IndexEightCorestrictionAffineReduction.lean
RiemannResearch/E7/E7IndexEightCorestrictionFiniteCountermodel.lean
```

Key declarations:

```text
RiemannResearch.E7.QuaternionTrialityPacket.splitLinkedLift_iff_quaternionCompletion
RiemannResearch.E7.QuaternionTrialityPacket.corestrictionFiber_iff_exists_restrictedTwist
RiemannResearch.E7.QuaternionTrialityPacket.hasCorestrictionLinkedQuaternionLift_iff_twist_edge
RiemannResearch.E7.QuaternionTrialityPacket.mem_quaternionTwistLocus_add_corestriction_iff
RiemannResearch.E7.QuaternionTrialityPacket.e7IndexEightRealizationGoal_of_variableCorestrictionLinkedRealizations
RiemannResearch.E7.QuaternionTrialityPacket.FiniteCountermodel.hardIndexEight_noPrescribedCorestrictionLift
```

Both modules have zero Lean diagnostics; the affected-module build passed. Source scans found no `sorry`, `admit`, local axioms, unsafe declarations, or native-code proof shortcuts. The aggregate import and theorem catalog were updated.

## Exact remaining target

For every hard triple, prove that some quadratic field `K/F` and basepoint `r₀` satisfy `∃ γ ∈ L_K(r₀), γ + β ∈ L_K(r₀)`.

Next: solve the embedded-β affine-slot equation; impose the dihedral maximal-subfield condition; discharge the `E/K` and `K/F` norm conditions; instantiate the actual Brauer/common-discriminant constructor in Lean; and separately handle characteristic two.

## Continuation update: fixed common slot and gauge quotient

This continuation produced two further exact Lean reductions.

Choose `K/F` to split the middle quaternion `q₂`. Then `β_K=(q₁)_K` is quaternion, and the linked-lift problem is exactly

```text
∃ r ∈ Br₂(K), cor(r)=q₂+q₃,
  r, (q₁)_K, and r+(q₁)_K are quaternion.
```

Thus the field-theoretic gap is

```text
cor⁻¹(α) ∩ Quat(K) ∩ (β_K + Quat(K)) ≠ ∅.
```

It is a prescribed common-slot theorem. Because `ind(α)=4`, a quaternion `r/K` with `cor(r)=α` has no quadratic `F`-subalgebra disjoint from `K`; therefore a slot shared with the descended quaternion `β_K` must be genuinely non-descended. See [Becher--Grenier-Boley--Tignol, Theorem 0.1](https://arxiv.org/pdf/1610.06096).

If instead `K` splits `q₁`, then `β_K=(q₂)_K`. An LLT preimage `r` of `α=q₂+q₃` satisfies `r+σr=(q₂)_K+(q₃)_K`; the missing edge is exactly an equivariant common-slot move from this conjugate decomposition to the descended decomposition `((q₂)_K,(q₃)_K)`.

More intrinsically, in the hard branch with `ind(β_K)≤2`, the linked lift is equivalent to the existence of a separable quadratic `E/K` such that

```text
β_E=0
and
α ∈ cor_{K/F}(Br(E/K)),
```

where `Br(E/K)=ker(Br(K)→Br(E))`. Indeed, every relative class for a quadratic extension is a cyclic quaternion `(E/K,z)`; two such classes add by multiplying their slots. Conversely, Albert--Draxl gives a common quadratic field for the two linked quaternion factors. See Gille--Szamuely, Corollaries 4.4.6 and 4.7.4, and [Albert, *Tensor products of quaternion algebras*](https://doi.org/10.2307/2038442). This is the sharp nested-quadratic target: a dihedral field lattice alone does not supply the two labelled conditions.

Define a gauge relation on base twists by

```text
γ ~ δ  iff  res(γ)=res(δ) or res(γ)=res(δ+α).
```

Under exponent two this is a setoid. The quaternion-twist predicate descends to `Br₂(F)/(ker(res)+⟨α⟩)`, and the linked lift is exactly a `[β]`-edge in that quotient locus. Translation by `[β]` is involutive. Before quotienting, the same condition is the full affine square with vertices `γ`, `γ+α`, `γ+β`, and `γ+α+β`.

## Aligned common-slot staging

A non-descended slot can be staged unconditionally from `q₁,q₂`:

1. Write `q₂=(d,b)` and take `K=F(√d)`.
2. From `I³(F)=0`, choose `p` represented by both the trace-zero square form `⟨d,b,-db⟩` of `q₂` and the norm form `⟨1,-d⟩` of `K/F`.
3. Then `q₂=(p,x)` and `p=N(w)` for some `w∈K×`. Put `M=F(√p)`.
4. Universality of the norm form of `q₁` and the constructive proof of [Lam--Leep--Tignol, Proposition 5.4](https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf#page=28) give `a,s∈F×` with `(q₁)_K=(aw,s)`. The slot `aw` is genuinely non-descended.

Fix these data and set

```text
c_t=N_{K/F}(t-w)=t²-t Tr(w)+p.
```

Every viable candidate sharing this selected slot has the form `r=(aw,xy(t-w))_K` with `t,y∈F×`, and

```text
cor(r)=q₂+(p,y)+(a,c_t)+(t,p c_t).
```

Hence the exact condition for this selected slot is

```text
∃ t,y∈F×, q₃=(p,y)+(a,c_t)+(t,p c_t).
```

Equivalently, after restricting to `M=F(√p)`,

```text
∃ t∈F×, (q₃)_M=(at,c_t)_M.
```

The converse uses `ker(Br₂(F)→Br₂(M))={(p,y):y∈F×}`. This is an exact one-parameter incidence for the staged slot and a sufficient criterion for the original linked-lift problem. It is not yet exhaustive: a converse for arbitrary lifts needs a normalization theorem forcing the first summand of the general corestriction form to equal `q₂`.

The special choice `t=y=1` gives `q₃=(a,N(1-w))`. If `q=N(1-w)`, then

```text
Tr(w)=1+p-q,
(1+p-q)²-4p=(1-p-q)²-4pq ∈ dF×².
```

## Automatic dihedral maximal splitting field

A separate unconditional consequence is now available. Choose any nonsquare slot `p` of `q₂`, put `M=F(√p)`, and let `A=q₁+q₃`. Hardness makes `A` a division biquaternion. Since `H³(F,μ₂)=0`, [Lam--Leep--Tignol, Theorem 5.12](https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf#page=33) supplies a quartic 2-extension `E/F` of discriminant `p` splitting `A`. LLT Proposition 3.3 says its Galois hull `L` contains `M` and has degree at most eight. It therefore splits both `A` and `q₂`, hence `q₁+q₂+q₃`. Index divisibility forces `[L:F]=8`, excluding the cyclic-quartic alternative. Thus `L/F` is dihedral of order eight and embeds as a maximal subfield of the degree-eight division representative.

This proves existence of a dihedral maximal subfield in the characteristic-not-two, `cd₂≤2` hard case. It does not alone produce the prescribed linked pair or E7 boundary object: a further bridge must preserve the three packet invariants, not merely the total Brauer class.

The obstruction is structural: replacing every `qᵢ` by `qᵢ+δ` leaves all pairwise packet classes unchanged in exponent two, while the total class changes from `T` to `T+δ`. Thus a maximal field of the total class is not packet data. For the LLT hull aligned with a slot of `q₁`, the unresolved condition remains linkage of the chosen preimage `r` with `(q₂)_K`.

The dihedral lattice does contain related linkage, but over the wrong quadratic field. If `F⊂K₀⊂E` is the quadratic tower inside the quartic splitter, LLT Theorem 4.7 links `(q₂)_{K₀}` and `(q₃)_{K₀}`. The prescribed-corestriction preimage lives instead over the discriminant field `M`, where it must link to `(q₂)_M`. The unresolved step is transporting or aligning this slot across the two quadratic subfields of the dihedral hull. Equivalently, among the three quadratic subextensions `U/M` of the dihedral hull, one must find one satisfying both `q₂_U=0` and `α∈cor_{M/F}(Br(U/M))`.

## Corrected norm obstruction

For fixed non-descended `e`, set `E=K(√e)`, `f=σ(e)`, and `A=(q₃)_K`. If `A` splits over `K(√e,√f)`, LLT Proposition 5.2 supplies adapted decompositions `A=(e,u)+(f,v)`. The equation

```text
A=(e,bz)+(f,σz)
```

has a solution exactly when **some** adapted pair satisfies `u/(bσ(v))∈N_{E/K}(E×)`, equivalently `(e,uσ(v))=(e,b)`. The existential quantifier over adapted decompositions is essential.

Once `z` exists, let

```text
δ_z=α+cor(e,z),
S_e={λ∈K× | (e,λ)+(σe,σλ)=0},
ρ_e(λ)=cor(e,λ).
```

The final obstruction is the canonical class

```text
[δ_z] ∈ Br(K/F)/im(ρ_e).
```

Its vanishing is independent of `z` and is equivalent to the full corestriction equality. Ordinary corestriction surjectivity is too weak; the sharp target is the fixed-slot subgroup. Cyclic relative Brauer theory gives `Br(K/F)≅F×/N_{K/F}(K×)`; see Gille--Szamuely, Corollaries 4.4.6--4.4.7.

## Literature boundary

No published theorem was found that forces the required `β`-edge.

- LLT Theorem 5.12 supplies some quaternion in the corestriction fibre but does not prescribe linkage to `β_K`.
- LLT Theorem 4.7 needs an extra quartic splitting/isotropy hypothesis.
- [Barry--Chapman, Theorem 4.6](https://arxiv.org/pdf/1501.03831#page=9) links already existing presentations but does not preserve corestriction.
- Failure of property `D(2)` even at `cd₂=2` rules out a generic norm-selection shortcut.
- [Barry, Theorem 3.3](https://arxiv.org/pdf/1304.2620) gives a decomposition adapted to the central biquadratic field of a dihedral maximal subfield. Comparing it with the original triple is promising but does not yet prove the edge.

## New Lean declarations

Added to `E7IndexEightCorestrictionAffineReduction.lean` and the theorem catalog:

```text
QuaternionLinkedPair
hasCorestrictionLinkedQuaternionLift_iff_linkedPair_of_restriction_quaternion
hasCorestrictionLinkedLiftForTriple_iff_middleSplittingLinkedPair
hasCorestrictionLinkedLiftForTriple_iff_firstSplittingLinkedPair
HasQuaternionTwistSquare
hasCorestrictionLinkedQuaternionLift_iff_twist_square
TwistGaugeEquivalent
TwistGaugeSetoid
TwistGaugeQuotient
QuaternionTwistQuotientLocus
twistGaugeQuotientTranslate
twistGaugeQuotientTranslate_involutive
hasCorestrictionLinkedQuaternionLift_iff_quotientTwistEdge
```

The module import checks and full `lake build RiemannResearch --quiet` pass. No `sorry`, `admit`, local axiom, unsafe declaration, or native shortcut was introduced.

## Exact next targets

1. Prove `(q₃)_M=(at,N(t-w))_M` for some staged choices, or make the staged family exhaustive.
2. In the automatic dihedral hull, find a quadratic `U/M` with `q₂_U=0` and `α∈cor_{M/F}(Br(U/M))`.
3. Compare Barry's adapted decomposition with the original triple.
4. Kill the canonical class in `Br(K/F)/im(ρ_e)`.
5. Instantiate the Brauer/common-discriminant constructor in Lean and treat characteristic two.

## Continuation state

This is another significant reduction. The four-hour continuation automation remains enabled and should continue these targets rather than pausing at this milestone.

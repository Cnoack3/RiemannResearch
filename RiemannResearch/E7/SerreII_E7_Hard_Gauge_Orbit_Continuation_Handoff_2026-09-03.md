# Serre II — E7 hard gauge-orbit continuation handoff

Date: 2026-09-03

Starting checkpoint: `96cefc72e4d69cc7fc64309e0975159bf0f25ef4`

## Status

Full Serre II and the hard inner E7 case remain open. The project now composes
per-triple linked-corestriction witnesses into the abstract E7 realization
goal, but constructing those field-theoretic witnesses remains decisive.

This continuation closes the two non-splitting assumptions in the
gauge-quotient reduction. For a quadratic field extension, use

```text
res_M(x) = 0  =>  ind(x) <= 2.
```

The Lean predicate recording exactly this input is
`QuadraticRestrictionKernelHasIndexAtMostTwo I T`. In the intended field
model it follows from the theorem that the index of a central simple algebra
divides the degree of every finite splitting field (Stacks Project,
Lemma 11.8.4, tag 074X): <https://stacks.math.columbia.edu/tag/074X>.

## New hard-index discharge

Let `q₁,q₂,q₃` be quaternion classes with
`ind(q₁+q₂+q₃)=8`, and let `M/F` be quadratic with `(q₂)_M=0`.
The verified packet-index theorem gives

```text
ind(q₁+q₂) = ind(q₁+q₃) = 4.
```

Lean now derives

```text
(q₁)_M != 0
and
(q₁+q₃)_M != 0.
```

If `q₁_M=0`, then `(q₁+q₂)_M=0`, contradicting the degree-two
splitting bound and index four. The second contradiction applies the same
bound directly to the index-four class `q₁+q₃`.

Thus the hard field row itself makes translation by
`β=q₁+q₂` fixed-point-free on the gauge quotient for
`α=q₂+q₃`; no separate non-splitting assumptions remain.

## Exact nondegenerate-orbit endpoint

Under exponent two, middle exactness, conjugation stability, a quaternion
basepoint `r₀` with `cor(r₀)=α`, and the hard hypotheses, Lean proves

```text
HasCorestrictionLinkedLiftForTriple T Q_B q₁ q₂ q₃
  iff
the quotient quaternion locus contains q and translate_β(q),
with translate_β(q) != q.
```

Since `translate_β` is involutive, the endpoints form a genuine
two-element orbit.

New module:
`RiemannResearch/E7/E7IndexEightCorestrictionHardOrbit.lean`.

New declarations:

```text
QuadraticRestrictionKernelHasIndexAtMostTwo
totalIndexEight_middleSplitting_restrictions_nonzero
totalIndexEight_middleSplitting_twistGaugeQuotientTranslate_fixedPointFree
HasNondegenerateQuaternionTwistQuotientEdge
totalIndexEight_middleSplitting_linkedLift_iff_nondegenerateQuotientEdge
```

## Correct remaining field problem

Because `q₁_M` is a non-split quaternion class, the corrected quadratic
layer `U/M` must be a genuine quadratic splitting field for `q₁_M`.
Simultaneously it must satisfy

```text
q₁_U = 0,
q₂+q₃ ∈ cor_{M/F}(Br(U/M)).
```

The new index argument proves that `U` cannot collapse to the already
chosen middle-splitting layer. It does not prove that a quadratic layer in an
LLT dihedral hull has both required labels.

Relevant published inputs:

- Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*,
  Publ. Math. IHÉS 77 (1993), Theorems 5.10 and 5.12:
  <https://www.numdam.org/articles/10.1007/BF02699188/>.
- D. Barry, *Decomposable and Indecomposable Algebras of Degree 8 and
  Exponent 2*, Theorem 3.3:
  <https://arxiv.org/abs/1304.2620>.

Neither source, as currently applied, forces the labelled alignment.

## Staged-slot normalization

For `s=Tr(w)` and `p=N(w)`, Wolfram independently checked

```text
N(t-w) = t²-s t+p,
disc = s²-4p,
4 N(t-w) = (2t-s)²-(s²-4p).
```

This confirms that the staged parameter is a translated-square conic. It
does not solve the coupled norm-coset condition

```text
(q₃)_M = (a t, N(t-w))_M,
```

or, after fixing `(q₃)_M=(at,c)_M`,

```text
N(t-w)/c ∈ N_{M(sqrt(at))/M}(M(sqrt(at))×).
```

## Highest-leverage continuation

1. Prove or refute the labelled-layer theorem: among the quadratic
   `U/M` compatible with an LLT quartic/dihedral presentation of
   `α=q₂+q₃`, one splits the division quaternion `q₁_M`.
2. Re-express the alignment as an intersection of the maximal-subfield conic
   of `q₁_M` with the relative-corestriction parameter space for `α`.
3. Use `I³(F)=0` only at this intersection; ordinary corestriction
   surjectivity and existence of a dihedral hull are separately insufficient.
4. Compare Barry's biquadratic-adapted decomposition with the fixed labels
   `q₁` and `q₂+q₃`.
5. Treat characteristic two separately after the characteristic-not-two
   orbit problem is settled.

This is a conditional research reduction, not Full Serre II. The existence of
the nondegenerate orbit, the common-discriminant constructor, and the passage
to actual nonabelian H¹ neutrality remain open.

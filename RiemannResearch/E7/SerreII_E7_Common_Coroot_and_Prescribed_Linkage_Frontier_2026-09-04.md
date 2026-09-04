# Serre II for E7: common-coroot and prescribed-linkage frontier

**Date:** 2026-09-04

## 1. Status

The hard case of Serre's Conjecture II for an inner simply connected group of
type E7 with Tits algebra of index 8 remains open over arbitrary perfect
fields of cohomological dimension at most 2.

This continuation does not prove that case. It does four narrower things:

1. repairs the characteristic-not-2, H3-vanishing construction of a
   nonnormal quartic splitting two prescribed quaternion labels;
2. identifies the exact fixed-layer affine obstruction left by that
   construction;
3. formalizes the affine fibre, its direction group, and the exact
   layer-constrained linked-lift equivalence in Lean;
4. isolates the genuinely E7-specific common-coroot theorem still required.

Gille's reduction identifies the unresolved index-eight case and gives the
common-coroot criterion. Later general Serre-II results still exclude E7.

Primary status references:

- Philippe Gille, Serre's Conjecture II, pp. 16-17:
  https://math.univ-lyon1.fr/~gille/prenotes/kruen_gille.pdf
- Diego Izquierdo and Giancarlo Lucchini Arteche:
  https://arxiv.org/pdf/2308.00903

## 2. Repaired LLT common lower quartic

Assume char(F) is not 2 and

\[
H^3(F,\mu_2^{\otimes 3})=0.
\]

Let q1, q2, q3 be quaternion Brauer classes with

\[
\operatorname{ind}(q_1+q_2+q_3)=8,
\]

and choose a quadratic field M = F(sqrt(d)) splitting q1.

The H3 vanishing implies that the norm Pfister form of q2 represents d.
Choose x = r+y in q2 with Trd(y)=0 and

\[
\operatorname{Nrd}(x)=r^2-y^2=d.
\]

With a = y^2, the field K = F(sqrt(a)) embeds in and splits q2, while

\[
d=N_{K/F}(r+y).
\]

The same H3 vanishing makes d a reduced norm from q3. Lam-Leep-Tignol
Theorem 4.2 then supplies a quadratic L/K, quartic over F, with discriminant
field M and splitting q3. Since K splits q2, L splits both prescribed base
classes q2 and q3.

Moreover K is not M. If M split q2 as well as q1, then the standard index
inequality would give

\[
8=\operatorname{ind}(q_1+q_2+q_3)
  \mid 2\operatorname{ind}((q_3)_M)\le 4,
\]

a contradiction. LLT Proposition 3.3 therefore makes L/F nonnormal with
dihedral normal hull.

Source: Lam-Leep-Tignol, Theorem 4.2 and Propositions 3.3 and 5.4:
https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf

This argument is not a characteristic-2 argument.

## 3. Tignol's correction: two different splitting statements

Let U/M be the quadratic member dual to L/F in the dihedral hull. Tignol's
Example 5.3 literally contains an extra symbol term (K/F,x). It is absorbed,
rather than omitted, by the projection formula:

\[
(K/F,x)=\operatorname{Cor}_{M/F}(U/M,x),
\]

and the class (U/M,x) is U-split. Consequently,

\[
\operatorname{Br}_2(L/F)=
\operatorname{Cor}_{M/F}
\ker\bigl(\operatorname{Br}(M)[2]\to\operatorname{Br}(U)[2]\bigr).
\]

Since L splits q2 and q3, there are M-classes s and t with

\[
s_U=t_U=0,\qquad
\operatorname{Cor}_{M/F}(s)=q_2,\qquad
\operatorname{Cor}_{M/F}(t)=q_3.
\]

The wording must remain exact:

- the lower quartic L splits the base labels q2 and q3;
- the upper quadratic U/M splits the selected M-lifts s and t;
- it does not follow that U splits (q2)_M or (q3)_M.

Source: Jean-Pierre Tignol, especially Example 5.3:
https://arxiv.org/abs/1704.04072

## 4. Exact fixed-layer affine fibre

Put alpha = q2+q3 and beta = q1+q2. Define

\[
\mathcal F_U(\alpha)=
\{r\in\operatorname{Br}(M)[2]:
  r_U=0,\ \operatorname{Cor}_{M/F}(r)=\alpha\}.
\]

The class s+t proves that this fibre is nonempty. Its direction group is

\[
D_U=
\ker(\operatorname{Br}(M)[2]\to\operatorname{Br}(U)[2])
\cap\ker(\operatorname{Cor}_{M/F}).
\]

For any basepoint r0 in the fibre, every fibre point is uniquely r0+delta
with delta in D_U. The remaining fixed-layer assertion is exactly

\[
\exists r\in\mathcal F_U(\alpha),\qquad
\operatorname{ind}\bigl(r+\operatorname{res}_{M/F}(\beta)\bigr)\le 2.
\]

Equivalently, one needs a direction correction delta in D_U for which

\[
\operatorname{ind}\bigl(
  r_0+\delta+\operatorname{res}_{M/F}(\beta)\bigr)\le 2.
\]

Neither LLT nor Tignol forces this quaternion point.

## 5. Why an unrestricted linked lift is weaker

LLT Theorem 5.12 gives, under H3 vanishing, a quaternion Q/M such that

\[
\operatorname{Cor}_{M/F}(Q)=\alpha.
\]

It does not force Q to be linked to (q2)_M, equivalently

\[
\operatorname{ind}(Q+(q_2)_M)\le 2.
\]

Even if such a linked Q exists, its common quadratic splitter P/M need not be
the upper layer dual to the prescribed lower quartic L. The dual lower
quartic need only split alpha. Separate splitting of q2 and q3 requires the
stronger incidence

\[
q_2\in
\operatorname{Cor}_{M/F}
\ker(\operatorname{Br}(M)[2]\to\operatorname{Br}(P)[2]).
\]

Thus the relaxed moving-layer condition is necessary for the chosen route,
not sufficient for its prescribed-dual incidence.

The obstruction is genuinely an index-4/common-slot problem. Cohomological
dimension 2 alone does not make all quaternion pairs linked; see
Becher-Hoffmann, Theorem II:
https://www.math.uni-bielefeld.de/lag/man/227.pdf

## 6. The genuinely E7-specific target

For an inner simply connected E7-group G, let C(G) be the quaternion Brauer
classes admitted by its relevant minuscule-coroot embeddings

\[
\mathrm{SL}_1(Q)\longrightarrow G.
\]

For z in H1(F,G), Gille's criterion is

\[
z=1\quad\Longleftrightarrow\quad
C(G)\cap C({}^{z}G)\ne\varnothing.
\]

The right remaining theorem is therefore a common-coroot theorem. A raw
three-quaternion packet forgets coroot effectivity, the orthogonal
involution/gift data, and the equivariant descent relation between G and its
twist.

A concrete next lemma is a prescribed equivariant D6/Fano decomposition
statement. In the actual index-eight E7 datum, after choosing a minuscule
quaternion q1 and a quadratic M/F splitting it, construct a Galois-stable
decomposition containing the prescribed q2_M and q3_M and a quaternion
vertex r such that

\[
\operatorname{Cor}_{M/F}(r)=q_2+q_3,\qquad
\tau(r)=r+(q_2+q_3)_M,
\]

\[
\operatorname{ind}(r+(q_2)_M)\le2,
\]

with the resulting vertex effective as a minuscule coroot of the twist.

Known decomposition-group and Fano results do not supply prescribed
membership, non-descended Galois action, exact corestriction normalization,
and coroot effectivity simultaneously. Petrov-Semenov compares two points
of the same anisotropic E7 variety; it does not compare G with its twist:
https://arxiv.org/pdf/2208.13730

## 7. Lean formalization and scope

The module

RiemannResearch/E7/E7IndexEightPrescribedDualCommonSplitter.lean

contains the abstract reduction, including:

- HasPrescribedDualCommonSplitter;
- CanonicalCrossedFibre;
- CanonicalCrossedDirection;
- mem_canonicalCrossedFibre_iff_existsUnique_direction;
- exists_quaternionPoint_iff_exists_directionCorrection;
- HasLayerKernelCorestrictionLinkedQuaternionLift;
- exists_quaternionPoint_iff_hasLayerKernelCorestrictionLinkedQuaternionLift;
- hasCrossedQuaternionKernelRectangle_iff_hasLayerKernelLinkedLift.

The LLT field construction is not formalized in that module:
HasPrescribedDualCommonSplitter remains an input interface.

The finite module

RiemannResearch/E7/E7IndexEightPrescribedDualFiniteNoGo.lean

proves that one explicit F2 transfer model has prescribed dual detection and
a nonempty corestriction fibre but no quaternion translate. It now also
states the failure directly as

no_layerKernelCorestrictionLinkedQuaternionLift.

This is a countermodel to an abstract implication from the recorded additive,
transfer, index, and fixed-layer axioms. It is not a field, not a
counterexample to E7, and not a counterexample to Serre II. It also rules out
only this fixed layer, not every possible dual layer.

Finally,

RiemannResearch/AlgebraicGeometry/SerreIIE7PacketEffectivityBridge.lean

is conditional assembly. Its packet structure already contains branchwise
neutrality maps. The module transports supplied packet effectivity to the
existing H1-neutrality endpoint; it does not prove packet effectivity or a
common-coroot theorem.

## 8. Frontier

The missing implication is

\[
\text{actual E7 D6/Fano geometry}
\Longrightarrow
\text{a quaternion point in the prescribed affine fibre}
\Longrightarrow
C(G)\cap C({}^{z}G)\ne\varnothing.
\]

Any completion must use E7 coroot, involution/gift, or equivariant descent
information absent from the current abstract Brauer-transfer model.

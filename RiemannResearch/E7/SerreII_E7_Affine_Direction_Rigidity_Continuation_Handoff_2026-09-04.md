# Serre II E7 affine-direction rigidity continuation handoff

Date: 2026-09-04

## Scope and status

This continuation advances the hard index-eight E7 packet problem but does not
prove E7 Serre II.  The terminal H¹ bridge remains conditional on genuine
torsor-to-packet geometry and packet effectivity.

The prescribed LLT--Tignol common-splitter reduction leaves the canonical
affine fibre

\[
\mathcal F_U(q_2+q_3)
 = \{r\in \operatorname{Br}_2(M):
       r_U=0,\ \operatorname{cor}_{M/F}(r)=q_2+q_3\}
\]

and asks for a point satisfying

\[
\operatorname{ind}
  \bigl(r+\operatorname{res}_{M/F}(q_1+q_2)\bigr)\le 2.
\]

The exact direction group of this fibre is

\[
D_U=\ker(\operatorname{res}_{U/M})
       \cap\ker(\operatorname{cor}_{M/F}).
\]

## New exact reduction

The module
`RiemannResearch/E7/E7IndexEightPrescribedDualCommonSplitter.lean`
now proves three additional structural theorems.

1. `exists_nonzero_directionCorrection_of_basepoint_not_quaternion`:
   if a basepoint \(r_0\in\mathcal F_U(q_2+q_3)\) has nonquaternion
   translate but some point of the same fibre has quaternion translate, then
   there is a nonzero \(\delta\in D_U\) for which

   \[
   r_0+\delta+\operatorname{res}(q_1+q_2)
   \]

   is quaternion.

2. `exists_quaternionPoint_iff_basepoint_of_trivial_direction`:
   if \(D_U=0\), existence of a quaternion point is equivalent to
   quaternionity of any chosen basepoint translate.

3. `crossedRectangle_forces_nonzero_direction_of_bad_basepoint`:
   under the prescribed dual-common-splitter hypotheses, a crossed quaternion
   rectangle together with one bad explicit basepoint forces such a nonzero
   direction correction.

This turns the fixed-witness index-four calculation into a sharp dichotomy.
On the same chosen quartic layer, a proof must construct a nonzero class in
\(D_U\) that repairs the witness.  If no such direction exists, the only
remaining possibility is to change to the conjugate nonnormal quartic layer.

## Finite obstruction reclassified

The finite transfer model now proves:

- `canonicalCrossedDirection_trivial`;
- `no_quaternionPoint_by_trivialDirection`.

Thus its failure is not merely a failed arbitrary choice: its entire
canonical fibre is rigid.  This remains an abstract finite no-go model, not a
Brauer group of a field and not a counterexample to Serre II.

## Verification

Affected-module diagnostics succeeded with no messages for both modified
Lean modules.  Source-scanned verification succeeded for all five new
declarations with no warnings.  Their reported dependencies are the standard
foundational constants `propext`, `Classical.choice`, and `Quot.sound`;
there are no project-local axioms, `sorry`, `admit`, or unsafe escapes.

The theorem catalog records the new affine-direction frontier.

## Mathematical interpretation and next target

For a quadratic layer \(U/M\), the immediate field-theoretic target is now to
compute or control

\[
D_U=\ker(\operatorname{Br}_2(M)\to\operatorname{Br}_2(U))
       \cap\ker(\operatorname{cor}_{M/F}).
\]

The next useful theorem would do one of the following:

1. prove \(D_U=0\) for the explicit bad LLT layer, thereby excluding that
   layer completely;
2. exhibit a nonzero \(\delta\in D_U\) and prove that it lowers the translated
   index from four to two;
3. prove that the conjugate nonnormal layer has the required quaternion point.

Tignol's relative Brauer-kernel description identifies the ambient
corestriction image but does not select this correction.  Barry's adapted
decompositions and the Becher--Grenier-Boley--Tignol stable-slot theorem remain
the most plausible tools for controlling the intersection.

## References

- Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*,
  Theorem 4.2 and Proposition 3.3:
  <https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>
- Tignol, *Tores associés à une algèbre étale quartique*, Corollary 3.5 and
  Example 5.3: <https://arxiv.org/abs/1704.04072>
- Barry, adapted decompositions of biquaternion algebras:
  <https://arxiv.org/abs/1304.2620>
- Becher--Grenier-Boley--Tignol, stable quadratic slots:
  <https://arxiv.org/abs/1610.06096>

## Publication note

The full Serre II development belongs on the protected archival branch
`serre-ii-archive-20260904`; the repository default branch is now RH-only.
Do not merge the obsolete recovery PR #15 into the default branch.

# Complete dyadic Cesàro energy: checked equivalence and the remaining RH obstruction

Date: 1 November 2026.
Starting repository snapshot: a84cfad2041415e10267cff566974f36289e6eda.
Source agenda: user-provided RH_Cesaro_P_Q_Squarefree_Research_Agenda_2026-11-01 (1).md, especially Priorities 2 and 3.

## Conclusion

RH has not been proved. The agenda's complete dyadic upper estimate has been strengthened to a two-sided comparison and connected to the existing RH consumer in Lean. The same normalized block budget characterizes zero lower logarithmic growth under both latent laws P and Q. The explicit single-repair and mean-neutral two-repair Möbius families have specialized conditional RH endpoints.

The new unconditional results are exact decomposition, summability, scalar and block inequalities, and the signed cumulative formula. They do not supply a new asymptotic cancellation estimate for the actual Möbius family. All RH endpoints below remain **conditional research reductions**.

## 1. Exact complete energy and block normalization

Let z = ζ(2), let g be a real arithmetic input, and write

\[
M_g(n)=\sum_{m=1}^{n}g(m),\qquad
a_n=\frac{2n+1}{z n^3(n+1)^2}.
\]

For the existing Q endpoint law λ_Q(n)=(2n+1)/(z n(n+1)^2),

\[
J_Q(g)=\sum_{n\ge1}\lambda_Q(n)(Cg(n))^2
      =\sum_{n\ge1}a_nM_g(n)^2.
\]

The formal statements require summability. This is discharged automatically for the finite legal inputs used by the RH consumers; it is not inferred from a real-valued totalized infinite sum.

Suppose g(n)=c for 1≤n≤H and c≠0. Put

\[
L_k=(H+1)2^k,\qquad
X_H(g,c)=\sum_{k\ge0}
 \frac{\sum_{n=L_k}^{2L_k-1}M_g(n)^2}{|c|^2L_k^4},
\qquad
A_H=\sum_{n=1}^{H}\lambda_Q(n).
\]

In the Lean definitions, the block budget is first summed without |c|² and is then normalized. Its summability is established before comparison.

The exact identity, before estimating any coefficient, is

\[
\boxed{J_Q(g)=c^2 A_H+
 \sum_{k\ge0}\sum_{n=L_k}^{2L_k-1}a_nM_g(n)^2.}
\]

All blocks appear. The finite head is exact; the existing Q mixture theorem further gives

\[
A_H=\sum_{n=1}^{H}Q(n)-H Q(H+1),\qquad 0\le A_H\le1.
\]

The generic dyadic module proves the finite identity

\[
\sum_{k<K}\sum_{i<N2^k}f(N2^k+i)
=\sum_{n<N2^K}f(n)-\sum_{n<N}f(n),
\]

then proves cofinality and complete regrouping for nonnegative summable series. The infinite equality therefore does not rely on a numerical tail cutoff.

## 2. The strengthened two-sided estimate

For every n≥1,

\[
\frac{2}{z(n+1)^4}\le a_n\le\frac{2}{zn^4}.
\]

For L≤n<2L, the integer endpoint gives n+1≤2L, hence

\[
\frac1{8zL^4}\le a_n\le\frac2{zL^4}.
\]

Summing every block proves

\[
\boxed{\frac{X_H(g,c)}{8z}
 \le \frac{J_Q(g)}{|c|^2}-A_H
 \le \frac{2X_H(g,c)}{z}.}
\]

In particular,

\[
X_H(g,c)\le8z\,\frac{J_Q(g)}{|c|^2},\qquad
\frac{J_Q(g)}{|c|^2}\le1+\frac2zX_H(g,c).
\]

The agenda used

\[
B_{H,k}=\frac{\sum_{n=L_k}^{2L_k-1}M_g(n)^2}{|c|^2L_k^3}.
\]

Its normalization is exactly

\[
X_H(g,c)=\frac1{H+1}\sum_{k\ge0}2^{-k}B_{H,k}.
\]

Thus the weighted aggregate is comparable to the complete tail energy in both directions, rather than being only a convenient sufficient majorant. No optimality theorem for the comparison constants is asserted.

## 3. The P/Q equivalence and precise RH endpoint

For Y_j→∞ and nonzero c_j, with exact heads g_j(n)=c_j for 1≤n≤Y_j, the new theorem proves

\[
\operatorname{lowerLogGrowth}\left(J_Q(g_j)/|c_j|^2,Y_j\right)=0
\quad\Longleftrightarrow\quad
\operatorname{lowerLogGrowth}\left(X_{Y_j}(g_j,c_j),Y_j\right)=0.
\]

The same equivalence with J_P follows from the existing P/Q energy comparison. A new general lemma transports zero lower logarithmic growth through eventual affine bounds E≤C+DF. This handles the finite head without assuming X is bounded below.

The formal definition of lowerLogGrowth uses an extended nonnegative liminf. For cofinal heads and these nonnegative quantities, the condition is

\[
\liminf_{j\to\infty}
\frac{\log(1+X_{Y_j}(g_j,c_j))}{\log Y_j}=0.
\]

For legal g_j, this implies the actual Mathlib RiemannHypothesis. There is no uniform energy bound, no limit at every index, and no uniform positive lower bound on |c_j|.

The declarations are:

- QCesaroDyadicCriterion.normalized_dyadic_lowerLogGrowth_zero_iff
- QCesaroDyadicCriterion.normalized_p_dyadic_lowerLogGrowth_zero_iff
- QCesaroDyadicCriterion.riemannHypothesis_of_dyadic_cumulative_lower_growth
- QCesaroDyadicCriterion.riemannHypothesis_of_mobiusHead_dyadic_lower_growth
- QCesaroDyadicCriterion.riemannHypothesis_of_meanNeutral_dyadic_lower_growth

The general endpoint assumes legality, nonzero amplitudes, exact heads, cofinality, and the displayed growth premise. Its specialized Möbius endpoints discharge legality and exact-head constraints with existing constructions. The growth premise remains Open.

Squarefree repair conductors give the existing literal squarefree-conductor families, including every squarefree composite in the Möbius prefix. The specialized endpoints are stronger in allowing other positive repair conductors too. No assertion is made that Cesàro averaging preserves the unsmoothed squarefree closure.

## 4. Explicit signed remainder for the two-repair family

For H≥1 and H<D<E, retain the existing notation

\[
S_H=\sum_{d\le H}\frac{\mu(d)}d,\quad
M_H=\sum_{d\le H}\mu(d),\quad
\delta_d(n)=\frac{r(d-2-r)}{2d},\quad r=n\bmod d.
\]

Let w_D,w_E be the existing mean-neutral repair weights. Define

\[
R_H(n)=\sum_{d\le H}\mu(d)\delta_d(n)
 -S_H\bigl(w_DD\delta_D(n)+w_EE\delta_E(n)\bigr).
\]

The new unconditional declaration meanNeutralMobiusHead_cumulative proves, for every positive n,

\[
\boxed{M_{g_H^0}(n)=R_H(n).}
\]

It uses both exact constraints w_D+w_E=1 and S_H(w_DD+w_EE)=M_H. The proof first cancels the mean and retains the complete signed remainder.

The new meanNeutral_dyadic_budget_exact then identifies the entire budget with

\[
\sum_{k\ge0}\sum_{n=L_k}^{2L_k-1}\frac{R_H(n)^2}{L_k^4}.
\]

Every prefix-prefix, prefix-repair, and repair-repair cross term is retained inside this square. No diagonal approximation or independence assumption is introduced.

## 5. What blocked an RH proof

The missing provider is an arithmetic estimate for these actual signed cumulative sums, or for a better legal exact-head family:

\[
\boxed{\liminf_j
\frac{\log\left(1+\sum_{k\ge0}L_{j,k}^{-4}
       \sum_{n=L_{j,k}}^{2L_{j,k}-1}R_{H_j}(n)^2\right)}
     {\log H_j}=0.}
\]

The two-sided theorem shows that this is precisely the existing energy-growth obstruction expressed through cumulative sums. It does not remove that obstruction.

The repository already had the period-independent bound |δ_d(n)|≤d/8 and a complete cubic tail certificate for the mean-neutral family. For separated repair conductors comparable to H, the absolute-value coefficient budget is of order H². Squaring this budget and summing n⁻⁴ after H gives only a linear-scale energy upper bound. The same repository memorandum also supplies an unconditional paper-level improvement to o(H), using existing PNT results; that asymptotic assembly is not newly formalized in this development.

Even o(H) is insufficient: H/log(H) is sublinear but its logarithmic growth exponent tends to 1, whereas the checked RH condition requires a zero lower exponent. A uniform primitive bound of H^(3/2+o(1)) would suffice, but is stronger than necessary; the weighted block condition allows localized large values when their complete weighted contribution is small.

Zero period mean controls the distant tail. It does not provide the required cancellation throughout the moving transition region. Conditional iid replication reduces conditional variance; it does not establish this deterministic signed-mean estimate. P/Q comparison transports the obstruction. Finite certificates and exact-head feasibility likewise do not prove the cofinal growth condition.

No RH-equivalent density statement, unproved coefficient estimate, or asserted cancellation has been inserted as an unconditional fact.

## 6. Verification and source map

The coherent development and 11 principal axiom inspections passed in job
job_yofjhWXBJpzeMrM2t4x5Jz07jeITb4y7: verified=true, exit_code=0.
The server reported 6.836 seconds for that development check.

All 11 inspected declarations depend only on propext, Classical.choice, and Quot.sound. The RH declarations still have their displayed domain-specific growth hypotheses; an axiom audit does not discharge theorem hypotheses.

Saved-module import, repeated axiom inspection, and exact-type inspection passed in job job_eYXksy5LSirAy-3hCWiRuc2zghXL0Gd9: verified=true, exit_code=0; reported verification duration 18.902 seconds. This imported the separately saved modules, rather than reusing only an in-memory combined candidate.

Final publication is certified by the enclosing successful server checkpoint, including integrated-source verification if main changes. Neither the development snippet nor the saved-module import is described as a full-project checkpoint.

| Module | Responsibility |
|---|---|
| Analysis/DyadicBlockDecomposition.lean | Exact finite partition, cofinality, grouped summability, complete regrouping |
| Analysis/LowerLogGrowthComparability.lean | Eventual affine comparison for zero lower logarithmic growth |
| RH/QCesaroDyadic.lean | Exact cumulative kernel, full block inequalities, exact head decomposition, normalized comparison |
| RH/SquarefreeMobiusCesaroEnergy.lean | Explicit mean-neutral signed remainder and exact cumulative formula |
| RH/QCesaroDyadicCriterion.lean | P/Q zero-growth equivalences, actual RH consumers, explicit signed block budget |

The previously established mean-neutral construction was reused rather than duplicated. This development follows Priority 3 and the signed-repair connection in the supplied agenda. The finite image-Gram optimization program remains a possible next direction; no new minimizer or uniform optimized-energy estimate is claimed.

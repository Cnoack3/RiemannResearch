# Finite signed sieve rows: bounded variation and one sign change

Research continuation — 20 October 2026

## Scope and notation

This continues QParityHeadContinuationResearch20261020.md, Section 5, and
the requested extension of the moving two-stage obstruction. Working base:
7d20806afda04d7d66a91a317846352b72a3d402, which contains 775bab3.

For a prime p, let V_K be the actual primorial gcd-class sieve vector,
s_K = sieveSlope(primorial K,p), and

\[
 E_K=E_{p,K}(\sigma)
 =p^{-\sigma}\prod_{\substack{q\le K\\q\ne p}}(1-q^{-\sigma}),
 \qquad \Phi_\sigma(v)=\sigma\,qMellin(v)(\sigma).
\]

Here the target is the existing logarithmic target
\(F_p(n)=\lfloor\log_p n\rfloor\) for positive n, with coordinate zero
anchored to zero. It is not the p-adic valuation of n. The physical Hilbert
weights are \(Q(n)=1/(\zeta(2)n^2)\).

A row is \(B=\sum_{K\in S}w_K V_K\), for an arbitrary finite set S of
integer cutoffs. Repeated cutoffs can be collected into one coefficient.
The two balance constraints are
\(\sum_S w_K=1\) and \(\sum_S w_Ks_K=0\).
A common lower cutoff H means every K in S satisfies K >= H.
Neither the cardinality of S nor the largest cutoff is bounded.

## 1. Exact Mellin identity and uniform Euler decay

New declarations in RH/QPrimePowerSignedObstruction.lean:

- signedSieveVector_mellin_exact
- signedSieveVector_balanced_mellin_exact
- signedSieveVector_mellin_bound
- primePowerEulerFactor_uniform_decay
- signedSieveVector_mellin_uniform
- signedSieveVector_quantitative_lower
- norm_tendsto_atTop_of_head_lower
- signedSieveVector_norm_tendsto_atTop

The identity is proved before any drift cancellation:

\[
 \Phi_\sigma(B)=\zeta(\sigma)
 \sum_{K\in S} w_K(E_K-s_K).
\]

Zero drift therefore gives exactly

\[
 \Phi_\sigma(B)=\zeta(\sigma)\sum_{K\in S}w_KE_K.
\]

For every envelope delta bounding |E_K| on the finite support,

\[
 |\Phi_\sigma(B)|\le|\zeta(\sigma)|
       \left(\sum_{K\in S}|w_K|\right)\delta.
\]

No mass-one condition is needed for these Mellin statements.
The exact full signed Gram identity remains
signedSieveVector_norm_sq_exact in QPrimePowerSignedSieve.lean.
No diagonal approximation or truncated physical norm is substituted.

The new uniform decay theorem proves, for 0 < sigma < 1,

\[
 \forall\epsilon>0\ \exists N\ge p\
 \forall K\ge N:\quad |E_K|<\epsilon.
\]

It derives this from the existing, unconditional scaled Euler decay
\(K^{1-\sigma}E_K\to0\), using \(K^{1-\sigma}\ge1\) for K >= 1.
The existing arithmetic Euler theorem is reused, not assumed as an
unresolved provider.

For \(1/2<\sigma<1\), a fixed TV bound M gives a threshold N uniform over
all finite supports, coefficient choices, and numbers of stages.

## 2. Quantitative complete-Q obstruction

Let

\[
 c_{p,\sigma}
 =\frac{2\sigma-1}
 {4\zeta(2)\sigma^2(p^\sigma-1)^2}>0.
\]

For every M >= 0 there is N >= p such that every balanced row with
support cutoffs K >= H >= N and TV <= M satisfies

\[
 \boxed{c_{p,\sigma}H^{2\sigma-1}
       \le \|B-F_p\|_Q^2.}
\]

The proof directly reuses:

1. signedSieveVector_head_of_balanced for the entire head n <= H;
2. qTarget_head_match_quantitative_lower for the complete-Q tail estimate;
3. qTarget_obstruction_constant_pos for the positive constant.

Consequently every such moving family with H_j tending to infinity
satisfies \(\|B_j\|_Q\to\infty\), not merely failure of norm convergence to
F_p. The hypotheses may hold eventually. All three, four, and arbitrary
finite or growing stage counts are included.

## 3. One sign change: the variation assumption is removed

New generic results in Analysis/SignedBalancedRows.lean:

- transport_determinant_exact
- transport_mass_exact
- transport_probe_bound
- signed_probe_bound
- not_balanced_of_reversed_slopes

New actual arithmetic results in RH/QPrimePowerOneSignObstruction.lean:

- NegativeBeforePositive (definition)
- sieveSlope_primorial_le_of_le
- primePowerEulerFactor_eq_of_slope_eq
- sieve_determinant_uniform
- signedSieveVector_oneSign_euler_uniform
- signedSieveVector_oneSign_mellin_uniform
- signedSieveVector_oneSign_quantitative_lower
- signedSieveVector_oneSign_norm_tendsto_atTop
- balanced_sieve_not_positive_before_negative

NegativeBeforePositive means that every negative coefficient occurs at a
cutoff no larger than every positive coefficient; zeros are ignored.
It permits repeated slope values. It imposes no minimum slope gap.

Here is the exact transport mechanism. Put
\(u_i=\max(-w_i,0)\), \(v_i=\max(w_i,0)\), and

\[
 T=\sum_i u_i s_i=\sum_i v_i s_i>0.
\]

Positivity of T follows from positive slopes and the two balance
constraints; it is discharged in signed_probe_bound. For any real probe f,

\[
 T\sum_iw_if_i
  =\sum_{i,j}u_i v_j(s_i f_j-s_j f_i),\qquad
 T=\sum_{i,j}u_i v_j(s_i-s_j).
\]

These are the specializations of the two exact finite transport identities.
The double sums are retained before taking absolute values.

For an ordered negative-positive pair, the existing uniform two-stage
secant theorem gives, for sufficiently large minimum cutoff,

\[
 |s_iE_j-s_jE_i|\le\epsilon(s_i-s_j).
\]

The new plateau theorem proves that equal sieve slopes force equal Euler
probes. Thus the displayed inequality also holds when s_i=s_j, with both
sides exactly zero. No division by a zero slope gap occurs.

Multiplying the pair inequality by \(u_i v_j\), summing, and dividing only
by T yields \(|\sum_iw_iE_i|\le\epsilon\), independently of TV.
The Mellin formula and existing head-tail bound then give

\[
 \boxed{c_{p,\sigma}H^{2\sigma-1}
       \le\|B-F_p\|_Q^2}
\]

uniformly over all such rows, even if TV is arbitrarily large.
Their complete-Q norms diverge as the common lower cutoff tends to infinity.

The opposite orientation is impossible: if all positive coefficients
precede all negative coefficients, the decreasing positive slopes cannot
satisfy mass one and zero drift. This is proved as a separate theorem,
rather than silently assuming the useful orientation.

The earlier sharp TV lower bound alone is not a norm bound. The stronger
conclusion uses the exact transport identities, actual plateau rigidity,
and the already established uniform secant decay.

## 4. Assumption and circularity audit

| Ingredient | Status and role |
|---|---|
| p prime; 1/2 < sigma < 1 | Explicit parameter hypotheses in the norm results |
| Finite legal synthesis | Existing signedSieveVector_mem; coefficients are unrestricted real numbers |
| Positive, decreasing actual slopes | Existing prime-step formulas and new finite-order consequence |
| Equal-slope Euler rigidity | New unconditional plateau theorem |
| Mass one and zero drift | Explicit algebraic restrictions on the proposed row family |
| Common lower cutoff tending to infinity | Explicit scope of the moving-family results |
| Uniform TV bound | Needed only for the first obstruction |
| One sign change | Replaces the TV bound in the stronger obstruction |
| Uniform Euler and secant decay | Existing arithmetic providers plus new checked deductions |
| Target signature and Mellin tail | Existing target and complete-Q results, reused directly |
| RH, target closure, PNT, conjectural energy estimate | None is assumed |

These are unconditional obstruction theorems for specified families.
They are not conditional RH reductions, proofs that F_p fails to belong
to the squarefree closure, or proofs of RH.

## 5. What remains available for three or more stages

Established exclusions:

- Any number of cofinal balanced sieve stages with uniformly bounded TV.
- Any number of cofinal balanced sieve stages with at most one sign change,
  regardless of TV; the reverse orientation is infeasible.
- Equal or nearly equal positive slopes do not provide an exception.

Mathematical consequences of the verified uniform estimates (not separate
additional Lean declarations in this change):

- A uniformly bounded-energy family within these cofinal rows must have
  TV tending to infinity and must eventually have at least two sign changes.
  Otherwise a bounded-TV or one-sign-change subsequence contradicts the
  uniform quantitative lower bound.
- The finite Mellin estimate also excludes an unbounded-TV family whenever
  TV times a uniform Euler envelope tends to zero.
- Convex averaging of uniformly small Mellin signatures keeps them small.
  Thus more sign changes are not by themselves sufficient: a convex mixture
  of cofinal balanced two-stage corrections still faces the same argument.

Open constructions, meaning not excluded here, not known to succeed:

1. Three-stage alternating patterns (+,-,+) or (-,+,-), and more general
   multiple-sign-change rows with sufficiently growing variation. They must
   retain the nonzero target Mellin signature while controlling every
   complete-Q Gram cross term. Matching one probe at one exponent is not
   sufficient for convergence.
2. Finite squarefree combinations with independently chosen divisor
   coefficients, outside mixtures of these fixed gcd-class sieve vectors.
   The exact-head/energy closure criterion still applies to this larger class.
3. Designs retaining a noncofinal portion of their sieve support, together
   with growing corrections. The common-lower-cutoff theorem does not apply;
   exact-head feasibility and complete-Q energy remain to be proved.

The preferred next finite investigation is an alternating three-stage row
satisfying mass, drift, and one prescribed Mellin signature. Keep the exact
3-by-3 determinant and full Gram energy. Test whether the energy has another
uniform obstruction before extending to larger alternating rows.
Do not infer a norm bound from the coefficient equations alone.

Still Open: a cofinal family of genuine finite legal exact-head candidates
with a uniform complete-Q energy budget; F_2 and F_3 membership in the
relevant enlarged closure; unconditional squarefree closure and RH.

## 6. Verification and publication record

The final saved-source import and axiom audit is
job_76IUGeg_G8JQSttSmSc0gDDtB_DbezCN: succeeded, exit_code=0, verified=true.
It built both new application modules and the changed generic module,
including the existing signed-sieve dependent. The nine inspected key
declarations depend only on propext, Classical.choice, and Quot.sound.
No project-local axiom, sorry, admit, or unsafe declaration was introduced.

The server reported 20.367 seconds for that job's verification work.
Its queue-start delay was under 0.01 seconds; user-visible polling delay
is separate. Workspace-opening duration was not separately recorded and
is not reported as proof-checking time.

Publication must pass the single final agent_workspace_checkpoint with
push enabled. Its terminal result is the authority for the integrated
validation scope and published commit. GitHub Actions is not used.

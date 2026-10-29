# CRT optimizer coalescence, signed conductor gaps, and finite dual closure

28 October 2026. Continuation of the attached CRT/Ramanujan/Pareto agenda, based on repository commit `20a079c0b083d524bf6ba3765eff914bf3ae47e3`.

## Conclusion

The continuation proves a sharper comparison of the actual Q and Pareto minimum-energy exact-head interpolants, a quantitative obstruction to arbitrary signed repairs using only distant conductors, and an exact description of what finite-support annihilator tests detect. The existing unconditional sublinear-energy theorem supplies convergence of the differences of suitable constrained minimizers. None of these results establishes constant membership or RH.

All measures and atoms retain the agenda's normalization: Q(n)=1/(ζ(2)n²), P(n)=1/(n(n+1)), and g_d(n)=(n mod d)/d at positive physical sites. The anchored value at zero is zero. Statements about squarefree legality are explicitly distinguished from estimates valid for all conductors.

## 1. Exact remainder and sharp head-dependent optimizer comparison

Let U be the legal zero-head tangent for a nonempty affine feasible set with a common head through H. Let F_Q and F_P minimize the complete Q and P norm energies on that same affine set. Define

\[
D=F_P-F_Q,\qquad x=F_Q-P_HF_Q,\qquad y=x+D,\qquad m=H+2.
\]

The affine minimum conditions are converted to normal equations; no derivative assumption is introduced. They give x perpendicular to U in Q, D in U, and

\[
\langle D,B(x+D)\rangle_Q=\|D\|_Q^2,
\quad Bf(n)=f(n)/(n+1).
\]

Where the tangent has an orthogonal projection, the exact equation is

\[
D=\Pi_U^Q B(x+D)=\Pi_U^Q Bx+\Pi_U^Q BD.
\]

Put C_my=2mBy-y. On vectors with zero head through H, the actual diagonal multiplier satisfies ||C_my||_Q≤||y||_Q. Before discarding any term, the general Hilbert identity is

\[
\boxed{\|x\|_Q^2-4m(m-1)\|D\|_Q^2
=\bigl(\|y\|_Q^2-\|C_my\|_Q^2\bigr)
+\|C_my-(2m-1)D\|_Q^2.}
\]

Both displayed remainders are nonnegative. Therefore

\[
\boxed{4(H+1)(H+2)\|F_P-F_Q\|_Q^2\le\|T_HF_Q\|_Q^2.}
\]

Equivalently the norm coefficient is 1/[2√((H+1)(H+2))], improving the agenda's proposed 1/[2(H+1)]. Exact Pythagoras holds in both metrics:

\[
\|F_P\|_Q^2=\|F_Q\|_Q^2+\|D\|_Q^2,
\qquad
\|F_Q\|_P^2=\|F_P\|_P^2+\|D\|_P^2.
\]

The coefficient is sharp given only the tail multiplier interval. For β=1/(H+2), the two-dimensional model U=span(e₁), x=e₂ and

\[
B=\frac{\beta}{2-\beta}
\begin{pmatrix}1&\sqrt{1-\beta}\\\sqrt{1-\beta}&1-\beta\end{pmatrix}
\]

has eigenvalues 0 and β and attains the abstract constant. This sharpness example is a paper-level calculation, independently checked in exact Wolfram algebra; the Lean result is the inequality and full remainder for the actual multiplier. The metric-angle context is classical: Lin and Sinnamon, [The generalized Wielandt inequality in inner product spaces](https://www.math.uwo.ca/faculty/sinnamon/pdf/wielandt.pdf). The formal proof is a direct expansion and does not assume that paper's theorem.

## 2. Unconditional coalescence of constrained minimizers

The canonical Möbius exact-head vector C_H=`QMobiusExactHead.exactHead H` satisfies the existing unconditional theorem

\[
\|C_H\|_Q^2/H\longrightarrow0.
\]

Its normalizing conductor is H+1. If H+1 is squarefree, C_H is a legal vector in the finite dictionary of divisors of primorial(H+1), and is exact through H. In particular every prime anchor H=p−1 is admissible. The actual zero-head tangent is the intersection of this finite dictionary with the physical head kernel.

Define p_j as the least prime at least j+2 and H_j=p_j−1. This is a fixed cofinal schedule. The Q and Pareto minimizers are explicitly defined by orthogonal projection of C_H along the finite zero-head tangent, with the Pareto projection transported back by the proved inverse measure-change map. Finite-dimensionality, common affine membership, exact heads, legality, and actual energy minimality are all proved. The same affine feasible set has C_{H_j} as a competitor. Q minimality and the preceding comparison yield

\[
4(H_j+1)(H_j+2)\|D_j\|_Q^2\le\|C_{H_j}\|_Q^2,
\qquad
\boxed{H_j\|D_j\|_Q^2\longrightarrow0.}
\]

Consequently ||D_j||_Q→0. This is a new application of the preexisting unconditional sublinear canonical-energy provider, not a new proof of that provider. It is convergence of differences between constrained minimum-energy interpolants. Their individual energies may still diverge. They are different families from the unconstrained projections of 1; their coalescence does not identify the limiting Q and Pareto projection residuals.

## 3. Signed conductor blocks and a finite maximum delay

Let R=Σ_{d∈S}c_dg_d, assume every d∈S exceeds M, and put A=Σ c_d/d. Without restrictions on signs or squarefreeness,

\[
R(n)=An\quad(0\le n\le M),\qquad
\sum_{n=1}^M Q(n)R(n)^2=MA^2/\zeta(2).
\]

The full signed head-energy expansion is

\[
\sum_{n=1}^M Q(n)(G(n)+R(n))^2
=\sum_{n=1}^M Q(n)G(n)^2
+\frac{2A}{\zeta(2)}\sum_{n=1}^M\frac{G(n)}n
+\frac{MA^2}{\zeta(2)}.
\]

The complete norms then imply

\[
\boxed{MA^2\le\zeta(2)(\|G+R\|_Q+\|G\|_Q)^2.}
\]

This controls arbitrary signed blocks and retains interaction with the old vector. Thus bounded old and repaired energies force the block slope to decrease at least at the inverse square-root scale of its conductor delay.

For the constant target put G_H=−Σ_{d≤H}μ(d)g_d and A_H=Σ_{d≤H}μ(d)/d. The preexisting theorem `Pareto.mobiusReciprocalSum_ne_zero` proves A_H≠0 whenever H>0, using an isolated prime and Bertrand's theorem. If a repair block beyond M≥H has slope A_H, then its exact prefix is

\[
(G_H+R)(n)=\sum_{d\le H}\mu(d)\lfloor n/d\rfloor\quad(n\le M),
\]

and its head through H equals 1. Every norm ceiling ||G_H+R||_Q≤C forces the explicit delay bound

\[
\boxed{M\le\frac{\zeta(2)(C+\|G_H\|_Q)^2}{A_H^2}.}
\]

There is no slope-nonvanishing hypothesis left open. This rules out sending an entire normalization block to infinity at a fixed head and fixed energy ceiling. It does not rule out cofinal constructions whose head, slope, old vector, and conductors vary together.

## 4. Finite constraints and the exact residual distance

Let W be the closed Q-Hilbert subspace defined by Δf(n)=Δf(rad n) for every n≥2. The finite-head interpolation theorem is now an equivalence: an anchored finite head is attainable by a squarefree legal vector exactly when it satisfies these radical-jump constraints.

Let A be the set of finitely supported vectors in L_sf⊥. The four-site Riesz vector

\[
a_m(k)=\frac{\delta_{k,m}-\delta_{k,m-1}-\delta_{k,\operatorname{rad}m}
+\delta_{k,\operatorname{rad}m-1}}{Q(k)}
\]

represents the corresponding jump constraint and belongs to A for m≥2. The formal dual classification is

\[
\boxed{(\operatorname{span}A)^\perp=W.}
\]

Since finitely supported annihilators form a linear subspace, Hilbert double-orthogonal duality gives closure(A)=W⊥. The exact distance theorem for the actual target residual r=1−Π_{L_sf}1 is

\[
\boxed{\|r-a\|_Q^2=\|r\|_Q^2+\|a\|_Q^2
\quad(a\in\overline A).}
\]

In particular r∈closure(A) iff r=0. Thus density of finite-support annihilators cannot be supplied merely by truncating an arbitrary annihilator: truncation need not preserve annihilation. Full density A in L_sf⊥ is equivalent to L_sf=W, a stronger condition than the target constant membership.

Paper-level rank refinement: at head H the attainable dimension is the number of squarefree integers in [1,H]. The count includes 1 as the initial-jump degree of freedom, although conductor 1 is excluded. The witnesses indexed by nonsquarefree m≤H form a triangular basis of finite-head annihilators. This dimension statement is not promoted to a new Lean theorem here.

## 5. Remaining RH obligation and next useful target

Open: prove a bounded-energy subsequence with cofinal exact heads, prove the genuine completed projected-point tests for one specified family, or establish zero mean for every relevant infinite-support annihilator. No such arithmetic provider has been proved in this continuation.

The strongest constructive next target is a repair scheme with interleaved conductors and a coupled estimate on slope, signed cross energy, and successive head cost. The new delay bound supplies a necessary constraint for such a scheme. The optimizer coalescence theorem permits comparison of metric-specific constrained constructions, but does not control their common energy.

## Verification ledger

Lean sources use focused imports, no placeholders and no new axioms. Exact Wolfram checks confirm the centered algebra, rational head constant, and two-dimensional eigenvalues; they are not proof premises. Saved-module verification and axiom audit `job_CTs9OiE1WwUqIJu7hVasqhHJWDuMpRUR` succeeded: the ten audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The central prime-schedule limit has no additional hypothesis. The server reported 23.044 seconds for that validation, distinct from request round-trip and polling time. The tool prescribed a 30-second polling interval; the server recorded negligible queue delay for this audit. Workspace-opening wall time was not separately recorded. Final publication uses the mandatory checkpoint to validate the saved modules and aggregate import; its identifier and commit are supplied in the accompanying response.

Sources: `Analysis/AffineEnergyMinimum.lean`, `Analysis/CenteredAffineDisplacement.lean`, `RH/QExactHeadOptimizerComparison.lean`, `RH/QExactHeadOptimizerCoalescence.lean`, `RH/QConductorGapEnergy.lean`, `RH/QMobiusDelayedBlock.lean`, `RH/QSquarefreeFiniteDualClosure.lean`, and `RH/QSquarefreeCanonicalFeasibility.lean`, `RH/QAffineEnergyMinimizers.lean`, and `RH/QPrimorialOptimizerCoalescence.lean`.

The central concrete declarations are `QPrimorialOptimizerCoalescence.prime_schedule_legal`, `prime_schedule_scaled_coalescence`, and `prime_schedule_coalescence`; these specify one fixed cofinal legal family without unknown energy hypotheses. The more general limit for all H concerns the canonical affine space; finite squarefree dictionary membership is asserted only when H+1 is squarefree.

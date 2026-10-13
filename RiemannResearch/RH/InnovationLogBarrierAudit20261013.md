# Innovation exponents and the logarithmic barrier

Date: 2026-10-13. Source: user-requested audit of the backward-RH investigation.
No novelty or RH claim is made. This note separates Lean results, published analytic
mathematics, and exploratory computations.

## Result and normalization

The quadratic innovation bound at every geometric stage is incompatible with Burnol's
logarithmic barrier. More strongly, every eventually uniform real exponent \(0<p<4\)
is incompatible. Quartic is the critical compatible exponent, with a sharp constant restriction.

Here \(d_N\) is a **squared norm**; \(d_N^4\) is the eighth power of the residual norm.
Repository stage \(n\) uses conductors through \(n+1\). For fixed initial stage \(n_0\), write

\[
x_k=\operatorname{energy}(\operatorname{geometricStage}(n_0,k)),\quad
a_k=\operatorname{twoSource}(\operatorname{geometricStage}(n_0,k)),\quad
N_k=(n_0+1)3^k.
\]

The existing actual adjacent-gain theorem supplies

\[
a_{k+1}\le 2(x_k-x_{k+1})(x_{k+1}-x_{k+2}). \tag{1}
\]

The explicit lower-envelope assumption is

\[
c>0,\qquad x_k\ge c/(k+1)\quad(k\ge K). \tag{2}
\]

No innovation lower-bound provider is asserted.

## Sharp obstruction

The new theorem 'late_actual_quartic_cap' states: for every \(a>1\), \(0<r<1\),
and \(J\), some \(j\ge J\) satisfies

\[
a_{2j+1}c^2r^4\le 2a^2x_{2j+1}^4. \tag{3}
\]

The exact parameterized Lean statement implies the sharp liminf conclusion

\[
\liminf_{k\to\infty}a_k/x_k^4\le 2/c^2. \tag{4}
\]

No extended-real liminf convention is needed by the formal theorem.
'actual_quartic_coefficient_cap' proves directly that an eventual uniform quartic
bound \(a_k\ge\eta x_k^4\) necessarily satisfies

\[
\boxed{\eta c^2\le2}. \tag{5}
\]

'no_eventual_subquartic_source' rules out \(a_k\ge\eta x_k^p\) for every \(k\ge J\),
for arbitrary real \(0<p<4\) and \(\eta>0\). Its quadratic specialization is
'no_eventual_quadratic_source'. RH is not assumed: the existing actual energy convergence
theorem supplies an unspecified limit, and the proposed innovation bound forces that
limit to vanish inside the contradiction.

Proof: apply the existing sharp relative-gain theorem to \(y_j=x_{2j}\).
Arbitrarily late two-step relative losses are below \(a/(j+1)\).
For sufficiently large \(j\), \(x_{2j+1}\ge r y_j\).
AM--GM in (1), together with \(c\le2(j+1)y_j\), yields (3).
A positive \(p\)-power lower bound first forces the residual limit to zero.
For \(p<4\), the lower bound divided by \(x_k^4\) then diverges, contradicting (3).

The additional scalar theorem 'no_cofinal_linear_source' excludes even an arbitrarily
sparse cofinal linear lower bound for a positive antitone convergent sequence satisfying
(1), without (2). Its actual specialization keeps finite-stage positivity explicit.
For \(0<p<1\), boundedness converts a positive \(p\)-power lower bound into a positive
linear one after constant rescaling. That rescaling is an elementary consequence,
not a separate Lean declaration in this development.

## Audit of Burnol's published theorem

Primary source: J.-F. Burnol, *A lower bound in an approximation problem involving the
zeros of the Riemann zeta function*, Advances in Mathematics 170 (2002), 56--70,
DOI 10.1006/aima.2001.2066; [2001 preprint, Theorem 1.3](https://arxiv.org/pdf/math/0103058).
The journal year is 2002; the preprint year is 2001.

Burnol's space is complex \(L^2((0,\infty),dt)\), with target \(\chi=1_{(0,1]}\) and
finite sums of \(\{\theta/t\}\), \(\lambda\le\theta\le1\).
His \(D(\lambda)\) is a norm, not a squared norm.
Theorem 1.3 bounds \(D(\lambda)\sqrt{\log(1/\lambda)}\) in liminf by the square root
of the zero sum with multiplicities squared. Squaring gives a positive logarithmic
barrier; every strictly smaller positive constant gives an eventual inequality.

The paper explicitly treats the RH dichotomy: if RH fails, the approximation distance
stays positive and the scaled liminf is infinite; the substantive proof treats RH.
The resulting lower barrier is unconditional mathematics. No simple-zero assumption
or replacement of the multiplicity-squared constant by an equality is made here.

## Cutoff-preserving transfer to the actual optimizer

The needed elementary correspondence already exists in 'ParetoNymanNorm.lean',
'BaezDuarteCenteredBridge.lean', and 'BaezDuarteNaturalApproximation.lean'.

For \(F(n)=\sum_{d\in s}b_d(n\bmod d)/d\), \(1\le d\le N\), define

\[
\widetilde F(t)=\sum_{d\in s}b_d
\left(\left\{\frac1{dt}\right\}-\frac1d\left\{\frac1t\right\}\right).
\]

It equals \(F(\lfloor1/t\rfloor)\) on the reciprocal integer cells, and vanishes for
\(t>1\). Conductor one absorbs the complete signed charge \(-\sum b_d/d\).
Thus it is a natural fractional-part sum with conductor support
\(\{1\}\cup s\subseteq[1,N]\), and every dilation parameter lies in \([1/N,1]\).
The exact complete-domain identity is

\[
\int_0^\infty|\chi-\widetilde F|^2\,dt
=\sum_{n\ge1}\frac{|1-F(n)|^2}{n(n+1)}. \tag{6}
\]

There is no factor-two loss in this direction. Burnol's larger complex-coefficient,
real-parameter approximation space contains these finite real sums, so

\[
D(1/N)^2\le d_N. \tag{7}
\]

The new 'BurnolParetoTransfer.lean' formalizes this via lower bounds rather than
rebuilding an infimum-distance API:

- 'ContinuousCutoffLowerBound N L' is a proposition about every literal finite sum
  with parameters in \([1/N,1]\). It is not an axiom, asserted instance, or provider.
- 'naturalError_lower' specializes to natural conductors.
- 'finiteResidueSum_projection' identifies the actual optimizer.
- 'energy_lower_of_continuous' proves \(L\le\operatorname{energy}(n)\) at cutoff \(n+1\).
- 'energy_log_envelope' transfers the logarithmic bound.
- 'geometric_envelope_of_continuous' obtains (2) on any fixed geometric ray.
- 'no_subquartic_of_continuous_lower_bound' assembles the contradiction with the
  only analytic input stated directly on continuous fractional-part functions.

**Formal boundary:** the finite cutoff-preserving transfer is proved.
A Lean provider for Burnol's analytic theorem is still Open.
The Lean implication remains conditional on that analytic proposition; invoking the
published theorem establishes the contradiction in ordinary mathematics.
No project-local analytic axiom was introduced.

The older 'BurnolDistanceLowerEnvelope' concerns 'CoupledResidual.distance', a two-seed
budget optimizer. It is not definitionally the full-residue 'energy' used here.
This development targets the latter directly and does not claim to discharge the old
two-seed proposition merely by renaming a distance.

## Quantifiers and schedules

For quadratic-success stages \(S\subseteq\{0,\ldots,K-1\}\), where the lower bound is
imposed at middle stage \(j+1\), put \(q=2/(2+\eta)\).
'quadratic_stage_count' proves

\[
|S|(-\log q)\le \log(x_0/c)+\log(K+1). \tag{8}
\]

Consequently only \(O(\log K)\) such successes can occur through scale index \(K\).
Every-stage, positive-density, and bounded-gap quadratic schedules are excluded.
Enumerated success indices grow at least exponentially in their count; their conductors
grow at least doubly exponentially.

Bare cofinality is not excluded. For a scalar compatibility example, fix \(0<q_0<1\)
and put paired drops
\(q_0^{2j}\to q_0^{2j+1}\to q_0^{2j+2}\) around indices \(B^{j+1}\), with plateaus between,
integer \(B\ge3\), and \(Bq_0^2\ge1\).
At each middle drop, saturating (1) gives
\(a/x^2=2(1-q_0)^2/q_0>0\), while the spacing preserves a reciprocal-index lower envelope.
This informal scalar example is not a construction of actual Pareto optimizers or a
separately formalized sequence.

| Exponent in \(a_k\ge\eta x_k^p\) | Eventually every geometric stage | Merely cofinal |
|---|---|---|
| \(0<p\le1\) | Impossible | Impossible for positive finite residuals |
| \(1<p<4\) | Impossible with (2) | Not generally excluded by the every-stage theorem |
| \(p=2\), sharper schedule restriction | Impossible | At most \(O(\log K)\) successes through index \(K\) |
| \(p=4\) | Compatible with the rate barrier, necessarily \(\eta c^2\le2\) | Not excluded; arithmetic provider Open |
| \(p>4\) | Compatible with the rate barrier | Not excluded; arithmetic provider Open |

“Not excluded” is not an existence theorem. Any fixed geometric base has the same
qualitative obstruction. A coefficient tending to zero or a sparse choice of successful
stages changes the hypothesis materially.

## Quartic compatibility and the arithmetic gap

For \(x_k=C/(k+1)\), set \(t=k+1>1\). The exact identity

\[
2\left(\frac C{t-1}-\frac Ct\right)\left(\frac Ct-\frac C{t+1}\right)
=\frac2{C^2}\frac{t^2}{t^2-1}\left(\frac Ct\right)^4 \tag{9}
\]

and its lower inequality with coefficient \(2/C^2\) are Lean-verified as
'reciprocal_quartic_model' and 'reciprocal_model_allows_quartic'.
The constant in (5) is sharp for the scalar adjacent-gain framework.
For \(C\le1\), this model also respects the older one-step upper inequality at
positive middle stages. Higher exponents are weaker once \(x_k\le1\).

This is not an arithmetic innovation lower bound.
The existing exact signed identity, with \(u=F_{3N}-F_N\) and
\(v_m=D_m(F_N-F_{N/3})\), gives, when both adjacent gaps \(G_-,G_+\) are positive,

\[
A_N=G_-G_+(\cos^2\theta_2+\cos^2\theta_3),\qquad
\cos\theta_m=\frac{\langle u,v_m\rangle}{\|u\|\|v_m\|}. \tag{10}
\]

Both the gain product and the alignment need lower control.
Two vectors cannot supply a positive frame lower bound on every direction of this
infinite-dimensional Hilbert space. The actual outgoing direction requires arithmetic
information. The scalar lemma 'zero_source_satisfies_upper' likewise records that zero
source satisfies the upper recurrence; it does not assert actual innovations vanish.

No unconditional cofinal lower bound for the actual alignment or quartic source was
obtained. Burnol controls distance, not this directional correlation.
A concrete next target is simultaneous cofinal lower control of the normalized
adjacent gains and their alignment, retaining both signed correlations.

## Exploratory arithmetic probe, not a proof certificate

For \(L=\operatorname{lcm}(d,e)\), the complete Gram entry was evaluated by

\[
G_{de}=\sum_{r=1}^{L}\frac{(r\bmod d)(r\bmod e)}{de}
 \frac{\psi((r+1)/L)-\psi(r/L)}L.
\]

This accounts analytically for the infinite periodic tail.
We solved \(Gc=b\), \(b_d=\log(d)/d\), and used
\(D_mg_d=g_{md}-g_m/d\) to evaluate innovations, retaining the conductor-\(m\) correction.
NumPy 2.3.5 / SciPy 1.17.0 double precision gave:

| \(N\) | \(d_N\) | \(I_{2,N}\) | \(I_{3,N}\) | \(A_N/d_N^4\) |
|---:|---:|---:|---:|---:|
| 3 | 0.095747784 | 0.088456516 | 0.087989665 | 462.554 |
| 9 | 0.024095079 | -0.002266828 | -0.000543212 | 33.1161 |
| 27 | 0.015344017 | -0.001590577 | -0.001878827 | 282.328 |
| 81 | 0.010963754 | -0.000318462 | -0.001003061 | 222.938 |

At \(N=3,9,27\), fractions of the adjacent upper bound attained are
0.300003, 0.00890079, and 0.204136.
Gram condition numbers ranged from approximately 4.1 to 13,949; normal-equation
residuals were at most \(1.7\cdot10^{-16}\).
These are not interval-certified errors and supply no asymptotic conclusion.
Sign changes and weak alignment at \(N=9\) caution against inferring positive
uniform alignment from the quartic scale calculation.

## Verification and remaining obligations

New exported modules:
'Analysis/InnovationLogBarrier.lean', 'RH/BurnolParetoTransfer.lean',
and 'RH/ActualInnovationLogBarrier.lean'.

Development job 'job__epG5TgUjFXm_2VqqNESjyt9MdKLpDxr' successfully compiled the final
three modules (exit 0) and checked nine selected declarations, each using only
'propext', 'Classical.choice', and 'Quot.sound'. These include the sharp constant,
the reciprocal model, the sparse linear obstruction, and the full continuous-input
contradiction. The earlier initial-module audit also passed.
Publication is gated by the final checkpoint's successful server validation of the
persisted delta and any integrated source; development snippets alone are not publication evidence.

Open analytic formalization: a provider of the continuous Burnol logarithmic envelope.
Open arithmetic research: a positive cofinal quartic innovation bound or a sufficient
gain-and-alignment provider. Neither is assumed proved.

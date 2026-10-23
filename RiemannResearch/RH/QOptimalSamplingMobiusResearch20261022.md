# Optimal sampled selections and the Möbius limit

Research continuation for Christian Noack, 22 October 2026.

## Conclusion and scope

The optimal selections admit a uniform complete-Q norm bound when they are
unconstrained projections in a linear legal trial space and the sampled metric
has uniform relative error below one. This bound does not identify their
limit as the constant target.

The new Lean results prove the sharp sampled-projection norm inequality, its
actual complete-Q realization, an exact rational equality example, and a
coefficient-limit identification criterion. They reuse the existing periodic
weights, sampling discrepancy estimates, and continuous Möbius coefficient
functionals. No uniform exact-head repair bound or RH proof is asserted.

## 1. Dictionaries and sampling heights

Let Q(n)=1/(zeta(2)n^2), n>=1, and let D_j be nested finite dictionaries of
squarefree conductors d>=2, exhausting all such conductors. Put

    V_j = span {g_d : d in D_j},   H = closure(union_j V_j),
    p_j = P_{V_j} 1,              h = P_H 1.

All composite squarefree conductors are retained. For a common squarefree
period L_j, use the complete weights

    w_j(a) = sum_{k>=0} Q(a+k L_j),  1 <= a <= L_j.

The zero residue has positive physical representative L_j. Thus these
finite weights already include the infinite tails.

At height T, coded zero frequencies give q_{j,T}(a)=L_j nu_{j,T}(a).
The existing strictly increasing diagonal selection theorem applies to
fixed-stage frequency convergence. It permits T_j increasing so that

    max_a |q_{j,T_j}(a)-1| <= epsilon_j,   0 <= epsilon_j < 1.

One may prescribe epsilon_j tending to zero, or bounded above by 1/2.
This is a nonquantitative selection: it provides no useful numerical height
bound. The analytic frequency provider remains a separate hypothesis in
the Lean sampling interface. The discussion below remains valid even when
that provider is granted.

The uniform comparison is on the finite complete-weighted cell space,
or on the necessary trial/target space via a suitable form comparison.
It is not a comparison of an unweighted finite physical sample with every
function on the infinite Q support.

## 2. New sharp norm bound

Write B for the true weighted form, E(f)=B(f,f), and Bhat for its perturbation
by q. Let f be the sampled projection of a target y in a linear trial space.
Its normal equation in the direction f is

    Bhat(y-f,f)=0.

Put e=E(y-f), x=E(f), t=B(y-f,f). The exact signed identity is

    E(y)=e+x+2t.

The previously verified discrepancy bound gives

    t^2 <= epsilon^2 e x.

Therefore e+epsilon^2 x+2t>=0, and

    (1-epsilon^2) E(f) <= E(y).

For y=1 this proves

    ||f||_Q^2 <= 1/(1-epsilon^2).

In particular epsilon_j<=1/2 gives the unconditional stability bound
||f_j||_Q^2<=4/3 for every stage satisfying the metric and normal equations.
The true optimizer has the stronger bound ||p_j||_Q^2<=1.

New declarations:

- Analysis.FiniteWeightedSampling.sampled_projection_energy_mul_bound
- Analysis.FiniteWeightedSampling.sampled_projection_energy_le
- Analysis.FiniteWeightedSampling.sampled_projection_two_cell_sharpness
- RH.QZeroPhaseSampling.weighted_normal_projection_norm_mul_bound

The Q theorem uses the full periodic-tail weights. It does not assume an
unproved arithmetic closure statement.

### Exact rational equality example

This is an abstract two-cell example, not a squarefree-conductor construction.

| Cell | w | q | f | y |
|---|---:|---:|---:|---:|
| 1 | 1/4 | 1/2 | 2 | 1 |
| 2 | 3/4 | 3/2 | 2/3 | 1 |

Here epsilon=1/2, Bhat(y-f,f)=0, E(y)=1, E(f)=4/3,
E(y-f)=1/3, and B(y-f,f)=-1/3. In the one-dimensional trial space
span{f}, the normal equation identifies the unique sampled optimizer.
Equality holds in the bound. The Lean example checks positive weights,
relative discrepancy, the normal equation, and both energies exactly.

## 3. What a cofinal schedule converges to

The existing optimizer-displacement theorem gives

    ||f_j-p_j||_Q^2 <= epsilon_j^2/(1-epsilon_j^2) * delta_j,
    delta_j = ||1-p_j||_Q^2 <= 1.

Nested projection theory gives p_j -> h=P_H1 strongly. Consequently
epsilon_j->0 implies f_j->h strongly. Every cofinal exhaustive schedule
has the same limit. Larger heights reduce sampling error; they do not
change h.

The exact true-error identity is

    ||1-f_j||_Q^2 = delta_j + ||f_j-p_j||_Q^2.

Thus the limiting error is ||1-h||_Q^2. Its vanishing remains Open.

## 4. Coefficients converge; their identification remains arithmetic

Use the existing continuous coefficient extractor, for d>=2,

    Lambda_d(F) =
      -sum_{e|d} mu(d/e) [F(e)-F(e-1)],  with F(0)=0.

It satisfies Lambda_d(g_a)=1 if d=a and 0 otherwise, and
Lambda_d(1)=-mu(d). Therefore, for the finite residue coefficients of f_j,

    c_{j,d} -> Lambda_d(h).

This convergence and boundedness are available without first identifying
the limit. The existing theorem coefficients_eq_mobius_iff states

    [Lambda_d(h)=-mu(d) for every d>=2] iff h=1.

The new theorem
RH.QSquarefreeFormalSynthesis.strong_limit_eq_one_iff_coefficients_tendsto
packages this with continuous coefficient convergence and uniqueness of limits:

    given F_j -> h strongly,
    h=1 iff every fixed residue coefficient tends to -mu(d).

It reuses the verified coefficient functionals rather than rebuilding
divisor incidence. Nonsquarefree coefficients vanish on legal squarefree
functions and hence on their closure, so their zero target values are automatic.

An ordinary explanation of the converse is useful. The exact discrete jump
identity for finite legal F is

    F(n)-F(n-1)=F(1)-sum_{d|n,d>=2} c_d.

Passing to the strong limit and substituting -mu(d) gives

    h(n)=1+n(h(1)-1),   n>=1.

Under Q, a nonzero linear slope has infinite squared norm. Hence h(1)=1
and h=1. The existing totality theorem formalizes the same rigidity.

Uniform optimizer bounds and coefficient convergence thus hold, but the
remaining assertion that the coefficient limits are specifically -mu(d)
already identifies the desired target. It cannot be inferred from choosing
a slower cofinal schedule.

## 5. Why the bound does not automatically apply to exact-head repairs

For exact-head minimization, F(n)=1 for 1<=n<=M already forces

    c_d=-mu(d),   2<=d<=M.

The feasible set is affine. F itself is generally not an allowed variation:
scaling F changes its head. Its normal equations therefore do not imply
Bhat(1-F,F)=0, the hypothesis of the new norm bound.

Sampling does preserve comparisons between minima over the same affine
feasible set. If p is its true optimizer and f its sampled optimizer,
the existing discrepancy argument controls ||f-p|| in terms of ||1-p||.
This transfers a uniform bound once available; it does not provide that bound.

For the reduced complete-Q repair system the exact identity remains

    ||1-F*_{M,D}||_Q^2 = delta_D + C(M,D),
    C(M,D) = r^T (A G^{-1} A^T)^{-1} r,    0<=delta_D<=1.

The required arithmetic provider is still a uniformly bounded C(M,D_j)
along an exhaustive, feasible schedule.

## 6. A precise diagonal-selection dichotomy

The following is an ordinary Hilbert-space derivation, not a new standalone
Lean declaration in this addition. It clarifies the quantifiers behind the
proposed selection argument.

If 1 belongs to H, fix M and use the existing finite-head interpolation map
B_M on the independent observations L_M. For legal g close to 1, the vector

    f = g + B_M(L_M1-L_Mg)

has exact head through M and satisfies

    ||1-f|| <= (1+||B_M|| ||L_M||) ||1-g||.

For fixed M the constant is finite. Density and nested dictionaries then
permit strictly increasing stages whose exact-head errors are below any
prescribed positive tolerances.

Conversely, if 1 does not belong to H, put h_perp=P_{H-perp}1, which is
nonzero. Every exact-head f in H satisfies the exact signed tail identity

    ||h_perp||^2
      = <1-f,h_perp>
      = <1-f, 1_{n>M} h_perp>.

Consequently

    ||1-f||_Q^2 >=
      ||h_perp||_Q^4 / ||1_{n>M} h_perp||_Q^2  -> infinity.

The denominator is positive whenever a feasible exact-head f exists.
It tends to zero by Q-square summability. Thus every exact-head dictionary
schedule would diverge in energy in this branch; optimization cannot remove
this obstruction. Since delta_D<=1, the corresponding repair cost is at least
the displayed ratio minus one.

There is therefore a genuine choice-of-schedule theorem once closure is known,
but closure cannot be supplied by the diagonal argument itself.

## 7. Remaining research target

Two precise routes remain:

1. For unconstrained optimizers, identify
   Lambda_d(P_H1)=-mu(d) for every fixed squarefree d>=2.
   Equivalently force delta_j -> 0, or b_j^T G_j^{-1} b_j -> 1.
2. For exact-head optimizers, establish one complete signed arithmetic bound
   sup_j C(M_j,D_j)<infinity with M_j tending to infinity.

The verified RH consumers apply after either route supplies target closure.
Neither norm stability of unconstrained projections nor coefficient
stabilization of exact-head projections supplies both ingredients by itself.

## Verification record

Saved-source import and all five declaration audits:
job_JoSSlEFQB0lmdE1r1OrlDwMa1-BByebh succeeded, exit code 0.
The server reported 15.82 seconds including required import/module work.
Every axiom audit reported only propext, Classical.choice, and Quot.sound.
The strong-limit hypothesis, relative metric control, and sampled normal
equation remain explicit assumptions in the respective declaration types.
The final checkpoint result is recorded in the publication receipt; this
targeted check is not the final aggregate project certificate.

Workspace-opening latency was not independently measured. Job queue delay
and server compilation time are distinct; observed queued development jobs
started within one hundredth of a second. Polling followed the server's
30-second retry guidance, and observation delay is not compilation time.

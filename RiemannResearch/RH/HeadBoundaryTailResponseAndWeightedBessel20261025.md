# Finite head boundaries and solved squarefree response

25 October 2026. Continuation of the odd-radical projection handoff, baseline
`ea8c48ad5ae3fed6fbba7753659b914955ef4c4d`.

**RH is not proved.** The uniform actual response bound (B), prime-square
surviving-energy bound (KPS), and flexible screening bound (KF) remain Open.
The progress below concerns exact actual-stage structure and unconditional
estimates after projection. No additional conditional RH theorem is needed.

## Objects and conventions

Let Z=zeta(2), Q(n)=1/(Z*n^2) for physical n>=1. All norms below are complete
Q-Hilbert norms, including every infinite tail. The actual stage V_N uses the
masked dictionary of squarefree conductors 2<=d<=N+1. Let P_N project onto V_N,
r_N=1-P_N1, epsilon_N=||r_N||^2, Bf(n)=f(n)/(n+1), and b_N=P_NBr_N.
Lean's coordinate j corresponds to physical site j+1.

## 1. Exact finite-head characterization

Module: `RH/QSquarefreeHeadBoundary.lean`.

For a physical sequence f anchored by f(0)=0, put

    Delta f(k) = f(k)-f(k-1)
    A_d(f) = sum_{k|d} mu(d/k) Delta f(k)
    c_d(f) = -A_d(f), d>=2
    S_N f = sum_{d=2}^{N+1} c_d(f) g_d
    L_N(f) = f(1)-sum_{d=2}^{N+1} c_d(f)/d.

These are the existing continuous Mobius coordinates, with no arbitrary
coefficient choice. `headSynthesis_prefix` proves the exact identity

    S_N f(n) = f(n)-n L_N(f), 0<=n<=N+1.

`exists_stage_head_match_iff` proves that the head of f is realized by a
vector in V_N exactly when both conditions hold:

1. c_d(f)=0 for every nonsquarefree d in [2,N+1];
2. L_N(f)=0.

The actual Lean statement uses `i : Fin N`, d=i+2, and `qCoefficientCLM`.
It does not silently replace omitted Mobius coordinates by an unproved
infinite radical-space characterization. The reconstruction S_N f is legal
when the omitted coordinates vanish. `stage_head_injective` proves uniqueness
of a stage vector with prescribed values on 0..N+1.

`headCharge_qOne`, `residual_headCharge`, and `movingCorrection_headCharge`
give, exactly,

    L_N(1) = 1 + sum_{d=2}^{N+1} mu(d)/d,
    L_N(r_N) = L_N(1),
    L_N(b_N) = 0.

Thus all finite omitted constraints together still leave one explicit
boundary condition. This is a finite statement, not density of the legal
closure or a bound for the complete extension norm.

## 2. An actual response component is uniformly controlled

Module: `RH/QSquarefreeTailResponse.lean`.

Define the actual legal zero-head subspace and its orthogonal projection:

    C_{N,H} = {v in V_N : v(1)=...=v(H)=0},
    J_{N,H} = P_{C_{N,H}},
    t_{N,H} = J_{N,H} B r_N,
    h_{N,H} = b_N - t_{N,H}.

`response_split` and `response_pythagorean` retain exact identities:

    b_N = h_{N,H}+t_{N,H},
    ||b_N||^2 = ||h_{N,H}||^2+||t_{N,H}||^2.

The vector h lies in V_N intersect C_{N,H}-perp. It agrees with b_N on sites
1..H. `headResponse_minimum_identity` proves, for every g in V_N with that
same head,

    ||g||^2 = ||h_{N,H}||^2 + ||g-h_{N,H}||^2.

Thus h is the unique minimum-norm complete legal extension of these actual
response head values. It is not obtained by discarding the complete tail.

For every real a, `tailResponse_pairing` proves

    ||t||^2 = < tail_H(B(tail_H r_N)-a tail_H r_N), t >.

The residual is orthogonal to C_{N,H}; this is why the scalar centering is
legitimate even though r_N itself is not tail-supported. Taking
c_H=1/[2(H+2)] and using the existing midpoint multiplier bound gives

    ||t_{N,H}|| <= ||tail_H r_N||/[2(H+2)],
    |t_{N,H}(n)| <= sqrt(Z)*n*||tail_H r_N||/[2(H+2)].

Central declarations: `tailResponse_norm_le`, `tailResponse_physical_bound`.
These estimates are for an already projected actual response. They do not
leave an uncontrolled inverse Gram matrix after the estimate.

`tailResponse_uniform_window` has the full quantifiers:

    forall A>=0, epsilon>0, exists H0, forall H>=H0, forall N,n,
      n <= A(H+2)  ==>  |t_{N,H}(n)| < epsilon.

This uses unconditional strong convergence of r_N and hence uniform unscaled
tail tightness. It supplies no effective rate. N is unrestricted.

### Exact arithmetic contrasts

For active conductors d,e>H,

    d g_d - e g_e in C_{N,H},

since each normalized atom equals n on the initial head. This is verified
by `normalized_contrast_mem_tailStage`, with actual masked-stage indexing.
Consequently `headResponse_normalized_moments_eq` proves

    d <g_d,h_{N,H}> = e <g_e,h_{N,H}>.

The remaining high-conductor normal moments therefore share one scalar.
This is an exact signed constraint, not a positivity or cancellation claim.

## 3. Weighted Bessel estimates after orthogonalization

Modules: `Analysis/TriangularWeightedBessel.lean` and
`RH/QTriangularWeightedBessel.lean`.

Let {u_i} be any finite pairwise orthogonal family with ||u_i||<=1. Let s_i>=1
be a physical onset: u_i(n)=0 for n<s_i. Completeness and distinct onsets are
unnecessary; zero vectors are allowed. The complete-tail theorem is

    sum_i (s_i+1)^2 |<Bf,u_i>|^2 <= ||f||^2.

For a subfamily with s_i>=H+1, the sharper bound is

    sum_i (s_i+1)^2 |<Bf,u_i>|^2 <= ||tail_H f||^2.

In Lean onset is zero-based, so the weight is `(onset_i+2)^2`.
`reciprocal_onset_bessel` and `reciprocal_onset_tail_bessel` prove these
statements, with no arithmetic hypothesis. `movingCorrection_onset_bessel`
and `movingCorrection_onset_tail_bessel` apply them to actual stage vectors:

    sum_i (s_i+1)^2 |<b_N,u_i>|^2 <= epsilon_N,

and the high-onset right side is ||tail_H r_N||^2.

Proof: combine Bessel inequalities on nested tail-supported subfamilies.
In zero-based coordinates use layer increments delta_0=4 and delta_k=2k+3
for k>=1. Their partial sum through j is (j+2)^2, exactly cancelling the
square of B's multiplier. Every tail in every layer remains infinite.
`layered_bessel` provides the general finite Hilbert-space identity/estimate;
`reciprocal_layer_energy_le` performs the complete Q summation.

This is a coefficient estimate after orthogonalization, rather than a bound
on raw forcing coordinates before a potentially ill-conditioned solve.

## 4. What remains to prove

The original consumer is still
`QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound`:

    exists C>=0, forall N,n, 1<=n<=N ==> |b_N(n)|<=C.

This continuation has not supplied that provider. Two concrete routes now
retain all the actual projection structure:

1. Choose H comparable to n (or a carefully controlled smaller cutoff), and
   bound the signed minimum-norm extension h_{N,H}(n). The t component is
   controlled above. Use the exact head boundary, normalized high-conductor
   moment identity, and actual residual coupling. No sup-norm contraction,
   positivity, or sign of individual normal coefficients has been proved.
2. Construct an ordered orthonormal basis of projected evaluation kernels,
   retaining its physical onsets. In ordinary finite-dimensional mathematics,
   weighted Cauchy--Schwarz and Section 3 give

       |b_N(n)|^2 <= epsilon_N D_N(n),
       D_N(n)=sum_i |u_i(n)|^2/(s_i+1)^2.

   The basis construction, exact synthesized response formula, and this
   physical diagonal corollary are NOT separately formalized in the new
   modules. The orthogonal-family estimates themselves are formalized.
   Prove a genuine uniform arithmetic bound on epsilon_N D_N(n), or exploit
   the signed actual coefficients to improve on that sufficient bound.
   High-onset weighted coefficient tails are already controlled; the
   low-onset physical reconstruction can still amplify them.

A general operator-norm estimate on arbitrary compatible head data is
stronger than the required actual coupled-response estimate. It must not be
assumed. Finite head solvability does not bound the norm of its complete
legal extension. The original KPS/KF routes also remain open.

The complete odd-radical QHilbert operator R and its 31/13 physical bound
remain ordinary mathematics from the incoming handoff, not newly formalized
here. No bound for P_N(RBr_N) follows merely from boundedness of RBr_N.

## 5. Numerical and symbolic diagnostics, not certificates

Complete moment formulas from the incoming handoff were evaluated with
SciPy special functions. G includes the full infinite periodic tail.
Ordered Gram--Schmidt of whitened head evaluation rows gave the following
floating diagnostics (basis orthogonality errors below 3e-15):

| N | epsilon_N | max head D_N | epsilon_N max D_N | max head abs(b_N) |
|---:|---:|---:|---:|---:|
| 16 | 0.01167427 | 0.90925527 | 0.01061489 | 0.00990097 |
| 32 | 0.00912754 | 1.24826539 | 0.01139359 | 0.01549382 |
| 64 | 0.00755325 | 1.61391653 | 0.01219032 | 0.01897713 |
| 128 | 0.00633207 | 3.04380736 | 0.01927360 | 0.03836078 |

A zero-pivot tolerance was used; these are not exact rank certificates.
The displayed D estimates are not numerically sharper than the earlier
prime-square certificates. Their purpose is to isolate the arithmetic
quantity after orthogonalization. They prove neither boundedness nor decay.

Wolfram exact rational calculations checked the head reconstruction and
zero charge of all active atoms for cutoffs 2..8; Lean proves the general
statements independently. An initial diagnostic had a bound-variable name
collision and was corrected before interpreting its output.

Primary-source context inspected: Balazard, arXiv:1812.04309 (Mobius
coordinates and the RH-related limiting arithmetic function), Bagchi,
arXiv:math/0607733 (Hilbert-space criteria), and Alouges--Darses--Hillion,
arXiv:2006.02953 (approximation and coefficient-control separation).
No assertion from those papers is used to discharge the open estimate.

## 6. Verification and continuation

The new declarations contain no sorry, admit, project-local axiom, or unsafe
declaration. Central isolated checks succeeded: finite-head job
`job_MCA2Ir4x0zBgLwgPIdjS6SDjgpHkYkIc` (9.357 s), tail-response job
`job_gQUmNkVc72ySiOrMBOfM3n_W5j_57T1Z` (7.907 s), and full weighted-Bessel
job `job_pVyd5cQ5KtB3lJDHqPKh70IYiHkYEQBu` (6.735 s). These are server
reported run durations, not pure kernel timing. Workspace opening completed
but no independent opening-duration measurement was retained. Axiom audits use only propext,
Classical.choice, and Quot.sound. Final publication requires the single
server checkpoint with push enabled; its terminal validation scope, job ID,
and commit are reported with the accompanying result. Failed intermediate
elaboration attempts are not mathematical counterexamples.

Retained workspace: ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj.
Root: /home/cri_2025/lean-agent-workspaces/ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj/RiemannResearch.
Follow any continuation workspace returned by publication. Serialize all
Lean verification submissions and preserve newer published work.

Next acceptance target: an unconditional provider of the actual signed
head-response bound or of a complete error-weighted surviving-energy bound.
Only then apply the existing RH consumer and inspect its assumption-free
final declaration type.

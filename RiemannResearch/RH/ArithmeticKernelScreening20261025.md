# Arithmetic screening of squarefree correction kernels

25 October 2026. Continuation of the shrinking-head handoff at
c8df87d13852f81ec4e8c62a13e2d606ddc73fa6.

**Status: RH is not proved.** This continuation proves an unconditional,
strictly sharper available estimate by removing known arithmetic annihilator
directions before Cauchy--Schwarz. It does not prove a common bound for the
remaining screened energy or the signed shrinking-head response.

## Actual objects and conventions

Q(m)=1/(zeta(2)m^2), m>=1. The masked stage V_N uses squarefree conductors
2<=d<=N+1. P_N is its Q-orthogonal projection, r_N=1-P_N1,
epsilon_N=||r_N||_Q^2, Bf(m)=f(m)/(m+1), and
b_N=P_N B r_N. Write e_n for the physical evaluation representer,
k_N,n=P_N e_n, u_N,n=(I-P_N)B k_N,n, and Lambda_N,n=||u_N,n||_Q^2.

The earlier exact signed identity is b_N(n)=<r_N,u_N,n>_Q.
Its energy is the complete infinite Schur difference
||Bk_N,n||^2-||P_N Bk_N,n||^2. All new results preserve these full quantities.

## Verified four-site subtraction

Define ell_4(f)=f(4)-f(3)-f(2)+f(1) and
z=e_4-e_3-e_2+e_1. The existing squarefree boundary theorem gives
ell_4(f)=0 for every f in the legal closure, and ell_4(1)=0.
Consequently <r_N,z>=0 at every actual finite stage.

The new module proves
||z||^2=30*zeta(2) and
D_N,n=<u_N,n,z>=ell_4(Bk_N,n)
=K_N(n,4)/5-K_N(n,3)/4-K_N(n,2)/3+K_N(n,1)/2.

Set u4_N,n=u_N,n-D_N,n*z/(30*zeta(2)). Then exactly

    <r_N,u4_N,n> = b_N(n),
    ||u4_N,n||^2 = Lambda_N,n-D_N,n^2/(30*zeta(2)) =: Lambda4_N,n,
    0 <= Lambda4_N,n <= Lambda_N,n,
    |b_N(n)|^2 <= epsilon_N * Lambda4_N,n.

Thus a square can be removed unconditionally. The removed direction is
orthogonal to the actual residual, not merely orthogonal to the legal stage.
This distinction is necessary: an arbitrary squarefree annihilator may have
nonzero mean and need not be orthogonal to r_N.

Source: RH/QSquarefreeKernelScreening.lean.
Principal declarations:
- fourSiteVector_norm_sq;
- residual_inner_fourSiteVector;
- residualized_inner_fourSiteVector;
- movingCorrection_sq_le_fourSite;
- fourSiteScreenedKernel_norm_sq;
- fourSiteScreenedKernel_pairing;
- fourSiteEnergy_nonneg and fourSiteEnergy_le;
- fourSiteScore_physical.

The conditional consumer riemannHypothesis_of_fourSiteEnergy_bound has the
explicit **Open** premise

    C>=0 and, for all N,n with 1<=n<=N,
    epsilon_N * Lambda4_N,n <= C^2.

It invokes the existing moving-head consumer. Its conclusion is Mathlib's
RiemannHypothesis, but the displayed arithmetic hypothesis is not discharged.

## Verified finite omitted-coordinate screening

For each i, let z_i be the actual Q-Riesz representer of the continuous
Möbius coefficient functional qCoefficientCLM(i+2). If i+2 is nonsquarefree,
the existing coefficient theorem and mu(i+2)=0 give

    <z_i,f>=0 for every f in V_N,
    <z_i,1>=0,
    <r_N,z_i>=0.

These facts are verified in omittedVector_inner, omitted_stage,
residual_inner_omitted, and residualized_inner_omitted.

For any finite list d:Fin M->Nat of omitted indices, repeated entries allowed,
put z_j=omittedVector(d_j) and
D_j=qCoefficientCLM(d_j+2)(Bk_N,n).
The theorem exists_omitted_screening constructs normal coefficients c satisfying

    sum_j <z_i,z_j> c_j = D_i.

There is no unresolved inverse or invertibility assumption. The complete exact
energy and coupled estimate are

    ||u_N,n-sum_j c_j z_j||^2 = Lambda_N,n-sum_j c_j D_j,
    |b_N(n)|^2 <= epsilon_N*(Lambda_N,n-sum_j c_j D_j).

The generic geometry lives in Analysis/OrthogonalKernelScreening.lean:
rankOne_norm_sq, pairing_sq_le_rankOne, and pairing_sq_le_finite.
The application uses the repository's existing finiteSchur_exists_normal
and finiteSchurResidual_norm_sq.

This family theorem removes an arbitrary finite collection of *proved*
target-orthogonal arithmetic constraints. It does not select a family that
makes the remaining energy uniformly bounded.

## Complete-sum diagnostics, not certified bounds

ArithmeticKernelScreeningDiagnostics20261025.md contains the reproducible Python
source and raw JSON results. Save its Python block as squarefree_kernel_screening.py.
Requirements are Python, NumPy, and SciPy. For example:

    OPENBLAS_NUM_THREADS=1 python squarefree_kernel_screening.py --stages 20 40 80

Every physical Gram sum is reduced to a finite period using digamma/trigamma,
including the B and B^2 weights; there is no finite physical-tail replacement.
The numerical evaluation uses IEEE float64. Cancellation, conditioning, and
finite-stage sampling prevent interpreting these values as proofs.

For L-periodic factors, set a=1,...,L and x=a+kL. The complete weights are

    S0=psi_1(a/L)/L^2,
    S1=S0+[psi(a/L)-psi((a+1)/L)]/L,
    S2=[psi_1(a/L)+psi_1((a+1)/L)]/L^2
       +2[psi(a/L)-psi((a+1)/L)]/L.

They sum respectively 1/x^2, 1/[x^2(x+1)], and 1/[x^2(x+1)^2].
Wolfram independently checked the rational partial fractions, ||z||^2=5*pi^2,
and ell_4(Bg_2)=1/8. These computational checks are not Lean proofs.

The diagnostic finite constraints use the radical relations below, rather
than an explicitly built list of Möbius coefficient representers.

| N | max epsilon_N Lambda_N,n | After radical constraints through N |
|---:|---:|---:|
| 40 | 0.00119487 | 0.00093721 |
| 80 | 0.00231172 | 0.00186770 |
| 120 | 0.00306308 | 0.00221675 |
| 160 | 0.00300387 | 0.00217669 |
| 240 | 0.00453088 | 0.00349181 |

Maxima are over 1<=n<=N. At N=80, increasing the constraint cutoff to 1280
gives approximately 0.00179771. Improvement is visible; uniform boundedness
has not been inferred from this finite table.

## Ordinary mathematical extensions, not formalized here

For nonsquarefree j, put
z_j=e_j-e_(j-1)-e_rad(j)+e_(rad(j)-1).
The squarefree atoms and the constant target satisfy
Delta f(j)=Delta f(rad(j)), so these are target-orthogonal annihilators.
On any finite head they generate all finite-support annihilator constraints:
the squarefree divisibility matrix is triangular, and a squarefree conductor
larger than the head supplies the linear sequence. The independent omitted
rows account for the complementary dimension.

Let W be the closed intersection of all these kernels. Then 1,V_N,r_N belong
to W, and the exact fully screened energy is

    ||(P_W-P_N)Bk_N,n||^2
      = ||P_W Bk_N,n||^2-||P_N Bk_N,n||^2.

W describes local radical compatibility. Equality W=V is a separate global
norm-density assertion. In particular, finite-head solvability does not prove
that equality or RH. This continuation does not use it.

An explicit orthogonal subfamily takes j=p^2 over odd primes p.
Their supports {p-1,p,p^2-1,p^2} are pairwise disjoint, and

    ||z_(p^2)||^2=zeta(2)*(2p^4-2p+2).

It therefore supplies a direct sum of removable squared scores with explicit
denominators, without any inverse matrix. Formalizing its finite and complete
Bessel subtraction is a focused next task. It still would not supply the
missing bound on the surviving energy.

## Remaining research obligations

1. Prove a stage-uniform bound for the surviving screened energy, retaining
   epsilon_N and the negative original Schur square. The explicit four-site
   bound has a ready consumer; the finite-family identity allows stronger
   arithmetic screening. Neither common bound has a provider.
2. Continue the signed shrinking-head route using the actual full normal
   equations. Legality, radical compatibility, and target-projection geometry
   alone do not provide the needed bound. Do not assume positivity of signed
   forcing tails.
3. Formalize the odd-prime-square orthogonal family if it yields a usable
   summed estimate. Account for the complete infinite remainder.
4. Preserve the handoff's bare-coefficient-response obstruction. The complete
   asymptotic unboundedness proof and its squarefree-pair count were not newly
   formalized here. Do not return to the disproved stronger uniform norm.
5. The optional single sublinear-cutoff selection and matched Pareto
   displacement provider remain at their handoff status; no new proof is
   claimed for them.
6. Only after a sufficient common bound is discharged, assemble an
   assumption-free theorem of exact type RiemannHypothesis.

## Verification and publication boundary

The new source modules imported successfully on the user's Lean server in
job_cj8YxHvo3hIgJbYNmrr54fLKCYFU2F4o (verified=true, 15.759 server-reported seconds).
An earlier coherent candidate also verified in
job_cm-AsSWSY6OswJTBo_dQ54w9JmgirhRX (7.628 seconds).
These durations are verification-job durations, not pure kernel timings.

The final publication uses the required checkpoint, not GitHub-hosted CI.
The final response records its terminal validation and commit. A standard
axiom list does not discharge the conditional uniform-energy premise.
No sorry, admit, project-local axiom, or unsafe declaration is introduced.

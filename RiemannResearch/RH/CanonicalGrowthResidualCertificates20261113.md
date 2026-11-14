# GROW-001: signed residual certificates for the actual canonical lift

13 November 2026. Source: continuation of the user's proof-triage target.
This is an independently derived formalization, without a novelty claim.

**Status:** the finite response certificate is formalized; the uniform eventual
canonical growth provider remains **Open**. No RH conclusion is claimed.

## Actual system and an arbitrary predictor

Let U be synthesis of the repository's joined old/screened-new family.
Let A be its actual nonsymmetric difference-test collocation operator,
and beta its prescribed source from h_M - F_L. These are constructed in
QCRTScreenedCoordinates.lean; their invertibility is already proved.
No physical Gram inverse is substituted for A inverse.

For any proposed coefficient vector z, put

    v = U z,   rho = beta - A z,
    T = U A^{-1},   w_i = T e_i,
    epsilon = sum_i |rho_i| ||w_i||_Q.

Every quantity here uses the old canonical vector, the new target, the
predictor, and the actual finite collocation system. It does not require
the unknown F_M as an input. All norms and inner products include the
complete infinite physical Q tail.

The new application theorems prove

    F_M - (F_L + v) = T rho,
    ||F_M - (F_L + v)||_Q <= epsilon,
    ||T rho||_Q^2 <= (sum_i rho_i^2)(sum_i ||w_i||_Q^2).

The last formula explains exactly which inverse-response cost must accompany
PAPER-001's raw squared-source estimate. Neither its decay nor boundedness
uniformly along admissions has been proved.

## Exact signed energy and a certified upper bound

With e = T rho, the full equality is

    E_M - E_L =
      2<F_L,v>_Q + ||v||_Q^2
      + 2<F_L+v,e>_Q + ||e||_Q^2.

The signed predictor term remains exact. For z=(x,y), Lean identifies it as

    2 c^T G x + x^T G x + y^T H y.

The error terms alone are bounded to obtain

    E_M - E_L <=
      2<F_L,v>_Q + ||v||_Q^2
      + 2 ||F_L+v||_Q epsilon + epsilon^2.

Thus a concrete upper bound on the right-hand side by alpha E_L certifies
E_M <= (1+alpha) E_L for the **actual** canonical vectors. The theorem
canonical_growth_of_residual_certificate is a **conditional research
reduction**: its finite certificate inequality is an explicit hypothesis,
not an established provider.

## Exact old-block elimination

Choose x0 = A00^{-1} beta0 and z0=(x0,0). The checked residual is exactly

    rho(z0) = (0, sigma),
    sigma = beta1 - A10 A00^{-1} beta0.

Consequently its radius reduces to

    epsilon(z0) =
      sum_new j |sigma_j| || U A^{-1} e_(new j) ||_Q.

These full inverse columns contain both the new Schur response and the
compensating old refit. This is not the physical inverse H^{-1}, and A01
and A10 are not identified by transpose.

## Zero cases and row normalization

No division by residual energy, projected-test capacity, or E_L occurs.
Zero radius implies an exact predicted update. Zero Schur source also
gives the exact old-only predictor, including an empty new block.

For positive row scales a_i, multiplying rho_i by a_i and the matching
response column by a_i^{-1} leaves epsilon unchanged. This identity is
proved in FiniteCollocationCertificate.radius_rescaling. Raw conductor
factors therefore cannot create a response gain by coordinate normalization.

## Remaining arithmetic provider

**Open:** construct predictors and certified complete-tail estimates for
the actual LCM prime-power admissions such that

    2<F_L,v>_Q + ||v||_Q^2
      + 2||F_L+v||_Q epsilon + epsilon^2 <= (C/p^k) E_L

eventually with **one fixed C**. A separate finite constant at each stage
does not establish GROW-001. The original signed response estimate itself
also remains open: the error certificate is a sufficient route, and may
be stronger because it bounds the unknown error correlation in absolute value.

Owning modules:
- Analysis/FiniteCollocationCertificate.lean: generic inverse-column
  response, exact signed residual identity, error bounds, zero case and
  positive row-rescaling identity.
- RH/QCRTCanonicalGrowthCertificate.lean: actual CRT instantiation,
  explicit signed old-refit energy, and exact old-only/Schur-source reduction.

## Verification

The owning application module and its generic certificate dependency passed
Bazel/BuildBuddy file check `job_IjsQM_7tpIN-VWcN_Z3ZACiJKXyuMxZI` (106.139 s):
[https://app.buildbuddy.io/invocation/b6c2da7b-0119-49b8-9ed6-12c2ceddc0d0](https://app.buildbuddy.io/invocation/b6c2da7b-0119-49b8-9ed6-12c2ceddc0d0).
Application source SHA-256: `d2fb6b6ec0b9396ec01659b8ca784b5b885209a5b9b4169b83386f5fda2233e8`.
All 30 declarations passed the strict transitive axiom whitelist in
`job_eb19EhAX5_qTVMu7RgtZMvTEeTyNla2l` (38.554 s):
[axiom audit](https://app.buildbuddy.io/invocation/bd60faf6-1b01-4c59-9db6-5ab038e159e8).
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; this is
an allowed set, not a claim that every declaration uses all three.
The final full-project publication checkpoint is separately required.

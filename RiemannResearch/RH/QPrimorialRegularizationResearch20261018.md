# Finite primorial regularization and strict signed certificates

Research record for Christian Noack. October 18, 2026.

## Verified mathematical scope

This continues the three regularization modules published in commit
3db4fb09feec49cd2d7665db1160bdb87ec33520. It formalizes the finite-stage
passage and the strict constant-one budget from Sections 8, 9 and 18 of
Squarefree_Primitive_Energy_Regularization_2026-10-17.

The complete proof candidate passed Lean server job
`job_rz_L1Ad8jRYQFS5IQEDbf72WMpLY6iD2`, exit 0. Three selected axiom
reports (the closure equivalence, fixed-penalty convergence, and RH
certificate consumer) contained only `propext`, `Classical.choice`, and
`Quot.sound`. Project source also passed server job
`job_P_eLBEpaKz8ssfTu89mTobUdIdHLDMKx`, compiling the modified analysis
module, its closure consumer, and the new primorial module. All six selected
axiom reports contained only the standard foundations listed above.
Publication is separately gated by the server checkpoint.

## Physical setup

Work in real L²(Q), Q(n)=1/(zeta(2)n²), n>=1. Extend physical sequences by
F(0)=0 and put Delta F(n)=F(n)-F(n-1), e=Delta 1=e_1. All energies are
complete infinite Q energies.

Let L_M be the product of the first M primes,
V_M=span{g_d: d>1, d divides L_M}, and
H=closure(union_M V_M). The previously verified primorial cofinality
theorems identify union_M V_M with the algebraic squarefree legal span.

For lambda>0 define
\[
J_\lambda(F)=\|\Delta F-e\|_Q^2+\lambda\|F\|_Q^2.
\]
Let u_{M,lambda} be the unique normal solution in V_M, and set
alpha_M(lambda)=J_lambda(u_{M,lambda}). Existence uses the already
verified coercive regularization theorem on the finite-dimensional stage.
It does not assume constant closure or RH.

## Exact stage identities and fixed-penalty convergence

For F in V_M,
\[
J_\lambda(F)=\alpha_M(\lambda)
 +\|\Delta(F-u_{M,\lambda})\|_Q^2
 +\lambda\|F-u_{M,\lambda}\|_Q^2.
\]
For M<=K this specializes to
\[
\alpha_M(\lambda)=\alpha_K(\lambda)
 +\|\Delta(u_{M,\lambda}-u_{K,\lambda})\|_Q^2
 +\lambda\|u_{M,\lambda}-u_{K,\lambda}\|_Q^2.
\]
Thus the optimized objective decreases with stage. This statement makes no
claim that the primitive norm separately decreases with stage.

For every fixed positive lambda and every actual normal solution
u_lambda in H,
\[
u_{M,\lambda}\longrightarrow u_\lambda
\quad\hbox{strongly in }L^2(Q).
\]
This is unconditional, since the closed-space normal solution exists
unconditionally. The proof uses density in the complete objective and the
exact lambda-weighted displacement remainder. It gives no interchange of
M->infinity and lambda->0.

Lean:
- `QPrimorialRegularization.minimizer_normal`
- `QPrimorialRegularization.minimizer_completion`
- `QPrimorialRegularization.nested_value_identity`
- `QPrimorialRegularization.value_antitone`
- `QPrimorialRegularization.minimizer_tendsto`

## The strict finite-stage criterion

Put a=||Delta 1||_Q²=1/zeta(2). If 1 belongs to H, the scaled competitor
t 1, t=a/(a+lambda), has exact objective
\[
J_\lambda(t1)=\frac{a\lambda}{a+\lambda}
 =\lambda-\frac{\lambda^2}{a+\lambda}<\lambda.
\]
The general Lean scalar completion retains the full square:
\[
J_\lambda(c1)=(a+\lambda)
 \left(c-\frac{a}{a+\lambda}\right)^2
 +\frac{a\lambda}{a+\lambda}.
\]
Continuity and primorial cofinality therefore provide a finite stage M>=N
with alpha_M(lambda)<lambda, for any prescribed N and positive lambda.

Consequently, for every positive sequence lambda_N->0,
\[
\boxed{\quad
1\in H\ \Longleftrightarrow\forall N\ \exists M\ge N:\
\alpha_M(\lambda_N)<\lambda_N.
\quad}
\]
This is an exact Lean closure equivalence. The reverse direction obtains
bounded full primitive energy and vanishing derivative error from the
strict objective budgets; no separate norm-bound hypothesis is needed.

Lean:
- `PrimitiveRegularization.scalar_target_completion`
- `PrimitiveRegularization.exists_strict_budget_of_unit_target`
- `QPrimorialRegularization.exists_strict_value`
- `QPrimorialRegularization.squarefree_constant_mem_iff_strict_primorial_budget`

The forward proof uses only qualitative density. The available objective
margin is of order lambda², so no effective stage-growth estimate is
claimed.

## A signed test that avoids a matrix inverse

For any finite legal trial v put
\[
q=\|\Delta v\|_Q^2+\lambda\|v\|_Q^2,
\qquad b=\langle e,\Delta v\rangle_Q.
\]
The following identity is formalized for every real c:
\[
\boxed{qJ_\lambda(cv)=qa-b^2+(qc-b)^2.}
\]
The signed correlation b is retained before squaring; no replacement by
a sum of absolute cross terms is made.

If q>0, choose c=b/q. Then
\[
J_\lambda(cv)=a-\frac{b^2}{q}.
\]
A sufficient strict finite-stage certificate is therefore
\[
\boxed{b^2>(a-\lambda)
 (\|\Delta v\|_Q^2+\lambda\|v\|_Q^2).}
\]
Since cv remains in the same legal stage, its stage minimum is below
lambda. A family of such certificates for positive lambda_N->0 therefore
implies squarefree constant closure and then RH. Stages may be enlarged
cofinally without worsening the objective.

Lean:
- `PrimitiveRegularization.ray_objective_identity`
- `PrimitiveRegularization.exists_strict_budget_of_ray_certificate`
- `QPrimorialRegularization.strict_value_of_ray_certificate`
- `QPrimorialRegularization.riemannHypothesis_of_primorial_ray_certificates`

This criterion is useful for exact coefficient trials and certified full
Q-energy enclosures: exact inversion of the full mixed Gram is unnecessary
for a sufficient upper certificate. The complete primitive energy and its
signed mixed terms still have to be controlled.

## RH interpretation and remaining obligations

The Lean declarations prove closure equivalence and conditional theorems
with conclusion `RiemannHypothesis`. The analytic implication RH =>
squarefree constant closure remains an external literature input: Bagchi,
*On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, Remark 8, https://arxiv.org/abs/math/0607733.
The paper also explains equivalent inverse-square weights.
No new analytic forward bridge is asserted as Lean-verified.

Conditional research reductions:
- `riemannHypothesis_of_strict_primorial_budget`.
- `riemannHypothesis_of_primorial_ray_certificates`.

Open arithmetic provider: construct a specified family with the strict
complete-energy budgets, or prove the signed line certificates at penalties
tending to zero. Derivative density, finite CRT consistency, and pointwise
convergence alone do not discharge this obligation.

Next actions:
1. Test signed Mobius/product-packet trials using the line certificate.
2. Retain the complete primitive Gram, or rigorous complete-series bounds.
3. Quantify stage growth if a positive margin can be proved arithmetically.
4. Do not substitute the divergent zero-penalty optimizer for a
   positive-penalty diagonal family.

RH is not proved by this development.

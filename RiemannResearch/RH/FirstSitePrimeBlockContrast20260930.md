# Full angular block lower certificates

Date: 2026-09-30.
Requested base: 4f4ede96e4e8fd5167f4f389bf03c64ee47670cc.
The workspace also contained its successor 4a7028c1c735b4a45560ea6336ae3c6f27916d2e,
which already supplies exact block scatter, historical drift and two-row
certificates. This continuation extends that verified block framework.

## Outcome and boundary

The new unconditional improvement is a finite all-row contrast lower bound
and a pooled two-subblock lower bound for the actual full angular sum.
Neither supplies an arithmetic growth rate. No divergent lower series,
unbounded capacity, or unconditional RH has been proved.

The reciprocal-prime energy E is not a research target here. No Burnol, PNT,
asymptotic rate or RH-strength hypothesis is imported by the new Lean module.

## Exact source-balanced all-row test

On a block [N,N+k), write w_i=primeSchurWeight(N+i),
a_i=factorialPrimeDelta(N+i), b_i=factorialPrimeError(N+i).
Keep the actual signed screened row
b_i = base_i + sum_{m<N+i} factorialPrimeCrossGram(N+i,m).
Let u=sum w_i a_i^2, x=sum w_i a_i b_i and t=x/u. For any finite test f, put

c_i = f_i - [sum w_j a_j f_j / u] a_i,
D = sum w_i c_i^2,
L = sum w_i c_i b_i,
Q = L^2/D.

Lean proves sum w_i a_i c_i=0, including u=0. The zero-source case
uses the finite Gram inequality with nonnegative weights. Real division by
zero makes Q=0 when D=0. The exact equality is

S = Q + sum w_i [b_i-t a_i-(L/D)c_i]^2,

where S is the existing internal weighted block variance. Hence, for N>0,

sum_{n in [N,N+k)} Gamma_n
  = Q + contrastRemainder + historicalMeanDrift.

Only after this equality do we use nonnegativity to infer
Q <= S <= sum Gamma. This supports many-row signed tests, rather than just a
single selected pair. Choosing f_i=b_i attains Q=S, even at zero variance;
this sharpness identity provides no lower growth.

The complete screened CRT expansion of L is retained. Its equality with
sum w_i c_i schurEta(N+i+1) cancels the aligned source exactly, using the
balance identity. No individual screened matrix entry is replaced by its
unscreened negative formula, and no absolute values are taken before cancellation.

## Pooled subblock determinant

Split a block into consecutive lengths k,l. Let (u_L,x_L,S_L) and
(u_R,x_R,S_R) be their exact source, signed cross and variance budgets.
When u_L,u_R>0, the established finite equality is

S_parent = S_L + S_R + H_split,
H_split = [u_L u_R/(u_L+u_R)] (x_R/u_R-x_L/u_L)^2.

The full angular equality keeps both child scatters, H_split and the parent's
historical mean drift. If v>=0 and v<=u_L,u_R, Lean proves

sum Gamma >= (v/2) (x_R/u_R-x_L/u_L)^2.

At v=0 this is the unconditional nonnegative ceiling from below; no prime
in either child is assumed. At v>0 the finite lower-source hypotheses give
positive child sources. Every factorial/Schur weight and screened signed
cross sum appears in the displayed certificate.

## Exact capacity accounting

For arbitrary dyadic tests, the new equality is

C_(2^J+1) = C_1 + R_(2^J)
  + sum_{j<J} Q_j + sum_{j<J} contrastRemainder_j
  + sum_{j<J} historicalMeanDrift_j + J_(2^J).

The physical tail is already included in the underlying exact Schur
quantities. Initial capacity and every nonprime gain remain present.
The original C_(N+1)=C_1+R_N+sum Gamma_n+J_N remains intact.

## Open arithmetic step

A nonsummable sequence of actual Q_j suffices for angular nonsummability
and capacity divergence. This is an explicit conditional reduction, not a
provider. The theorem riemannHypothesis_of_dyadic_prime_contrast keeps
nonsummability as its sole substantive growth hypothesis.

A concrete alternative splits [2^(j+1),2^(j+2)) into two equal halves.
The theorem riemannHypothesis_of_dyadic_split_gap keeps the following inputs
explicit: nonnegative v_j, v_j below both actual source budgets,
d_j^2 below the square of the actual pooled slope difference, and
nonsummability of (v_j/2)d_j^2. Finite initial blocks may use v_j=d_j=0.

For example, *if separately proved* eventually v_j>=a(j+1) and
|x_R/u_R-x_L/u_L|>=b/(j+1), with a,b>0, the certificate has a
harmonic lower bound ab^2/[2(j+1)]. This is a sufficient target, not a
claimed asymptotic. The source estimate alone would not establish it.
Pooled separation is not necessary for RH: divergence can occur in internal
scatter, historical drift, the running mean channel or nonprime gains.

Why the available structural formulas do not close the step: weighted
orthogonality, positive source weights and a divergent source are compatible
in abstract regression with b_i=-a_i, giving zero centered scatter and zero
contrasts. This is not a statement about the actual arithmetic rows. It
shows why those rows require a further signed correlation estimate, beyond
PNT source size or an upper large-sieve inequality.

## Verification

A coherent ephemeral Lean candidate passed with exit code 0. Axiom inspection
of the block contrast equality, exact dyadic capacity formula, split-gap bound
and both RH implication theorems reported only propext, Classical.choice
and Quot.sound. These axiom reports do not discharge their explicit local
arithmetic hypotheses. Final project acceptance and publication use the
checkpoint's changed-module and reverse-dependent validation.

Modules:
- Analysis/WeightedScalarEnergy.lean: balanced contrast completion and balancing.
- RH/ParetoFirstSitePrimeBlockContrast.lean: actual screened block tests,
  sharpness, exact capacity, pooled mean lower bound and conditional endpoints.

Source for these finite identities: elementary weighted projection and
regression square completion, developed for the user's continuation.

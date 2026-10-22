# Actual zero density: optimized signed-tail certificates

Research date: 2026-10-05. Starting repository commit: 81ecb78.

## Exact objects

Every actual zero rho=beta+i gamma with 0<gamma<=T is counted with its
analytic multiplicity. Set N=N(T), a=beta-1/2, x_n=log n-log(d)/2.
The original complex convention is unchanged:

H_nm=N^(-1) sum_rho cosh(a(log n-log m)) exp(+i gamma(log n-log m)).

The conjugated analysis rows give exactly H[f]=||Cf||^2-||Sf||^2.
All coordinates 1,...,d and their composite interactions remain.

For the strict bad mask |a|>delta, the existing finite theorem gives

    ||H_bad|| <= Budget <= (strictTail(T,delta)/N)*W_d,
    W_d=(d+sqrt(d(d+1)H_d/2))/2,  H_d=sum_(n<=d)1/n.

The two individual row eigenvalues are
(d +/- sqrt(S_d(2a)S_d(-2a)))/(2N). The negative eigenvalue is retained.

## Published uniform count increment, without discarding the initial count

Let H0=3*10^12, L=log T, s=sigma-1/2, v(s)=4s/(3-2s).
Chourasiya--Simonic, arXiv:2507.15184v2, Theorem 1 and the proof of
Corollary 1 give, uniformly for T>=H0 and 0<=s<=1/32,

    N(1/2+s,T)-N(1/2+s,H0)
      <=5.069*T^(1-v(s))*L^(3-v(s))+9.461*L^2+167.8*L.

The numerical constants come from their first table interval.
For s>0.28/L, admissible sigma_1>1/2+0.28/L is dominated by the
coefficient values evaluated at 1/2; this is coefficient monotonicity,
not an invalid fixed-height limiting substitution.
The tiny remaining interval uses their trivial-count argument (11).

Retaining N(1/2+s,H0)<=N(H0) avoids any dependence on a finite RH
certificate. Reflection gives strictTail(T,s)<=2*N(1/2+s,T);
the strict and inclusive boundary conventions are different.
The exact source power identity is

    T^(1-v(s))*L^(3-v(s))=T*L^3*exp(-(L+log L)*v(s)).

Source: https://arxiv.org/html/2507.15184v2, Section 2.1, Theorem 1,
Table 1, proof of Corollary 1. The density theorem remains an analytic
formalization obligation; a source citation is not a Lean provider.

## Exact harmonic-cap cutoff, replacing a coarse asymptotic choice

For any M>0, S>=0 define

    delta(M,S)=3*S/(4*M+2*S).

Then M*v(delta(M,S))=S. For t<=1/2 the exact comparison is

    delta(M,S)<=t iff S<=M*v(t).

In particular delta<=1/32 iff 47*S<=2*M. This checks the actual source
interval, rather than silently evaluating an estimate outside its range.

Suppose the inclusive right count at the chosen cutoff obeys

    N(1/2+delta,T)<=K*exp(-M*v(delta))+E.

With N>0 and d>=1 set A=2*K*W_d/N and S=log A+omega>=0.
The exact cutoff above yields

    ||H_bad(T,d,delta)|| <= exp(-omega)+2*E*W_d/N.

Proof: apply reflection and the full signed harmonic cap, expand the two
count terms, and use A*exp(-M*v(delta))=exp(-omega).
This is the smallest cutoff meeting this particular count-only main-term
budget. It does not assert optimality of the weaker directional surplus
provider or of the actual signed operator.

For the published increment use

    M=L+log L,
    K=5.069*T*L^3,
    E=9.461*L^2+167.8*L+N(H0).

Consequently the main tail budget can be prescribed directly. The full
additive remainder 2*E*W_d/N remains in the formula. No initial count,
negative square, or endpoint normalization has been suppressed.

## Uniform growing support and the existing centered threshold

At ell=log d=O(sqrt L), N~T*L/(2*pi), and omega->infinity with
omega=o(sqrt L), one has S=ell+2*log L+(1/2)*log(ell)+O(1)+omega
when ell->infinity. Hence delta*ell/2->3*c^2/8 whenever ell/sqrt L->c,
and the retained additive remainder tends to zero exponentially.

The actual full H tends to I in this support regime by the existing
unconditional signed Landau theorem. Therefore H_good=H-H_bad tends to I.
For z=cosh(3*c^2/8), the saved good-moment and centered-row bounds give

    liminf s_min(V_good)
      >= [2-(z-1)/sqrt(2-z^2)]/(1+z).

This is positive for z<7/5, equivalently

    c<sqrt((8/3)*arcosh(7/5))=1.5205391381485407013...

Adding all complementary phase rows increases phase energy.
This establishes the actual-zero application at paper level from the
published theorem. The analytic density input is not yet Lean-verified.
The exact cutoff improves finite-height efficiency; it does not by itself
increase the leading centered support constant.

## Verification classification

The countCutoff algebra and finite actual operator consumers are kernel-checked
in Analysis/NonlinearZeroDensityRate.lean and Analysis/ActualHyperbolicDensityBudget.lean. Their count estimate is an explicit substantive
hypothesis. The underlying Littlewood/Gabriel/mollifier/fourth-moment
density proof and the physical screened Pareto transfer remain Open.

Wolfram checked the exact inverse rate, the condition 47*S<=2*M, and
the main-term exponential cancellation. Numerical checks supplement,
rather than replace, the written proof and Lean verification.

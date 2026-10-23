# Ramanujan dual transfers 11–20

Source: user-requested continuation, 23 October 2026. Each numbered transfer
is verified on the Lean server and published separately to main.

The complete P and Q metrics, signed arithmetic terms, and full residuals
are retained. Full RH iff statements explicitly require the open analytic
provider RH -> BaezDuarte.NaturalApproximation unless a checked provider is
supplied. No saturation or RH assertion follows from a change of coordinates.
The residue dictionary approximating +1 has target coefficients -mu(d).

## Transfer 11: normalized legal optimizers and attained variance floor

Every nonempty canonical packet family has strictly positive mass M_n.
U_n=F_(n+1)/M_(n+1) is legal, has mean exactly one, and uniquely minimizes
energy among all mean-one vectors in its entire finite Hilbert span.
The exact identity is ||f||^2=1/M_(n+1)+||f-U_n||^2.
For m<=n, ||U_m-U_n||^2=1/M_(m+1)-1/M_(n+1).
The sequence converges unconditionally to U_inf=P_V1/(1-E_inf).
For every mean-one f in the full closed legal space, the original variance
floor strengthens to the exact attained identity
||f-1||^2=E_inf/(1-E_inf)+||f-U_inf||^2.
Energy(U_n)->1 iff E_inf=0, with the explicit analytic provider for RH iff.
Generic theorem: Analysis/ProjectionMeanOne.lean; consumer: RH/RamanujanUnitMean.lean.

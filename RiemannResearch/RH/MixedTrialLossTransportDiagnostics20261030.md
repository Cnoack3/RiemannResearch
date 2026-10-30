# Mixed-trial loss transport diagnostics

Prepared 30 October 2026. **Exploratory floating point; no interval certification,
new Lean verification, or asymptotic inference.**

The derivation and exact identities are in
[MixedTrialLossTransportResearch20261030.md](MixedTrialLossTransportResearch20261030.md).
Every divisor is retained. The complete infinite Q norm is evaluated by the
periodic trigamma Gram construction, not by truncating physical coordinates.

Save the Python block in [EndpointSourceDiagnostics20261030.md](EndpointSourceDiagnostics20261030.md)
as `endpoint_diagnostics.py`, and the block below as
`mixed_loss_transport_diagnostics.py` in the same directory. Run
`python mixed_loss_transport_diagnostics.py`. Dependencies are NumPy, SciPy,
and threadpoolctl. The finite prime list is sufficient only for the displayed
blocks [1,2), [2,4), and [4,8); extending the stage range requires extending it.

The residual is reconstructed in the full conductor coefficient space. The
old final-head repair and the new final-head projection are computed separately.
The diagnostics check the complete certificate identity, both loss decompositions,
the transported cross pairings, the moving divisor pairing, and the signed Abel
boundary/source-drift expansion. The source-variation bounds are compared using
a common legal anchor (6, 6, and 10, respectively).

On [4,8), the source-drift term is approximately 0.00224816, while the general
bound from the coefficient-defect moment is approximately 0.27557850. The bound
is therefore coarse at this finite scale. Its value is the proved uniform
inequality, not a numerical improvement of the mixed certificate.

## Reproducible source

```python
#!/usr/bin/env python3
"""Exploratory complete-divisor diagnostics; no interval or asymptotic claim.

Save the Python block from EndpointSourceDiagnostics20261030.md as
endpoint_diagnostics.py beside this file. It supplies the complete-period Gram.
"""
import json
import numpy as np
import scipy.linalg as la
from threadpoolctl import threadpool_limits
from endpoint_diagnostics import (
    period_data, optimizer, primorial, squarefree, rows, trial_gain, ZETA2,
    PRIMES, mu_sf
)


def embed(c, source_ds, target_ds):
    out = np.zeros(len(target_ds))
    indices = np.searchsorted(target_ds, source_ds)
    assert np.array_equal(target_ds[indices], source_ds)
    out[indices] = c
    return out


def tangent_project(G, N, c):
    if not N.shape[1]:
        return np.zeros(len(c))
    return N @ la.solve(N.T @ G @ N, N.T @ G @ c, assume_a='pos')


def minimum_head_lift(ds, G, K, target):
    A = rows(np.arange(1, K + 1), ds)
    c0 = la.lstsq(A, target, cond=1e-12)[0]
    N = la.null_space(A, rcond=1e-12)
    c = c0 - tangent_project(G, N, c0)
    return c, N, float(np.max(np.abs(A @ c - target)))


def loss_vector(i):
    L = primorial(2 * i + 2)
    Ln = primorial(2 * i + 4)
    ds, G = period_data(L)
    dn, Gn = period_data(Ln)
    cf, _, Ef, _ = optimizer(L, i + 1)
    ch, Nh, Eh, _ = optimizer(L, i + 2)
    cn, _, En, _ = optimizer(Ln, i + 2)
    if not squarefree(i + 2) or Ln == L:
        # The global certificate uses exact increments at dependent heads;
        # empty added-conductor spaces also have exactly zero loss.
        return dn, np.zeros(len(dn)), {'i': i, 'certificate': En - Ef,
                                     'expected_loss': 0.0}
    p = 2 * i + 3
    x = np.zeros(len(dn))
    x[np.searchsorted(dn, p * ds)] = cf
    x[np.searchsorted(dn, p)] -= np.sum(cf / ds)
    z = np.zeros(len(dn))
    z[np.searchsorted(dn, p)] = 1
    z[np.searchsorted(dn, L)] -= L / p
    old = np.searchsorted(dn, ds)
    Gold = Gn[np.ix_(old, old)]
    gram_discrepancy = float(np.max(np.abs(Gold - G)))

    def screen(c):
        if not Nh.shape[1]:
            return c.copy()
        pc = Nh @ la.solve(Nh.T @ Gold @ Nh,
                          Nh.T @ (Gn @ c)[old], assume_a='pos')
        return c - embed(pc, ds, dn)

    sx, sz = screen(x), screen(z)
    h = embed(ch, ds, dn)
    A, B, C = sx @ Gn @ sx, sx @ Gn @ sz, sz @ Gn @ sz
    u, v = h @ Gn @ sx, h @ Gn @ sz
    gain, alpha, beta, _ = trial_gain(A, B, C, u, v)
    y = alpha * sx + beta * sz
    r = h - cn - y
    return dn, r, {
        'i': i, 'certificate': Eh - Ef - gain,
        'expected_loss': Eh - En - gain,
        'loss_norm_squared': float(r @ Gn @ r),
        'next_head_residual': float(np.max(np.abs(rows(np.arange(1, i+3), dn) @ r))),
        'old_tangent_pairing_residual': float(np.max(np.abs(Nh.T @ (Gn @ r)[old])))
            if Nh.shape[1] else 0.0,
        'gram_embedding_discrepancy': gram_discrepancy,
    }


def block(N):
    K = 2 * N + 1
    df, Gf = period_data(primorial(4 * N + 2))
    r_all, q_all, s_all, rho_all, sigma_all, details = [], [], [], [], [], []
    for i in range(N, 2 * N):
        dn, r, detail = loss_vector(i)
        ds, G = period_data(primorial(2 * i + 2))
        Gn = period_data(primorial(2 * i + 4))[1]
        values = rows(np.arange(1, K + 1), dn) @ r
        s, Nk_old, head_error = minimum_head_lift(ds, G, K, values)
        bi = optimizer(primorial(2*i+2), K)[0]
        hi = bi - optimizer(primorial(2*i+2), i+2)[0]
        eta_b = G @ bi - (primorial(2*i+2)*(G@bi)[-1])/ds
        old_band = (ds > i+2) & (ds <= K)
        r_old = r[np.searchsorted(dn,ds)]
        head_pairing = float(hi @ G @ s)
        band_pairing = float(r_old[old_band] @ eta_b[old_band])
        sn = embed(s, ds, dn)
        q = r - sn
        Nk_new = la.null_space(rows(np.arange(1, K + 1), dn), rcond=1e-12)
        rho = tangent_project(Gn, Nk_new, r)
        sigma = r - rho
        for v, collection in [(r,r_all),(q,q_all),(sn,s_all),
                               (rho,rho_all),(sigma,sigma_all)]:
            collection.append(embed(v, dn, df))
        band = (dn > i+2) & (dn <= K)
        band_head = -np.array([sum(r[(dn > i+2) & (dn <= n)])
                               for n in range(1,K+1)])
        old_orth = (float(np.max(np.abs(Nk_old.T @ (Gn @ q)[np.searchsorted(dn, ds)])))
                    if Nk_old.shape[1] else 0.0)
        detail.update({
            'old_repair_energy': float(sn @ Gn @ sn),
            'moving_head_pairing': head_pairing,
            'moving_head_pairing_from_divisors': band_pairing,
            'moving_head_pairing_identity_error': head_pairing-band_pairing,
            'signed_head_work': float(s @ G @ s + 2*head_pairing),
            'transported_energy': float(q @ Gn @ q),
            'new_projection_energy': float(rho @ Gn @ rho),
            'new_repair_energy': float(sigma @ Gn @ sigma),
            'physical_head_repair_lower_bound': float(np.sum(values**2 /
                                             (ZETA2*np.arange(1,K+1)**2))),
            'old_repair_head_error': head_error,
            'old_repair_residual_pairing': float(r @ Gn @ sn),
            'transported_old_tangent_pairing_residual': old_orth,
            'band_head_formula_error': float(np.max(np.abs(values-band_head))),
            'band_residual_coefficients': [[int(d),float(c)] for d,c in zip(dn[band],r[band])],
        })
        details.append(detail)
    R, Q, S, P, Z = map(np.stack, [r_all,q_all,s_all,rho_all,sigma_all])
    dot = lambda v: float(v @ Gf @ v)
    loss = sum(map(dot,R))
    repair = sum(map(dot,S))
    transported = dot(np.sum(Q,axis=0))
    new_repair = sum(map(dot,Z))
    projected = dot(np.sum(P,axis=0))
    qgram, rgram = Q @ Gf @ Q.T, R @ Gf @ R.T
    offdiag = lambda X: X - np.diag(np.diag(X))
    Ef = optimizer(primorial(4*N+2),K)[2]
    Ei = optimizer(primorial(2*N+2),N+1)[2]
    d0, G0 = period_data(primorial(2*N+2))
    b0 = optimizer(primorial(2*N+2),K)[0]
    f0 = optimizer(primorial(2*N+2),N+1)[0]
    ff = optimizer(primorial(4*N+2),K)[0]
    base_cost = float((b0-f0) @ G0 @ (b0-f0))
    period_vector = embed(b0,d0,df)-ff
    period_gain = dot(period_vector)
    signed_work = sum(d['signed_head_work'] for d in details)
    remaining_square = dot(period_vector-np.sum(Q,axis=0))
    common_source = float(period_vector @ Gf @ np.sum(Q,axis=0))
    source_drift = drift_diagnostics(N, df, Gf, R)
    return {'interval':[N,2*N], 'final_head':K, 'loss_sum':loss,
        'old_repair_sum':repair, 'transported_sum_norm_squared':transported,
        'old_repair_identity_error': loss-transported+repair,
        'new_repair_sum':new_repair, 'projected_sum_norm_squared':projected,
        'new_repair_identity_error':loss-projected-new_repair,
        'raw_residual_gram':rgram.tolist(), 'transported_residual_gram':qgram.tolist(),
        'max_transported_off_diagonal':float(np.max(np.abs(offdiag(qgram)))),
        'max_projected_off_diagonal':float(np.max(np.abs(offdiag(P@Gf@P.T)))),
        'certificate_sum':sum(d['certificate'] for d in details),
        'actual_energy_increment':Ef-Ei,
        'initial_final_head_cost':base_cost,
        'fixed_final_head_period_gain':period_gain,
        'signed_head_work_sum':signed_work,
        'remaining_global_square':remaining_square,
        'head_work_upper_bound':base_cost+signed_work,
        'global_signed_formula':base_cost+signed_work-remaining_square,
        'global_signed_formula_error':base_cost+signed_work-remaining_square-sum(d['certificate'] for d in details),
        'common_source_pairing':common_source,
        'common_source_identity_error':loss-common_source-sum(d['moving_head_pairing'] for d in details),
        'source_drift': source_drift,
        'certificate_completion_error':sum(d['certificate'] for d in details)-(Ef-Ei)-loss,
        'stages':details}


def drift_diagnostics(N, df, Gf, residuals):
    K = 2*N+1
    t = 6 if N == 1 else 2*next(p for p in PRIMES if N < p <= 2*N)
    band = df[(df>N+1)&(df<=K)]
    mu = np.array([mu_sf(int(d)) for d in band])
    band_indices = np.searchsorted(df,band)
    W = np.zeros((len(band),len(df)))
    W[np.arange(len(band)),band_indices] = 1
    W[:,np.searchsorted(df,t)] -= t/band
    phis, actuals, hats = [], [], []
    for i in range(N,2*N+1):
        L = primorial(2*i+2)
        ds = period_data(L)[0]
        phis.append(embed(optimizer(L,K)[0],ds,df))
        actuals.append(embed(optimizer(L,i+1)[0],ds,df))
        if i<2*N:
            hats.append(embed(optimizer(L,i+2)[0],ds,df))
    phis, actuals, hats = map(np.stack,[phis,actuals,hats])
    delta = phis[:-1]-phis[1:]
    gains = np.einsum('ij,jk,ik->i',delta,Gf,delta)
    eta = phis @ Gf @ W.T
    drift = eta[1:]-eta[:-1]
    selected = gains > 1e-24  # Only a numerical zero guard, not a proof cutoff.
    bessel = np.sum(drift[selected]**2/gains[selected,None],axis=0)
    test_norms = np.einsum('ij,jk,ik->i',W,Gf,W)
    boundary = float((actuals[0,band_indices]+mu)@eta[0])
    weighted_drift = float(np.sum((actuals[1:,band_indices]+mu)*drift))
    # The exact negative period gain at dependent heads is represented by
    # the full gain vector, since residuals there are exactly zero by definition.
    ys = hats-actuals[1:]-residuals
    head_steps = hats-actuals[:-1]
    remaining_work = float(np.sum((head_steps[:,band_indices]-ys[:,band_indices])*eta[:-1]))
    pairing = float(np.sum(residuals[:,band_indices]*eta[:-1]))
    moment = float(np.sum(gains*np.sum((actuals[1:,band_indices]+mu)**2,axis=1)))
    return {'anchor':t, 'band':band.tolist(),
        'fixed_head_gain_squares':gains.tolist(),
        'weighted_dual_variation':bessel.tolist(),
        'test_norm_squares':test_norms.tolist(),
        'elementary_test_norm_bounds':(t*t/(ZETA2*band*band*(band-1))).tolist(),
        'source_total_variations':np.sum(np.abs(drift),axis=0).tolist(),
        'bessel_total_variation_bounds':np.sqrt(sum(gains)*test_norms).tolist(),
        'boundary_pairing':boundary, 'signed_source_drift':weighted_drift,
        'signed_head_and_trial_work':remaining_work,
        'divisor_pairing':pairing,
        'abel_identity_error':pairing-boundary-weighted_drift-remaining_work,
        'coefficient_defect_moment':moment,
        'uniform_drift_bound_N_ge_2':4*np.sqrt(moment/ZETA2) if N>=2 else None}


if __name__ == '__main__':
    with threadpool_limits(limits=4):
        print(json.dumps({'classification':'Exploratory float64, complete periodic Q norm; not rigorous bounds',
                          'blocks':[block(N) for N in [1,2,4]]}, indent=2))
```

## Recorded output

```json
{
  "classification": "Exploratory float64, complete periodic Q norm; not rigorous bounds",
  "blocks": [
    {
      "interval": [
        1,
        2
      ],
      "final_head": 3,
      "loss_sum": 0.02087256153237102,
      "old_repair_sum": 1.5806565287133842e-31,
      "transported_sum_norm_squared": 0.020872561532371017,
      "old_repair_identity_error": 3.469446951953772e-18,
      "new_repair_sum": 1.6282578074540449e-31,
      "projected_sum_norm_squared": 0.020872561532371013,
      "new_repair_identity_error": 6.938893903907066e-18,
      "raw_residual_gram": [
        [
          0.02087256153237102
        ]
      ],
      "transported_residual_gram": [
        [
          0.020872561532371017
        ]
      ],
      "max_transported_off_diagonal": 0.0,
      "max_projected_off_diagonal": 0.0,
      "certificate_sum": 0.08786075488745507,
      "actual_energy_increment": 0.06698819335508321,
      "initial_final_head_cost": 0.2522496786711301,
      "fixed_final_head_period_gain": 0.18526148531604705,
      "signed_head_work_sum": 1.5806565287133837e-31,
      "remaining_global_square": 0.16438892378367567,
      "head_work_upper_bound": 0.2522496786711301,
      "global_signed_formula": 0.0878607548874544,
      "global_signed_formula_error": -6.661338147750939e-16,
      "common_source_pairing": 0.020872561532371225,
      "common_source_identity_error": -2.0469737016526324e-16,
      "source_drift": {
        "anchor": 6,
        "band": [
          3
        ],
        "fixed_head_gain_squares": [
          0.1852614853160471
        ],
        "weighted_dual_variation": [
          0.04962676490988904
        ],
        "test_norm_squares": [
          0.17154659411998846
        ],
        "elementary_test_norm_bounds": [
          1.2158542037080533
        ],
        "source_total_variations": [
          0.0958849736853295
        ],
        "bessel_total_variation_bounds": [
          0.17827219869508015
        ],
        "boundary_pairing": -0.25224967867112985,
        "signed_source_drift": -3.193611165030902e-17,
        "signed_head_and_trial_work": 0.2522496786711298,
        "divisor_pairing": -1.1547463415389894e-16,
        "abel_identity_error": 0.0,
        "coefficient_defect_moment": 2.0551716985641483e-32,
        "uniform_drift_bound_N_ge_2": null
      },
      "certificate_completion_error": 8.326672684688674e-16,
      "stages": [
        {
          "i": 1,
          "certificate": 0.08786075488745507,
          "expected_loss": 0.020872561532371853,
          "loss_norm_squared": 0.02087256153237102,
          "next_head_residual": 4.839878497975292e-16,
          "old_tangent_pairing_residual": 0.0,
          "gram_embedding_discrepancy": 5.551115123125783e-17,
          "old_repair_energy": 1.5806565287133842e-31,
          "moving_head_pairing": 0.0,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 0.0,
          "signed_head_work": 1.5806565287133837e-31,
          "transported_energy": 0.020872561532371017,
          "new_projection_energy": 0.020872561532371013,
          "new_repair_energy": 1.6282578074540449e-31,
          "physical_head_repair_lower_bound": 1.4339150806025163e-31,
          "old_repair_head_error": 4.930380657631324e-32,
          "old_repair_residual_pairing": 7.2938575583940165e-19,
          "transported_old_tangent_pairing_residual": 0.0,
          "band_head_formula_error": 4.839878497975292e-16,
          "band_residual_coefficients": []
        }
      ]
    },
    {
      "interval": [
        2,
        4
      ],
      "final_head": 5,
      "loss_sum": 0.0,
      "old_repair_sum": 0.0,
      "transported_sum_norm_squared": 0.0,
      "old_repair_identity_error": 0.0,
      "new_repair_sum": 0.0,
      "projected_sum_norm_squared": 0.0,
      "new_repair_identity_error": 0.0,
      "raw_residual_gram": [
        [
          0.0,
          0.0
        ],
        [
          0.0,
          0.0
        ]
      ],
      "transported_residual_gram": [
        [
          0.0,
          0.0
        ],
        [
          0.0,
          0.0
        ]
      ],
      "max_transported_off_diagonal": 0.0,
      "max_projected_off_diagonal": 0.0,
      "certificate_sum": 0.006743617170223315,
      "actual_energy_increment": 0.006743617170223315,
      "initial_final_head_cost": 0.02610766545929632,
      "fixed_final_head_period_gain": 0.01936404828907494,
      "signed_head_work_sum": 0.0,
      "remaining_global_square": 0.01936404828907494,
      "head_work_upper_bound": 0.02610766545929632,
      "global_signed_formula": 0.006743617170221379,
      "global_signed_formula_error": -1.9359513991901167e-15,
      "common_source_pairing": 0.0,
      "common_source_identity_error": 0.0,
      "source_drift": {
        "anchor": 6,
        "band": [
          5
        ],
        "fixed_head_gain_squares": [
          0.01936404828907491,
          0.0
        ],
        "weighted_dual_variation": [
          0.00193786195143475
        ],
        "test_norm_squares": [
          0.04468054674932945
        ],
        "elementary_test_norm_bounds": [
          0.21885375666744958
        ],
        "source_total_variations": [
          0.006125753211250307
        ],
        "bessel_total_variation_bounds": [
          0.029414218752778127
        ],
        "boundary_pairing": -0.026107665459296495,
        "signed_source_drift": 0.004550481426668512,
        "signed_head_and_trial_work": 0.021557184032627977,
        "divisor_pairing": 0.0,
        "abel_identity_error": 6.938893903907228e-18,
        "coefficient_defect_moment": 0.010685426378862632,
        "uniform_drift_bound_N_ge_2": 0.32239008149945375
      },
      "certificate_completion_error": 0.0,
      "stages": [
        {
          "i": 2,
          "certificate": -0.011138126001302262,
          "expected_loss": 0.0,
          "old_repair_energy": 0.0,
          "moving_head_pairing": 0.0,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 0.0,
          "signed_head_work": 0.0,
          "transported_energy": 0.0,
          "new_projection_energy": 0.0,
          "new_repair_energy": 0.0,
          "physical_head_repair_lower_bound": 0.0,
          "old_repair_head_error": 0.0,
          "old_repair_residual_pairing": 0.0,
          "transported_old_tangent_pairing_residual": 0.0,
          "band_head_formula_error": 0.0,
          "band_residual_coefficients": [
            [
              5,
              0.0
            ]
          ]
        },
        {
          "i": 3,
          "certificate": 0.017881743171525577,
          "expected_loss": 0.0,
          "old_repair_energy": 0.0,
          "moving_head_pairing": 0.0,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 0.0,
          "signed_head_work": 0.0,
          "transported_energy": 0.0,
          "new_projection_energy": 0.0,
          "new_repair_energy": 0.0,
          "physical_head_repair_lower_bound": 0.0,
          "old_repair_head_error": 0.0,
          "old_repair_residual_pairing": 0.0,
          "transported_old_tangent_pairing_residual": 0.0,
          "band_head_formula_error": 0.0,
          "band_residual_coefficients": []
        }
      ]
    },
    {
      "interval": [
        4,
        8
      ],
      "final_head": 9,
      "loss_sum": 0.0008440412911831514,
      "old_repair_sum": 1.9970174836546344e-07,
      "transported_sum_norm_squared": 0.0008442409929314528,
      "old_repair_identity_error": 6.407899537185348e-17,
      "new_repair_sum": 1.9410189923271328e-07,
      "projected_sum_norm_squared": 0.0008438471892838471,
      "new_repair_identity_error": 7.162118849244259e-17,
      "raw_residual_gram": [
        [
          0.0006639522534779427,
          9.143695025760228e-08,
          0.0,
          0.0
        ],
        [
          9.143695025769969e-08,
          0.00018008903770520807,
          0.0,
          0.0
        ],
        [
          0.0,
          0.0,
          0.0,
          0.0
        ],
        [
          0.0,
          0.0,
          0.0,
          0.0
        ]
      ],
      "transported_residual_gram": [
        [
          0.0006641519552263106,
          -3.31494814237443e-17,
          0.0,
          0.0
        ],
        [
          -3.2741211543167725e-17,
          0.0001800890377052079,
          0.0,
          0.0
        ],
        [
          0.0,
          0.0,
          0.0,
          0.0
        ],
        [
          0.0,
          0.0,
          0.0,
          0.0
        ]
      ],
      "max_transported_off_diagonal": 3.31494814237443e-17,
      "max_projected_off_diagonal": 3.3509470426327376e-17,
      "certificate_sum": 0.04267188965900098,
      "actual_energy_increment": 0.0418278483678175,
      "initial_final_head_cost": 0.058144338626346756,
      "fixed_final_head_period_gain": 0.0163164902585285,
      "signed_head_work_sum": 0.00015430403906306617,
      "remaining_global_square": 0.015626753006408988,
      "head_work_upper_bound": 0.05829864266540982,
      "global_signed_formula": 0.04267188965900083,
      "global_signed_formula_error": -1.5265566588595902e-16,
      "common_source_pairing": 0.0007669891225254997,
      "common_source_identity_error": 3.013810988966581e-16,
      "source_drift": {
        "anchor": 10,
        "band": [
          6,
          7
        ],
        "fixed_head_gain_squares": [
          0.00978273421633442,
          0.002964433711403364,
          0.0,
          0.0035693223307901355
        ],
        "weighted_dual_variation": [
          0.005516832617835572,
          0.0007562906864221022
        ],
        "test_norm_squares": [
          0.07034018121148858,
          0.046425807045148704
        ],
        "elementary_test_norm_bounds": [
          0.3377372788077926,
          0.20677792580068932
        ],
        "source_total_variations": [
          0.00942079721075334,
          0.0032037318511287105
        ],
        "bessel_total_variation_bounds": [
          0.033877793339005154,
          0.027522831038911417
        ],
        "boundary_pairing": -0.05814433862634693,
        "signed_source_drift": 0.0022481646769356724,
        "signed_head_and_trial_work": 0.05597322611806848,
        "divisor_pairing": 7.705216865730524e-05,
        "abel_identity_error": 8.326672684688674e-17,
        "coefficient_defect_moment": 0.007807628927229137,
        "uniform_drift_bound_N_ge_2": 0.275578496289738
      },
      "certificate_completion_error": 3.3241638608405566e-16,
      "stages": [
        {
          "i": 4,
          "certificate": 0.02312984703942044,
          "expected_loss": 0.0006639522534790309,
          "loss_norm_squared": 0.0006639522534779345,
          "next_head_residual": 4.7338435255062095e-15,
          "old_tangent_pairing_residual": 2.663223522702434e-16,
          "gram_embedding_discrepancy": 1.8041124150158794e-16,
          "old_repair_energy": 1.9970174836546707e-07,
          "moving_head_pairing": 7.705216865735035e-05,
          "moving_head_pairing_from_divisors": 7.705216865725012e-05,
          "moving_head_pairing_identity_error": 1.0023449084628488e-16,
          "signed_head_work": 0.00015430403906306617,
          "transported_energy": 0.0006641519552263022,
          "new_projection_energy": 0.0006637581515786982,
          "new_repair_energy": 1.941018992327156e-07,
          "physical_head_repair_lower_bound": 1.7594132350742756e-07,
          "old_repair_head_error": 5.637851296924623e-18,
          "old_repair_residual_pairing": -1.234589821772398e-18,
          "transported_old_tangent_pairing_residual": 1.6880225791277373e-16,
          "band_head_formula_error": 4.735578248982186e-15,
          "band_residual_coefficients": [
            [
              7,
              -0.0024458534927832842
            ]
          ]
        },
        {
          "i": 5,
          "certificate": 0.023111364950371426,
          "expected_loss": 0.00018008903770445677,
          "loss_norm_squared": 0.00018008903770520162,
          "next_head_residual": 1.2600984107408717e-15,
          "old_tangent_pairing_residual": 3.0150948394517123e-16,
          "gram_embedding_discrepancy": 2.914335439641036e-16,
          "old_repair_energy": 1.1693142652661666e-30,
          "moving_head_pairing": 8.445746790151295e-31,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 8.445746790151295e-31,
          "signed_head_work": 2.8584636232964266e-30,
          "transported_energy": 0.00018008903770520143,
          "new_projection_energy": 0.00018008903770520127,
          "new_repair_energy": 1.4505061449038215e-30,
          "physical_head_repair_lower_bound": 1.1360946148640097e-30,
          "old_repair_head_error": 2.2226806280608544e-18,
          "old_repair_residual_pairing": 3.980633672941033e-20,
          "transported_old_tangent_pairing_residual": 4.834376335007906e-16,
          "band_head_formula_error": 1.5939017073969379e-15,
          "band_residual_coefficients": []
        },
        {
          "i": 6,
          "certificate": 3.3306690738754696e-16,
          "expected_loss": 0.0,
          "old_repair_energy": 0.0,
          "moving_head_pairing": 0.0,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 0.0,
          "signed_head_work": 0.0,
          "transported_energy": 0.0,
          "new_projection_energy": 0.0,
          "new_repair_energy": 0.0,
          "physical_head_repair_lower_bound": 0.0,
          "old_repair_head_error": 0.0,
          "old_repair_residual_pairing": 0.0,
          "transported_old_tangent_pairing_residual": 0.0,
          "band_head_formula_error": 0.0,
          "band_residual_coefficients": []
        },
        {
          "i": 7,
          "certificate": -0.0035693223307912136,
          "expected_loss": 0.0,
          "old_repair_energy": 0.0,
          "moving_head_pairing": 0.0,
          "moving_head_pairing_from_divisors": 0.0,
          "moving_head_pairing_identity_error": 0.0,
          "signed_head_work": 0.0,
          "transported_energy": 0.0,
          "new_projection_energy": 0.0,
          "new_repair_energy": 0.0,
          "physical_head_repair_lower_bound": 0.0,
          "old_repair_head_error": 0.0,
          "old_repair_residual_pairing": 0.0,
          "transported_old_tangent_pairing_residual": 0.0,
          "band_head_formula_error": 0.0,
          "band_residual_coefficients": []
        }
      ]
    }
  ]
}
```

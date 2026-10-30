# Screened and mixed complete-Q diagnostics — 30 October 2026

Classification: exploratory floating point, not interval-certified and not a Lean certificate. Full-period trigamma weights include the entire infinite physical tail. See [research memorandum](ScreenedMixedTrialResearch20261030.md) for definitions, eligible-stage distinctions, and the remaining RH obligation.

The global adjusted columns in the output retain exact negative period gains at nonsquarefree observation sites. They are distinct from summing raw physical competitor bounds at every prime. A repeated run reproduced all seven stage records with largest absolute difference zero in this environment.

## Reproducible source

Save as screened_mixed_trials_diagnostics.py and run with Python, NumPy, SciPy and threadpoolctl. The script uses all divisors and streams period rows; no tail cutoff is used. The solver is floating point and the output is not a certified inequality.

```python
#!/usr/bin/env python3
"""Exploratory complete-Q full-squarefree trial diagnostics (not certified).

Periods are summed exactly in form via trigamma weights, then evaluated in float64.
Every divisor d>1 of primorial(2*i+2) is retained. The actual finite-dimensional
optimizer has head 1 through i+1. All physical tail coordinates enter the Gram.

The matrix construction streams period rows to limit memory. No truncated tail is
used. Floating-point energies, conditioning and head residuals are diagnostics,
not certified inequalities or asymptotic evidence.
"""
import json
from functools import lru_cache
from math import prod
import numpy as np
import scipy.linalg as la
from scipy.special import polygamma, zeta
from threadpoolctl import threadpool_limits

ZETA2 = float(zeta(2))
PRIMES = [2,3,5,7,11,13,17]
CHUNK = 8192


def divisors(L):
    return np.array([d for d in range(2,L+1) if L % d == 0], dtype=np.int64)


def rows(n, ds):
    return np.remainder(n[:,None],ds[None,:])/ds[None,:]


def weights(n, L):
    return polygamma(1,n/L)/(ZETA2*L*L)


@lru_cache(None)
def period_data(L):
    ds=divisors(L)
    G=np.zeros((len(ds),len(ds)))
    for begin in range(1,L+1,CHUNK):
        n=np.arange(begin,min(L+1,begin+CHUNK))
        X=rows(n,ds); w=weights(n,L)
        G += X.T@(w[:,None]*X)
    G=(G+G.T)/2
    return ds,G


@lru_cache(None)
def optimizer(L,H):
    ds,G=period_data(L)
    Ahead=rows(np.arange(1,H+1),ds)
    c0=la.lstsq(Ahead,np.ones(H),cond=1e-12)[0]
    N=la.null_space(Ahead,rcond=1e-12)
    if N.shape[1]:
        TG=N.T@G@N
        c=c0-N@la.solve(TG,N.T@G@c0,assume_a='pos')
    else:
        c=c0
    return c,N,float(c@G@c),float(np.max(np.abs(Ahead@c-1)))


def primorial(cutoff):
    return prod(p for p in PRIMES if p<=cutoff)


def squarefree(n):
    return all(n%(p*p) for p in PRIMES if p*p<=n)


def trial_gain(abar,B,C,u,v):
    det=abar*C-B*B
    alpha=(C*u-B*v)/det
    beta=(abar*v-B*u)/det
    gain=(C*u*u-2*B*u*v+abar*v*v)/det
    return float(gain),float(alpha),float(beta),float(det)


def stage(i):
    L=primorial(2*i+2); Lnew=primorial(2*i+4); H=i+1; p=2*i+3
    ds,G=period_data(L)
    cf,_,E,ef=optimizer(L,H)
    ch,N,Ehat,eh=optimizer(L,H+1)
    cn,_,En,en=optimizer(Lnew,H+1)
    result={'i':i,'head':H,'p':p,'old_period':L,'new_period':Lnew,
       'old_dictionary_dimension':len(ds),'new_dictionary_dimension':len(cn),
       'E':E,'Ehat':Ehat,'Enext':En,'old_head_cost':Ehat-E,
       'actual_full_gain':Ehat-En,'actual_increment':En-E,
       'new_observation_squarefree':squarefree(i+2),
       'max_head_residual':max(ef,eh,en)}
    if L==Lnew:
        result.update({k:En-E for k in ['raw_refined_certificate','screened_certificate',
            'mixed_certificate','mixed_regularized_screened_certificate',
            'mixed_regularized_upper_certificate']})
        return result
    # All needed pairings in the common period; old tangent uses the same Gold.
    cross_x=np.zeros(len(ds)); cross_q=np.zeros(len(ds))
    rawA=rawB=rawC=0.0
    for begin in range(1,Lnew+1,CHUNK):
        n=np.arange(begin,min(Lnew+1,begin+CHUNK)); w=weights(n,Lnew)
        X=rows(n,ds)
        raw=rows(n//p,ds)@cf
        prime=(n%p)/p-(L/p)*((n%L)/L)
        cross_x += X.T@(w*raw); cross_q += X.T@(w*prime)
        rawA += np.dot(w*raw,raw); rawB += np.dot(w*raw,prime); rawC += np.dot(w*prime,prime)
    vx=N.T@cross_x; vq=N.T@cross_q
    if N.shape[1]:
        TG=N.T@G@N
        px=la.solve(TG,vx,assume_a='pos'); pq=la.solve(TG,vq,assume_a='pos')
        screenA=float(vx@px); screenB=float(vx@pq); screenC=float(vq@pq)
    else:
        screenA=screenB=screenC=0.0
    A=float(rawA-screenA); B=float(rawB-screenB); C=float(rawC-screenC)
    u=float(ch@cross_x); v=float(ch@cross_q)
    D=sum(1/(ZETA2*k*k*p)-sum(1/(ZETA2*(p*k+r)**2) for r in range(p)) for k in range(1,H+1))
    A0=E/p-D
    tau=A0/1000  # Same explicit positive regularizer for both variants.
    gm,am,bm,dm=trial_gain(A,B,C,u,v)
    gs,ass,bss,dss=trial_gain(A+tau,B,C,u,v)
    gu,au,bu,du=trial_gain(A0+tau,B,C,u,v)
    result.update({'raw_norm_sq':float(rawA),'screening_energy':screenA,
      'screened_norm_sq':A,'screened_norm_ratio':A/rawA,'prime_norm_sq':C,
      'mixed_gram_entry':B,'self_source':u,'prime_source':v,'head_defect':D,
      'tail_defect':A0-rawA,'A0':A0,'tau':tau,'mixed_determinant':dm,
      'raw_refined_gain':u*u/A0,'raw_exact_gain':u*u/rawA,
      'screened_gain':u*u/A,'prime_gain':v*v/C,
      'mixed_exact_gain':gm,
      'mixed_regularized_screened_guaranteed_gain':gs,
      'mixed_regularized_screened_realized_gain':gs+tau*ass*ass,
      'mixed_regularized_upper_guaranteed_gain':gu,
      'mixed_regularized_upper_realized_gain':gu+(A0+tau-A)*au*au,
      'mixed_coefficients':[am,bm],
      'regularized_screened_coefficients':[ass,bss],
      'regularized_upper_coefficients':[au,bu],
      'raw_refined_certificate':Ehat-E-u*u/A0,
      'screened_certificate':Ehat-E-u*u/A,
      'mixed_certificate':Ehat-E-gm,
      'mixed_regularized_screened_certificate':Ehat-E-gs,
      'mixed_regularized_upper_certificate':Ehat-E-gu,
      'mixed_loss':Ehat-En-gm,
      'regularized_screened_loss':Ehat-En-(gs+tau*ass*ass),
      'regularized_upper_loss':Ehat-En-(gu+(A0+tau-A)*au*au),
      'old_gram_condition_number':float(np.linalg.cond(G)),
      'new_gram_condition_number':float(np.linalg.cond(period_data(Lnew)[1]))})
    return result


def main():
    with threadpool_limits(limits=4):
        stages=[stage(i) for i in range(1,8)]
        keys=['actual_increment','raw_refined_certificate','screened_certificate',
              'mixed_certificate','mixed_regularized_screened_certificate',
              'mixed_regularized_upper_certificate']
        blocks=[]
        for lo,hi in [(1,2),(2,4),(4,8)]:
            sub=[r for r in stages if lo<=r['i']<hi]
            row={'interval':[lo,hi]}
            row.update({k:sum(r[k] for r in sub) for k in keys})
            # Existing global adjusted certificates use the exact negative gain
            # at nonsquarefree observation sites; distinguish from raw trial bounds.
            for key in keys[1:]:
                row['global_adjusted_'+key]=sum(r[key] if r['new_observation_squarefree'] else r['actual_increment'] for r in sub)
            blocks.append(row)
        result={'classification':'Exploratory float64; complete periodic Q norm; not interval-certified',
                'regularizer':'tau=A0/1000 at each prime stage',
                'stages':stages,'dyadic_blocks':blocks}
        print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
```

## Output

```json
{
  "classification": "Exploratory float64; complete periodic Q norm; not interval-certified",
  "regularizer": "tau=A0/1000 at each prime stage",
  "stages": [
    {
      "i": 1,
      "head": 2,
      "p": 5,
      "old_period": 6,
      "new_period": 30,
      "old_dictionary_dimension": 3,
      "new_dictionary_dimension": 7,
      "E": 0.8293945844066188,
      "Ehat": 1.0816442630777496,
      "Enext": 0.896382777761702,
      "old_head_cost": 0.2522496786711308,
      "actual_full_gain": 0.18526148531604758,
      "actual_increment": 0.06698819335508321,
      "new_observation_squarefree": true,
      "max_head_residual": 2.220446049250313e-16,
      "raw_norm_sq": 0.1053141640795782,
      "screening_energy": 0.0,
      "screened_norm_sq": 0.1053141640795782,
      "screened_norm_ratio": 1.0,
      "prime_norm_sq": 0.04468054674932964,
      "mixed_gram_entry": -0.020284127518473798,
      "self_source": 0.10969004431285191,
      "prime_source": -0.06634244936701142,
      "head_defect": 0.05934296947087009,
      "tail_defect": 0.0012217833308754839,
      "A0": 0.10653594741045369,
      "tau": 0.00010653594741045369,
      "mixed_determinant": 0.00429404860233846,
      "raw_refined_gain": 0.11293752121994836,
      "raw_exact_gain": 0.11424774555741415,
      "screened_gain": 0.11424774555741415,
      "prime_gain": 0.09850641740592642,
      "mixed_exact_gain": 0.16438892378367612,
      "mixed_regularized_screened_guaranteed_gain": 0.16431597187716043,
      "mixed_regularized_screened_realized_gain": 0.16438884300380058,
      "mixed_regularized_upper_guaranteed_gain": 0.163490745333931,
      "mixed_regularized_upper_realized_gain": 0.16437667888632868,
      "mixed_coefficients": [
        0.8279627873964702,
        -1.1089377863903107
      ],
      "regularized_screened_coefficients": [
        0.8270459815980044,
        -1.1093539989722672
      ],
      "regularized_upper_coefficients": [
        0.8166751425614892,
        -1.1140621647579374
      ],
      "raw_refined_certificate": 0.13931215745118242,
      "screened_certificate": 0.13800193311371664,
      "mixed_certificate": 0.08786075488745468,
      "mixed_regularized_screened_certificate": 0.08793370679397036,
      "mixed_regularized_upper_certificate": 0.08875893333719981,
      "mixed_loss": 0.020872561532371464,
      "regularized_screened_loss": 0.020872642312247003,
      "regularized_upper_loss": 0.020884806429718905,
      "old_gram_condition_number": 13.3275863460267,
      "new_gram_condition_number": 123.2566022386382
    },
    {
      "i": 2,
      "head": 3,
      "p": 7,
      "old_period": 30,
      "new_period": 210,
      "old_dictionary_dimension": 7,
      "new_dictionary_dimension": 15,
      "E": 0.896382777761702,
      "Ehat": 0.8963827777617042,
      "Enext": 0.8852446517603998,
      "old_head_cost": 2.1094237467877974e-15,
      "actual_full_gain": 0.011138126001304371,
      "actual_increment": -0.011138126001302262,
      "new_observation_squarefree": false,
      "max_head_residual": 2.6645352591003757e-15,
      "raw_norm_sq": 0.0798453020372481,
      "screening_energy": 0.04575983463050294,
      "screened_norm_sq": 0.03408546740674516,
      "screened_norm_ratio": 0.4268938376718041,
      "prime_norm_sq": 0.018456620944404423,
      "mixed_gram_entry": -0.010446608593649973,
      "self_source": 0.014056212136560168,
      "prime_source": -0.01084183268110106,
      "head_defect": 0.04696777776452343,
      "tail_defect": 0.0012416027356144665,
      "A0": 0.08108690477286257,
      "tau": 8.108690477286256e-05,
      "mixed_determinant": 0.0005199709205302255,
      "raw_refined_gain": 0.0024366092179918144,
      "raw_exact_gain": 0.002474498744281924,
      "screened_gain": 0.005796520178827969,
      "prime_gain": 0.00636873543857592,
      "mixed_exact_gain": 0.008595037239233107,
      "mixed_regularized_screened_guaranteed_gain": 0.008588647844816917,
      "mixed_regularized_screened_realized_gain": 0.008595018901934457,
      "mixed_regularized_upper_guaranteed_gain": 0.007202176413905252,
      "mixed_regularized_upper_realized_gain": 0.007723609439929211,
      "mixed_coefficients": [
        0.28111148352732895,
        -0.4283108519876397
      ],
      "regularized_screened_coefficients": [
        0.280304705154942,
        -0.42876749559014604
      ],
      "regularized_upper_coefficients": [
        0.10523722746760211,
        -0.5278572164218269
      ],
      "raw_refined_certificate": -0.002436609217989705,
      "screened_certificate": -0.00579652017882586,
      "mixed_certificate": -0.008595037239230998,
      "mixed_regularized_screened_certificate": -0.008588647844814808,
      "mixed_regularized_upper_certificate": -0.007202176413903143,
      "mixed_loss": 0.0025430887620712644,
      "regularized_screened_loss": 0.0025431070993699144,
      "regularized_upper_loss": 0.00341451656137516,
      "old_gram_condition_number": 123.2566022386382,
      "new_gram_condition_number": 1172.4262926373683
    },
    {
      "i": 3,
      "head": 4,
      "p": 9,
      "old_period": 210,
      "new_period": 210,
      "old_dictionary_dimension": 15,
      "new_dictionary_dimension": 15,
      "E": 0.8852446517603998,
      "Ehat": 0.9031263949319254,
      "Enext": 0.9031263949319254,
      "old_head_cost": 0.017881743171525577,
      "actual_full_gain": 0.0,
      "actual_increment": 0.017881743171525577,
      "new_observation_squarefree": true,
      "max_head_residual": 1.7763568394002505e-15,
      "raw_refined_certificate": 0.017881743171525577,
      "screened_certificate": 0.017881743171525577,
      "mixed_certificate": 0.017881743171525577,
      "mixed_regularized_screened_certificate": 0.017881743171525577,
      "mixed_regularized_upper_certificate": 0.017881743171525577
    },
    {
      "i": 4,
      "head": 5,
      "p": 11,
      "old_period": 210,
      "new_period": 2310,
      "old_dictionary_dimension": 15,
      "new_dictionary_dimension": 31,
      "E": 0.9031263949319254,
      "Ehat": 0.9315412156977876,
      "Enext": 0.9255922897178668,
      "old_head_cost": 0.028414820765862214,
      "actual_full_gain": 0.005948925979920805,
      "actual_increment": 0.02246589478594141,
      "new_observation_squarefree": true,
      "max_head_residual": 2.220446049250313e-15,
      "raw_norm_sq": 0.04973282985201579,
      "screening_energy": 0.0398181327275421,
      "screened_norm_sq": 0.009914697124473688,
      "screened_norm_ratio": 0.19935919902357663,
      "prime_norm_sq": 0.00891603016546516,
      "mixed_gram_entry": -0.0045860316681270025,
      "self_source": 0.006087553856263946,
      "prime_source": -0.006058207050517439,
      "head_defect": 0.03231503316392849,
      "tail_defect": 5.453652332166464e-05,
      "A0": 0.049787366375337455,
      "tau": 4.9787366375337454e-05,
      "mixed_determinant": 6.736805218219435e-05,
      "raw_refined_gain": 0.0007443316377399538,
      "raw_exact_gain": 0.0007451478643621157,
      "screened_gain": 0.003737714978850778,
      "prime_gain": 0.004116391710864566,
      "mixed_exact_gain": 0.005284973726443595,
      "mixed_regularized_screened_guaranteed_gain": 0.005277324040636959,
      "mixed_regularized_screened_realized_gain": 0.0052849236506319185,
      "mixed_regularized_upper_guaranteed_gain": 0.004302363289168207,
      "mixed_regularized_upper_realized_gain": 0.0044587388036306545,
      "mixed_coefficients": [
        0.39326778157321035,
        -0.47719315336644236
      ],
      "regularized_screened_coefficients": [
        0.39069340089063853,
        -0.47851730673032605
      ],
      "regularized_upper_coefficients": [
        0.06258579120687781,
        -0.6472820888854433
      ],
      "raw_refined_certificate": 0.02767048912812226,
      "screened_certificate": 0.024677105787011436,
      "mixed_certificate": 0.02312984703941862,
      "mixed_regularized_screened_certificate": 0.023137496725225255,
      "mixed_regularized_upper_certificate": 0.024112457476694008,
      "mixed_loss": 0.0006639522534772103,
      "regularized_screened_loss": 0.0006640023292888864,
      "regularized_upper_loss": 0.0014901871762901505,
      "old_gram_condition_number": 1172.4262926373683,
      "new_gram_condition_number": 15172.97129795163
    },
    {
      "i": 5,
      "head": 6,
      "p": 13,
      "old_period": 2310,
      "new_period": 30030,
      "old_dictionary_dimension": 31,
      "new_dictionary_dimension": 63,
      "E": 0.9255922897178668,
      "Ehat": 0.9514879993419362,
      "Enext": 0.9485235656305337,
      "old_head_cost": 0.025895709624069396,
      "actual_full_gain": 0.0029644337114024255,
      "actual_increment": 0.02293127591266697,
      "new_observation_squarefree": true,
      "max_head_residual": 2.220446049250313e-15,
      "raw_norm_sq": 0.0432886218753659,
      "screening_energy": 0.037709212892433,
      "screened_norm_sq": 0.005579408982932896,
      "screened_norm_ratio": 0.1288885795208914,
      "prime_norm_sq": 0.006325625176325289,
      "mixed_gram_entry": -0.002660407453483768,
      "self_source": 0.0035301326562801583,
      "prime_source": -0.0033522279013736772,
      "head_defect": 0.02785181853323226,
      "tail_defect": 5.89664927762093e-05,
      "A0": 0.043347588368142106,
      "tau": 4.334758836814211e-05,
      "mixed_determinant": 2.8215482112903815e-05,
      "raw_refined_gain": 0.00028748627178748227,
      "raw_exact_gain": 0.0002878778771663142,
      "screened_gain": 0.002233540614974754,
      "prime_gain": 0.0017764934831747759,
      "mixed_exact_gain": 0.002784344673699638,
      "mixed_regularized_screened_guaranteed_gain": 0.002774644551720084,
      "mixed_regularized_screened_realized_gain": 0.0027842513143155312,
      "mixed_regularized_upper_guaranteed_gain": 0.0018828409894849922,
      "mixed_regularized_upper_realized_gain": 0.0019779668073111067,
      "mixed_coefficients": [
        0.4753420075572387,
        -0.33002658604049856
      ],
      "regularized_screened_coefficients": [
        0.4707670509578324,
        -0.3319507039414418
      ],
      "regularized_upper_coefficients": [
        0.05015763996059634,
        -0.5088490153068514
      ],
      "raw_refined_certificate": 0.025608223352281915,
      "screened_certificate": 0.023662169009094642,
      "mixed_certificate": 0.023111364950369757,
      "mixed_regularized_screened_certificate": 0.023121065072349314,
      "mixed_regularized_upper_certificate": 0.024012868634584406,
      "mixed_loss": 0.00018008903770278754,
      "regularized_screened_loss": 0.00018018239708689427,
      "regularized_upper_loss": 0.0009864669040913188,
      "old_gram_condition_number": 15172.97129795163,
      "new_gram_condition_number": 223037.3218115194
    },
    {
      "i": 6,
      "head": 7,
      "p": 15,
      "old_period": 30030,
      "new_period": 30030,
      "old_dictionary_dimension": 63,
      "new_dictionary_dimension": 63,
      "E": 0.9485235656305337,
      "Ehat": 0.9485235656305341,
      "Enext": 0.9485235656305341,
      "old_head_cost": 3.3306690738754696e-16,
      "actual_full_gain": 0.0,
      "actual_increment": 3.3306690738754696e-16,
      "new_observation_squarefree": false,
      "max_head_residual": 1.7763568394002505e-15,
      "raw_refined_certificate": 3.3306690738754696e-16,
      "screened_certificate": 3.3306690738754696e-16,
      "mixed_certificate": 3.3306690738754696e-16,
      "mixed_regularized_screened_certificate": 3.3306690738754696e-16,
      "mixed_regularized_upper_certificate": 3.3306690738754696e-16
    },
    {
      "i": 7,
      "head": 8,
      "p": 17,
      "old_period": 30030,
      "new_period": 510510,
      "old_dictionary_dimension": 63,
      "new_dictionary_dimension": 127,
      "E": 0.9485235656305341,
      "Ehat": 0.9485235656305312,
      "Enext": 0.9449542432997429,
      "old_head_cost": -2.886579864025407e-15,
      "actual_full_gain": 0.003569322330788327,
      "actual_increment": -0.0035693223307912136,
      "new_observation_squarefree": false,
      "max_head_residual": 2.220446049250313e-15,
      "raw_norm_sq": 0.033953246534830506,
      "screening_energy": 0.029659456437960356,
      "screened_norm_sq": 0.0042937900968701495,
      "screened_norm_ratio": 0.12646184194684945,
      "prime_norm_sq": 0.005185517480285284,
      "mixed_gram_entry": -0.003245130854924047,
      "self_source": 0.0036833380112265414,
      "prime_source": -0.0032631064327426048,
      "head_defect": 0.021774840025756796,
      "tail_defect": 6.74173000323533e-05,
      "A0": 0.03402066383486286,
      "tau": 3.4020663834862856e-05,
      "mixed_determinant": 1.1734649338415927e-05,
      "raw_refined_gain": 0.0003987864249445791,
      "raw_exact_gain": 0.0003995782521423623,
      "screened_gain": 0.0031596744598287657,
      "prime_gain": 0.0020533849576031835,
      "mixed_exact_gain": 0.0032437473329637854,
      "mixed_regularized_screened_guaranteed_gain": 0.003226116878137133,
      "mixed_regularized_screened_realized_gain": 0.0032434862083316326,
      "mixed_regularized_upper_guaranteed_gain": 0.0021375019085720206,
      "mixed_regularized_upper_realized_gain": 0.002215674735644846,
      "mixed_coefficients": [
        0.7252714614452367,
        -0.1753934180086447
      ],
      "regularized_screened_coefficients": [
        0.7145294672401553,
        -0.18211582844711216
      ],
      "regularized_upper_coefficients": [
        0.051251303993041855,
        -0.5971996539541741
      ],
      "raw_refined_certificate": -0.00039878642494746566,
      "screened_certificate": -0.0031596744598316523,
      "mixed_certificate": -0.003243747332966672,
      "mixed_regularized_screened_certificate": -0.0032261168781400197,
      "mixed_regularized_upper_certificate": -0.002137501908574907,
      "mixed_loss": 0.00032557499782454166,
      "regularized_screened_loss": 0.00032583612245669445,
      "regularized_upper_loss": 0.0013536475951434809,
      "old_gram_condition_number": 223037.3218115194,
      "new_gram_condition_number": 4178121.613093752
    }
  ],
  "dyadic_blocks": [
    {
      "interval": [
        1,
        2
      ],
      "actual_increment": 0.06698819335508321,
      "raw_refined_certificate": 0.13931215745118242,
      "screened_certificate": 0.13800193311371664,
      "mixed_certificate": 0.08786075488745468,
      "mixed_regularized_screened_certificate": 0.08793370679397036,
      "mixed_regularized_upper_certificate": 0.08875893333719981,
      "global_adjusted_raw_refined_certificate": 0.13931215745118242,
      "global_adjusted_screened_certificate": 0.13800193311371664,
      "global_adjusted_mixed_certificate": 0.08786075488745468,
      "global_adjusted_mixed_regularized_screened_certificate": 0.08793370679397036,
      "global_adjusted_mixed_regularized_upper_certificate": 0.08875893333719981
    },
    {
      "interval": [
        2,
        4
      ],
      "actual_increment": 0.006743617170223315,
      "raw_refined_certificate": 0.015445133953535872,
      "screened_certificate": 0.012085222992699717,
      "mixed_certificate": 0.00928670593229458,
      "mixed_regularized_screened_certificate": 0.009293095326710769,
      "mixed_regularized_upper_certificate": 0.010679566757622435,
      "global_adjusted_raw_refined_certificate": 0.006743617170223315,
      "global_adjusted_screened_certificate": 0.006743617170223315,
      "global_adjusted_mixed_certificate": 0.006743617170223315,
      "global_adjusted_mixed_regularized_screened_certificate": 0.006743617170223315,
      "global_adjusted_mixed_regularized_upper_certificate": 0.006743617170223315
    },
    {
      "interval": [
        4,
        8
      ],
      "actual_increment": 0.0418278483678175,
      "raw_refined_certificate": 0.05287992605545704,
      "screened_certificate": 0.04517960033627476,
      "mixed_certificate": 0.04299746465682204,
      "mixed_regularized_screened_certificate": 0.043032444919434885,
      "mixed_regularized_upper_certificate": 0.045987824202703836,
      "global_adjusted_raw_refined_certificate": 0.04970939014961329,
      "global_adjusted_screened_certificate": 0.0447699524653152,
      "global_adjusted_mixed_certificate": 0.0426718896589975,
      "global_adjusted_mixed_regularized_screened_certificate": 0.042689239466783685,
      "global_adjusted_mixed_regularized_upper_certificate": 0.04455600378048753
    }
  ]
}
```

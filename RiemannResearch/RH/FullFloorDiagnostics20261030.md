# Complete-period floor-trial diagnostics — 30 October 2026

Exploratory double precision only; no interval enclosure. Every infinite tail is
aggregated by trigamma period weights. Save the following Python code and run
with NumPy/SciPy, for example with OPENBLAS_NUM_THREADS=2.

## Reproducible source

```python
"""Uncertified floating-point complete-period Q calculations; no tail cutoff.
Source: full-squarefree handoff diagnostic, adapted for consecutive stages and
floor dilations of the actual old optimizer and next-head old optimizer.
"""
import json
from math import prod
import numpy as np
from scipy.linalg import solve
from scipy.special import polygamma

ZETA2 = np.pi**2 / 6
PRIMES = [2,3,5,7,11,13,17]
CACHE = {}

def dictionary(cutoff):
    ps = [p for p in PRIMES if p <= cutoff]
    ds = [1]
    for p in ps:
        ds += [p*d for d in ds]
    return prod(ps), np.array(sorted(ds)[1:], dtype=np.int64)

def gram(L, ds):
    if L not in CACHE:
        G = np.zeros((len(ds),len(ds)))
        for start in range(1,L+1,4096):
            r=np.arange(start,min(L+1,start+4096),dtype=np.int64)
            X=(r[:,None]%ds[None,:])/ds[None,:]
            w=polygamma(1,r/L)/(ZETA2*L**2)
            G+=X.T@(w[:,None]*X)
        CACHE[L]=G
    return CACHE[L]

def opt(ds,G,H):
    A=(np.arange(1,H+1)[:,None]%ds[None,:])/ds[None,:]
    C=solve(G,A.T,assume_a='pos')
    N=A@C
    c=C@(np.linalg.pinv(N,rcond=1e-12)@np.ones(H))
    return c, float(c@G@c), float(np.max(np.abs(A@c-1)))

records=[]
for i in range(1,8):
    L,ds=dictionary(2*i+2)
    K,es=dictionary(2*i+4)
    G=gram(K,es)
    idx={int(d):j for j,d in enumerate(es)}
    ix=np.array([idx[int(d)] for d in ds])
    Gold=G[np.ix_(ix,ix)]
    c,E,err=opt(ds,Gold,i+1)
    ch,Eh,errh=opt(ds,Gold,i+2)
    cn,En,errn=opt(es,G,i+2)
    r={'stage':i,'oldPeriod':L,'newPeriod':K,'oldHead':i+1,
       'Eold':E,'Enew':En,'headFirstCost':Eh-E,'actualGain':Eh-En,
       'increment':En-E,'headError':max(err,errh,errn),
       'conditionGram':float(np.linalg.cond(G))}
    p=2*i+3
    if K>L:
        R=np.zeros((len(es),len(ds)))
        for j,d in enumerate(ds):
            R[idx[p*int(d)],j]=1
            R[idx[p],j]=-1/d
        ce=np.zeros(len(es)); ce[ix]=ch
        for tag,coeff,energy in [('oldSelf',c,E),('headFirstSelf',ch,Eh)]:
            v=R@coeff
            S=float(ce@G@v); D=float(v@G@v)
            gain=p*S*S/energy
            H=i+1 if tag=='oldSelf' else i+2
            head_defect=sum(1/(ZETA2*p*k*k)-sum(1/(ZETA2*(p*k+r0)**2)
                for r0 in range(p)) for k in range(1,H+1))
            head_bound=energy/p-head_defect
            head_gain=S*S/head_bound
            r[tag]={'source':S,'normSq':D,'sharpNormBound':energy/p,
                    'baselineGain_float':gain,'rawOptimalGain':S*S/D,
                    'headDefect':head_defect,'headAdjustedNormBound':head_bound,
                    'headAdjustedGain_float':head_gain,
                    'signedCertificate':Eh-E-gain,
                    'headAdjustedCertificate':Eh-E-head_gain}
    records.append(r)
    print(json.dumps(r),flush=True)
for lo,hi in [(1,2),(2,4),(4,8)]:
    block=[r for r in records if lo<=r['stage']<hi]
    # Both self trials are set to zero at stages without a prime enlargement.
    print(json.dumps({'block':[lo,hi], 'actualIncrement':sum(r['increment'] for r in block),
      'oldSelfCertificate':sum(r.get('oldSelf',{}).get('signedCertificate',r['headFirstCost']) for r in block),
      'headFirstSelfCertificate':sum(r.get('headFirstSelf',{}).get('signedCertificate',r['headFirstCost']) for r in block),
      'headAdjustedSelfCertificate':sum(r.get('oldSelf',{}).get('headAdjustedCertificate',r['headFirstCost']) for r in block)}),flush=True)
```

## Observed output

```json
{"stage": 1, "oldPeriod": 6, "newPeriod": 30, "oldHead": 2, "Eold": 0.8293945844066194, "Enew": 0.8963827777617019, "headFirstCost": 0.25224967867113024, "actualGain": 0.1852614853160477, "increment": 0.06698819335508255, "headError": 1.6653345369377348e-15, "conditionGram": 123.25660223863832, "oldSelf": {"source": 0.10969004431285193, "normSq": 0.10531416407957833, "sharpNormBound": 0.1658789168813239, "rawOptimalGain": 0.11424774555741404, "headDefect": 0.05934296947087009, "headAdjustedNormBound": 0.1065359474104538, "headAdjustedGain_float": 0.11293752121994827, "signedCertificate": 0.17971541061846685, "headAdjustedCertificate": 0.13931215745118197, "baselineGain_float": 0.0725342680526634}, "headFirstSelf": {"source": 0.14697501792179885, "normSq": 0.14905979047920992, "sharpNormBound": 0.21632885261554993, "rawOptimalGain": 0.14491940330565523, "headDefect": 0.06211196635745581, "headAdjustedNormBound": 0.15421688625809413, "headAdjustedGain_float": 0.1400732203668087, "signedCertificate": 0.15239403929646672, "headAdjustedCertificate": 0.11217645830432155, "baselineGain_float": 0.09985563937466352}}
{"stage": 2, "oldPeriod": 30, "newPeriod": 210, "oldHead": 3, "Eold": 0.8963827777616997, "Enew": 0.8852446517603993, "headFirstCost": 1.887379141862766e-15, "actualGain": 0.011138126001302262, "increment": -0.011138126001300375, "headError": 1.9984014443252818e-15, "conditionGram": 1172.4262926373672, "oldSelf": {"source": 0.01405621213656024, "normSq": 0.07984530203724792, "sharpNormBound": 0.12805468253738567, "rawOptimalGain": 0.002474498744281955, "headDefect": 0.04696777776452343, "headAdjustedNormBound": 0.08108690477286223, "headAdjustedGain_float": 0.002436609217991849, "signedCertificate": -0.0015429119475584886, "headAdjustedCertificate": -0.0024366092179899618, "baselineGain_float": 0.001542911947560376}, "headFirstSelf": {"source": 0.014056212136560243, "normSq": 0.07984530203724809, "sharpNormBound": 0.12805468253738594, "rawOptimalGain": 0.0024744987442819506, "headDefect": 0.04791153516342826, "headAdjustedNormBound": 0.08014314737395768, "headAdjustedGain_float": 0.0024653024756572718, "signedCertificate": -0.0015429119475584856, "headAdjustedCertificate": -0.0024653024756553844, "baselineGain_float": 0.001542911947560373}}
{"stage": 3, "oldPeriod": 210, "newPeriod": 210, "oldHead": 4, "Eold": 0.8852446517603993, "Enew": 0.9031263949319233, "headFirstCost": 0.01788174317152391, "actualGain": 0.0, "increment": 0.01788174317152391, "headError": 2.4424906541753444e-15, "conditionGram": 1172.4262926373672}
{"stage": 4, "oldPeriod": 210, "newPeriod": 2310, "oldHead": 5, "Eold": 0.9031263949319255, "Enew": 0.9255922897178683, "headFirstCost": 0.028414820765864657, "actualGain": 0.005948925979921804, "increment": 0.022465894785942853, "headError": 3.3306690738754696e-15, "conditionGram": 15172.971297951628, "oldSelf": {"source": 0.006087553856263658, "normSq": 0.049732829852015645, "sharpNormBound": 0.08210239953926596, "rawOptimalGain": 0.0007451478643620474, "headDefect": 0.03231503316392848, "headAdjustedNormBound": 0.049787366375337476, "headAdjustedGain_float": 0.0007443316377398831, "signedCertificate": 0.027963453788031237, "headAdjustedCertificate": 0.027670489128124774, "baselineGain_float": 0.00045136697783342103}, "headFirstSelf": {"source": 0.006531386215713586, "normSq": 0.05206221317085236, "sharpNormBound": 0.08468556506343547, "rawOptimalGain": 0.0008193851797813424, "headDefect": 0.032515699428504526, "headAdjustedNormBound": 0.052169865634930944, "headAdjustedGain_float": 0.0008176943793056389, "signedCertificate": 0.027911086677689666, "headAdjustedCertificate": 0.027597126386559017, "baselineGain_float": 0.0005037340881749898}}
{"stage": 5, "oldPeriod": 2310, "newPeriod": 30030, "oldHead": 6, "Eold": 0.9255922897178673, "Enew": 0.9485235656305322, "headFirstCost": 0.025895709624068508, "actualGain": 0.0029644337114036468, "increment": 0.02293127591266486, "headError": 3.3306690738754696e-15, "conditionGram": 223037.32181151814, "oldSelf": {"source": 0.0035301326562801527, "normSq": 0.04328862187536606, "sharpNormBound": 0.07119940690137441, "rawOptimalGain": 0.00028787787716631226, "headDefect": 0.027851818533232264, "headAdjustedNormBound": 0.04334758836814215, "headAdjustedGain_float": 0.0002874862717874811, "signedCertificate": 0.02572068237154943, "headAdjustedCertificate": 0.025608223352281027, "baselineGain_float": 0.00017502725251907972}, "headFirstSelf": {"source": 0.00362461538815447, "normSq": 0.04505368965063823, "sharpNormBound": 0.07319138456476429, "rawOptimalGain": 0.0002916040132100494, "headDefect": 0.027962466109721473, "headAdjustedNormBound": 0.045228918455042816, "headAdjustedGain_float": 0.00029047426206101046, "signedCertificate": 0.025716209853840485, "headAdjustedCertificate": 0.025605235362007497, "baselineGain_float": 0.0001794997702280246}}
{"stage": 6, "oldPeriod": 30030, "newPeriod": 30030, "oldHead": 7, "Eold": 0.9485235656305322, "Enew": 0.9485235656305313, "headFirstCost": -8.881784197001252e-16, "actualGain": 0.0, "increment": -8.881784197001252e-16, "headError": 2.6645352591003757e-15, "conditionGram": 223037.32181151814}
{"stage": 7, "oldPeriod": 30030, "newPeriod": 510510, "oldHead": 8, "Eold": 0.9485235656305324, "Enew": 0.9449542432997409, "headFirstCost": 7.771561172376096e-16, "actualGain": 0.003569322330792324, "increment": -0.0035693223307915467, "headError": 4.773959005888173e-15, "conditionGram": 4178121.6130938316, "oldSelf": {"source": 0.003683338011226412, "normSq": 0.03395324653483022, "sharpNormBound": 0.05579550386061955, "rawOptimalGain": 0.0003995782521423376, "headDefect": 0.0217748400257568, "headAdjustedNormBound": 0.034020663834862755, "headAdjustedGain_float": 0.0003987864249445523, "signedCertificate": -0.00024315541515303974, "headAdjustedCertificate": -0.00039878642494377514, "baselineGain_float": 0.0002431554151538169}, "headFirstSelf": {"source": 0.003683338011226422, "normSq": 0.03395324653483022, "sharpNormBound": 0.0557955038606196, "rawOptimalGain": 0.00039957825214233976, "headDefect": 0.021816513892067783, "headAdjustedNormBound": 0.033978989968551816, "headAdjustedGain_float": 0.00039927552047609136, "signedCertificate": -0.00024315541515304082, "headAdjustedCertificate": -0.0003992755204753142, "baselineGain_float": 0.00024315541515381798}}
{"block": [1, 2], "actualIncrement": 0.06698819335508255, "oldSelfCertificate": 0.17971541061846685, "headFirstSelfCertificate": 0.15239403929646672, "headAdjustedSelfCertificate": 0.13931215745118197}
{"block": [2, 4], "actualIncrement": 0.006743617170223537, "oldSelfCertificate": 0.016338831223965424, "headFirstSelfCertificate": 0.016338831223965428, "headAdjustedSelfCertificate": 0.01544513395353395}
{"block": [4, 8], "actualIncrement": 0.04182784836781528, "oldSelfCertificate": 0.053440980744426735, "headFirstSelfCertificate": 0.053384141116376224, "headAdjustedSelfCertificate": 0.052879926055461136}
```

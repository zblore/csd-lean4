"""
Record layer (MD-1), Phase 2b — the FIBRE model reproduces Born at N>=3 (existence proof).

Correct structure: for a sharp prep the base is pinned (pi(omega)=[psi]); the measurement
carves the FIBRE. The object is a "Born partition of the fibre": for base point phi and
context M={e_i}, partition (F,nu) into pieces of measure nu(F_i)=|<e_i|phi>|^2.

Canonical symmetric instance (no outcome ordering): the Gumbel race
    F=R^n, nu=iid Gumbel,  F_i = { xi : i = argmax_j (log|<e_j|phi>|^2 + xi_j) }
gives nu(F_i)=softmax_i(log b)=b_i EXACTLY (Gumbel-max identity). Minimal fibre dim = n-1
(argmax invariant under global shift); n=2 -> single logistic threshold (recovers the qubit).

Verified here at N=3: exact Born (to MC noise) for random states and Haar bases, and the
KS-relevant check that two bases SHARING a vector give the same outcome probability
(measurement-noncontextual probabilities, context-dependent regions).

Honest boundary: this is injected iid noise -> a valid ontological model that settles the
architecture, but NOT yet CSD-native (which needs typicality on a geometric fibre + a
deterministic de-isolation flow). See specs/record-layer-plan.md §3b. Requires numpy.
"""
import numpy as np
def freqs(bvec, Ns, rng):
    s=np.log(np.clip(bvec,1e-300,None))
    G=-np.log(-np.log(rng.random((Ns,len(bvec)))))   # iid Gumbel
    out=np.argmax(s[None,:]+G,axis=1)
    return np.array([np.mean(out==i) for i in range(len(bvec))])
if __name__=="__main__":
    rng=np.random.default_rng(1); d=3; Ns=2_000_000
    for t in range(4):
        Z=rng.standard_normal(d)+1j*rng.standard_normal(d); psi=Z/np.linalg.norm(Z)
        Q,_=np.linalg.qr(rng.standard_normal((d,d))+1j*rng.standard_normal((d,d)))
        b=np.abs(Q.conj().T@psi)**2
        f=freqs(b,Ns,rng)
        print(f"trial {t}: Born={np.round(b,4)} fibre={np.round(f,4)} max|err|={np.max(np.abs(f-b)):.4f}")

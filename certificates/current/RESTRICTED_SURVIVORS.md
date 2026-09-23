# Restricted statements that survive

## Full qubit hierarchy

For every qubit density matrix and time-independent Hermitian Hamiltonian, both sides of Eq.(4) hold at every real time. After dropping the scalar part of H and rescaling time, the three complexities have the form

F(mu;t)=mu sin²t+8mu(1-mu)sin⁴(t/2).

Writing z=(p1-p2)² and c=cos²(theta), mu_I=(1-zc)/2 and mu_K=z(1-c)/(1+z). Their difference is (1-z)(1+zc)/(2(1+z))>=0. The U* spread coefficient is mu_S=(1-sqrt(1-z))(1-c)/2, with mu_S<=mu_K. All three coefficients lie in [0,1/2], where F is nondecreasing in mu at every time. Stationary endpoints are included directly, without dividing by a zero complexity. Dimension one is stationary. Consequently the qutrit counterexamples to either side have minimal physical-system dimension three.

This reconstructs, rather than extends, the source's arbitrary-qubit hierarchy. Source: arXiv:2408.00826v4, End Matter and S24–S31; exact checks in verify_1r_bootstrap.py.

## Qubit ratio concentration bound — T2-SURVIVES

This is a restricted byproduct, not an additional central attack statement. For any nonstationary qubit, put y=2sqrt(p1p2) in [0,1), h=sin²(theta)>0. Then

mu_S=(1-y)h/2,  mu_K=(1-y²)h/(2-y²).

After removable recurrence limits, r=F(mu_S;t)/F(mu_K;t) is positive, and the ratio of its largest and smallest temporal values is

kappa=(1-mu_S)/(1-mu_K).

The same range factor applies to q=1/r and to Pq. Since mu_K>=mu_S, kappa increases with h, so

kappa <= (1+y)(2-y²)/2 <= kappa_*=(17+7sqrt(7))/27.

The last maximum occurs at y=(sqrt(7)-1)/3; the second derivative is -1-3y<0 and both endpoint values are one.

For any positive random variable in [m,M], positivity of E[(X-m)(M-X)] gives Var(X)<=(M-E X)(E X-m). Maximizing the relative variance over its allowed mean yields

CV(X) <= (kappa-1)/(2sqrt(kappa)),  kappa=M/m.

Therefore, for any probability-weighted time average,

**CV(r), CV(q), CV(Pq) <= (kappa_*-1)/(2sqrt(kappa_*)) = 0.1375633885... .**

This is a proved upper bound, not an assertion that the actual maximal qubit CV equals this number. It does not replace the source's example-specific Werner CV by a universal 5% theorem. Completely stationary 0/0 ratios are excluded. The no-go families in dimension four remain consistent with this theorem. The minimum dimension of the temporal no-go phenomenon remains between three and four, not determined here.

Verification: verify_restricted_survivors.py exactly differentiates the range factor, verifies the maximum, and checks the variance inequality's scalar maximization. It also independently verifies the U* symmetric eighth-order gap on a terminating three-node state chain, obtaining 3/2500.

## General state-dependent return bounds

For finite state and operator chain lengths m_S,m_K and nonzero return losses, define A_S=Tr(sqrt(rho(t))sqrt(rho)) and A_K=Tr(rho(t)rho)/P. Bounding nonzero Krylov indices between 1 and m-1 proves

(1-A_S²)/[(m_K-1)(1-A_K²)] <= r <= (m_S-1)(1-A_S²)/(1-A_K²).

These bounds retain information about the two spectral measures. They do not reduce to a purity-only universal comparison. The general factor-two theorem is the stronger corrected universal statement for pure-density-matrix versus state-vector complexity, and is externally known as a tensor-superadditivity corollary.

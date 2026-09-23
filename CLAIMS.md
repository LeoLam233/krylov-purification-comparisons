# Retained manuscript claims and frozen scope

Authority: V3 SHA-256 `aaebb0e5b0768746bbd0c1eccb1fd128534680c54c8377de90e0c58365c29401`.
This index restates the completed manuscript claim map; it makes no new scientific claim.
The full statements and hypotheses remain unchanged in the corrected TeX and original claim map.
Two prose repairs and rebuilt assets are recorded in RELEASE_AUDIT_CHANGES.md.
Notation: r=S_U*/C_M, q=1/r, R=Pq. Common recurrence values use removable continuation.

| Claim | Retained statement / scope | Manuscript locator |
|---|---|---|
| Eq. (4), left | Separate full-rank qutrit: S_U*(pi)=82/441, C_M(pi)=1074/8281; gap 4192/74529 | prop:left |
| Eq. (4), right | Separate full-rank qutrit: C_M(pi/3)=1141425/913952, K_I(pi/3)=2967537/2456246; gap 1600683/39299936; also 0<t<1/2704 | prop:right |
| Qubit hierarchy | Every qubit density matrix, time-independent Hermitian H, every real t, with stationary/degenerate cases; d=3 minimal for either failure | thm:qubit |
| Right perturbation | Fixed rho_R; 0<abs(delta)<1/sqrt(135), each pair fails at sufficiently small positive times; delta=1/20, t=1/20000 has exact lower gap 378247/21125000000000000 | prop:robust |
| Factor two | Finite-dimensional normalized pure seed, Hermitian G, every real t; both purification generators applied separately; prior-art corollary | thm:factor; cor:branches |
| Main ratio | d=4, H=diag(0,2,3,4), uniform T=2pi average, 0<epsilon<=1/4; CV(r)^2 >= 289/(132710400*pi*epsilon)-1; epsilon=10^-10 gives CV(r)>80 | thm:main-ratio |
| Reciprocal | Distinct full-rank family, same d,H,T; eta>0, epsilon=eta^2, 0<epsilon<=1/16; CV(q)^2 >= 1/(1679616*pi*epsilon)-1; CV(Pq)=CV(q); eta=1/100000 gives CV(q)>40 | thm:reciprocal |
| Fixed purity | d=4, H=diag(2,3,0,1), P=1/2, 0<epsilon<5/18; (5/(18*epsilon))*(1-epsilon/10) <= r <= 5/(18*epsilon), every real t after continuation; r and its period mean have no uniform finite upper bound | thm:purity |
| Restricted survivors | Nonstationary qubits: CV(r), CV(q), CV(Pq) <= (kappa*-1)/(2*sqrt(kappa*)), kappa*=(17+7*sqrt(7))/27, any probability-weighted time average; bound not asserted attained | prop:qubit-cv |
| Return comparison | Finite chain lengths and nonzero return losses; state-dependent comparison, not purity-only control | cor:return-comparison |
| Unbounded left ratio | Full-rank qutrit family, real m>=4; all t outside 2pi integers; r(pi)/m^2 -> 1/9; no fixed positive state-independent multiplier repairs the entire class | prop:unbounded-left |

Conjecture 2 is qualitative. Only the displayed universal formulations are ruled out.
No typicality result, absolute priority, unconditional infinite-dimensional theorem,
minimum temporal-CV dimension, or fixed-purity minimum dimension is claimed here.
The factor-two theorem has broader public prior art. The qubit source result is reconstructed.

The [original claim map](paper/CLAIM_SOURCE_MAP.md) and
[reviewed-content snapshot](paper/checks/REVIEWED_CONTENT.json) preserve exact V3 source paths.
Clean-room alternatives remain segregated in
[PROPOSED_NONAUTHORITATIVE_IMPROVEMENTS.md](paper/PROPOSED_NONAUTHORITATIVE_IMPROVEMENTS.md).
No stronger constant has been promoted. Replaying historical byproduct checks does not
add those byproducts to the manuscript claim set.

# Notation map

All statements in the manuscript are finite dimensional. H is time independent and Hermitian; hbar = 1. The V3 convention is retained.

| Manuscript | Meaning | Source convention / distinction |
|---|---|---|
| d | Physical system dimension | Not purification dimension or Krylov-chain length |
| P | Tr(rho squared), conserved under unitary dynamics | Operator seed rho/sqrt(P) |
| vec_r | Row vectorization | vec_r(A) = sum A_ab |a>|b> |
| s | vec_r(sqrt(rho)) in the full-rank canonical coordinates | Already normalized; not vec_r(rho) |
| G_I | H tensor I | Time-independent purification |
| G_U* | H tensor I - I tensor conjugate(H) | Time-dependent purification |
| C_M | C_K(rho(t)) | Normalized mixed operator complexity |
| S_X | C_S(s_X(t)), X = I or U* | State-vector spread complexity |
| K_X | C_K(|s_X(t)><s_X(t)|) | Operator complexity of the rank-one purified density matrix |
| r | S_U*/C_M | Main-text Conjecture 2 ratio |
| q | C_M/S_U* = 1/r | Supplemental reciprocal |
| R | P q | Supplemental Eq. (S.32); never identified with r or q |
| CV(f) | sqrt(<f^2> - <f>^2)/<f> | Recurrence-period mean in the no-go families; arbitrary probability time average only in the qubit theorem |
| T | Common recurrence period, 2 pi for the three ratio families | Distinct from T_4 |
| T_4 | Tr(A_eta^4) | V3 temporal certificate calls this T in one file; renamed to avoid conflict with period |
| D_S, D_K | 1 minus the corresponding normalized return amplitude | D_S is a spread return, not a purified-operator return |
| F(mu;t) | mu sin^2(t) + 8 mu(1-mu) sin^4(t/2) | Three-atom formula, with gap absorbed in time |
| m | Chain length in the general framework; family parameter in Appendix A.2 | Contexts are separate; m_S,m_K are lengths in the return comparison |
| z, c | (p1-p2)^2 and cos^2(theta), in qubit hierarchy | c = cos^2(t/2) is separately local to temporal proofs |
| y, h | 2 sqrt(p1 p2), sin^2(theta) | Qubit variation proof |
| epsilon = eta^2 | Reciprocal-family parameter, with eta > 0 | The families reuse epsilon locally, not a common density matrix |

Rank-deficient endpoint statements use the actual normalized pure seed or explicitly terminated chains. The manuscript does not assert that canonical and minimal purifications coincide for rank-deficient states.

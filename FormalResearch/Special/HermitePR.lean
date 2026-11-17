module

public import FormalResearch.Special.HermitePRPhase
public import FormalResearch.Special.HermitePRDeriv
public import FormalResearch.Special.HermitePRRho

/-!
# Hermite Plancherel–Rotach calculus and ladder bounds

Umbrella for the formalized phase calculus, the exact ladder estimate and the
derivative bound |y_n'| <= C N^(1/4) rho_n^(1/2) (HermitePRRho). The bulk
oscillatory asymptotic (Lemma PR(a)) is `hermite_bulk_PR` (umbrella `HermiteBulk`);
see the imported modules for their precise scope. W1, Lemma lem:PR; Szegő, Theorem 8.22.8; DLMF §18.15(iv).
-/

@[expose] public section

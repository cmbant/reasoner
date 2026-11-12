# Wigner certificate search scripts

Exploratory sympy scripts that found the telescoping certificates (Zeilberger/Gosper style, `F(t) = H(t+1) - H(t)`)
used in `FormalResearch/Wigner/Rec3jKey.lean`, `Rec3m.lean` and `Rec6jKey.lean`
(`ring3j.py`, `ringQ.py`, `symQ.py`: 3j j₁-recurrence and 6j certificate quadratics; `scan.py`, `scan3m.py`,
`ring3m2.py`: scans for the reference exponents and the constant certificate of the m-recurrence;
`atoms3j.py`, `atoms6.py`, `red6j.py`: the atom-variable reductions of the key identities).
They are provenance only. They read pickles/paths from a scratch directory and are not run by any gate;
nothing in Lean depends on them, because Lean re-checks every certificate by `ring`.

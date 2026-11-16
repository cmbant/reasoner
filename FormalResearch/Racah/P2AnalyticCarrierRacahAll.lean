module

public import FormalResearch.Racah.P2AnalyticCarrierRacah
public import FormalResearch.Racah.P2AnalyticLeading6jChambers

/-!
# The `6j` carrier is the even Racah deformation in every chamber (Weyl P2, `eq:carrierRacah6j`,
`lem:evendeformation6j`, `lem:sqrtfreecarrier6j`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:evendeformation6j` (canonical chamber
`m ≥ |n|`) and `lem:sqrtfreecarrier6j`, whose `eq:carrierRacah6j` `P̃_f = k_{6j} q_{f-f_0}(ς; S⁻¹, δ)` is
stated "in the canonical chamber" while `P̃_f` is "the polynomial of the canonically reduced family" in the
other three.  `P2AnalyticCarrierRacah` proves the canonical statement; here every chamber is reduced to it.

## Reduction of the Racah system

The two symmetries of the `6j` symbol that reduce the chambers (`Phi6_swap_ab`, `Phi6_exch_ab`) act on the
labels by `(a,b;m,n) ↦ (b,a;n,m)` and `(a+n,b+m;-m,-n)`.  They preserve `c_min`, `c_max` (so the dimension `D`)
and the integrality conventions: `racahSystem_chamber` shows that if `RacahSystem a b m n D` then
`RacahSystem a' b' M N D` for the reduced data (`chamberSysA`, `chamberSysB`, `chamberM`, `chamberN`), with
`(wA a' N, wB b' M) = (chamberA a b m n, chamberB a b m n)`.  Hence the canonical-chamber theorems apply to
the reduced system, with Jacobi parameters `(M-N, M+N) = (|m-n|, |m+n|)` in every chamber.

* `evenRacah6All`, `carrierPolyAll_eq_kLeadAll_mul_evenRacah6`: the signed carrier polynomial of every
  chamber is `k_{6j} q_d`, `q_d = evenRacah6 M N d` (`eq:carrierRacah6j`, all chambers);
* `lem_evendeformation6_all`: `q_d` is monic of degree `d`, equals `P̂_d^{(|m-n|,|m+n|)}` at zero scale,
  and on every `RacahSystem a b m n D` is a nonzero multiple of the Racah polynomial of the reduced system
  (`A↔B` swapped in chambers III, IV);
* `Phi6_eq_kLeadAll_mul_evenRacah6`: at every physical point `Φ_f = E W Π_f^{-1/2} k_{6j} q_d(ς; A⁻², B⁻², (AB)⁻¹)`
  with the reduced edges, in every chamber.

Not formalised: the analytic estimate `eq:evendeformationbound` (see `P2AnalyticEvenDegree6`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ FormalResearch.Racah.RacahPoly Polynomial

/-! ### The reduced Racah system -/

/-- The reduced first `6j` label of the chamber of `(m,n)`: `a, a+n, b, b+m` in chambers I-IV. -/
noncomputable def chamberSysA (a b m n : ℚ) : ℚ :=
  if |n| ≤ m then a else if |n| ≤ -m then a + n else if |m| ≤ n then b else b + m

/-- The reduced second `6j` label of the chamber of `(m,n)`: `b, b+m, a, a+n` in chambers I-IV. -/
noncomputable def chamberSysB (a b m n : ℚ) : ℚ :=
  if |n| ≤ m then b else if |n| ≤ -m then b + m else if |m| ≤ n then a else a + n

lemma wA_chamberSys (a b m n : ℚ) :
    wA (chamberSysA a b m n) (chamberN m n) = chamberA a b m n := by
  unfold chamberSysA chamberN chamberA
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]; unfold wA; push_cast; ring
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]; unfold wA wB; ring
  · simp only [c1, c2, c3, ↓reduceIte]; unfold wA wB; push_cast; ring

lemma wB_chamberSys (a b m n : ℚ) :
    wB (chamberSysB a b m n) (chamberM m n) = chamberB a b m n := by
  unfold chamberSysB chamberM chamberB
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]; unfold wB; push_cast; ring
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]; unfold wA wB; ring
  · simp only [c1, c2, c3, ↓reduceIte]; unfold wA wB; push_cast; ring

lemma cMin_chamber (a b m n : ℚ) :
    cMin (chamberSysA a b m n) (chamberSysB a b m n) (chamberM m n) (chamberN m n) =
      cMin a b m n := by
  unfold chamberSysA chamberSysB chamberM chamberN cMin
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    rw [show b + m + -m - (a + n) - -n = -(a - b) by ring,
      show a + n - (b + m) = -(b + m - a - n) by ring, abs_neg, abs_neg, max_comm]
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    rw [show b + m - a - n = -(a + n - b - m) by ring, abs_neg, abs_sub_comm a b]
  · simp only [c1, c2, c3, ↓reduceIte]
    rw [show a + n + -n - (b + m) - -m = a - b by ring, show b + m - (a + n) = b + m - a - n by ring,
      max_comm]

lemma cMax_chamber (a b m n : ℚ) :
    cMax (chamberSysA a b m n) (chamberSysB a b m n) (chamberM m n) (chamberN m n) =
      cMax a b m n := by
  unfold chamberSysA chamberSysB chamberM chamberN cMax
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    rw [show a + n + (b + m) + -m + -n = a + b by ring,
      show a + n + (b + m) = a + b + m + n by ring, min_comm]
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    rw [show b + a + n + m = a + b + m + n by ring, show b + a = a + b by ring]
  · simp only [c1, c2, c3, ↓reduceIte]
    rw [show b + m + (a + n) + -n + -m = a + b by ring,
      show b + m + (a + n) = a + b + m + n by ring, min_comm]

/-- The reduction of the chambers preserves the Racah system (same dimension `D`). -/
theorem racahSystem_chamber {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    RacahSystem (chamberSysA a b m n) (chamberSysB a b m n) (chamberM m n) (chamberN m n) D := by
  obtain ⟨⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩, hD⟩ := h
  have hn : 2 * n = ((r - 2 * s : ℤ) : ℚ) := by push_cast; linarith
  refine ⟨?_, ?_⟩
  · unfold chamberSysA chamberSysB chamberM chamberN
    by_cases c1 : |n| ≤ m
    · simp only [c1, ↓reduceIte]; exact ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩
    by_cases c2 : |n| ≤ -m
    · simp only [c1, c2, ↓reduceIte]
      refine ⟨⟨p + (r - 2 * s), ?_⟩, ⟨q + r, ?_⟩, ⟨-r, ?_⟩, ⟨-s, ?_⟩⟩ <;> push_cast at hn ⊢ <;> linarith
    by_cases c3 : |m| ≤ n
    · simp only [c1, c2, c3, ↓reduceIte]
      exact ⟨⟨q, hq⟩, ⟨p, hp⟩, ⟨r - 2 * s, hn⟩, ⟨-s, by push_cast; linarith⟩⟩
    · simp only [c1, c2, c3, ↓reduceIte]
      refine ⟨⟨q + r, ?_⟩, ⟨p + (r - 2 * s), ?_⟩, ⟨-(r - 2 * s), ?_⟩, ⟨-(-s), ?_⟩⟩ <;>
        push_cast at hn ⊢ <;> linarith
  · rw [cMin_chamber, cMax_chamber]; exact hD

lemma cc_mul' (a b : ℝ) : cc (a * b) = cc a * cc b := by
  simp [cc]

/-! ### The carrier polynomial in every chamber -/

/-- The even Racah deformation of the chamber of `(m,n)` and rank `d` above `f_0 = max(|m|,|n|)`:
`q_d = P̃_{M+d}/k_{6j}` of the canonical data `(M,N)`. -/
noncomputable def evenRacah6All (m n : ℚ) (d : ℕ) : CarrierRing :=
  evenRacah6 (chamberM m n) (chamberN m n) d

/-- **`eq:carrierRacah6j`, every chamber** (polynomial form): the signed carrier polynomial of the chamber
is `k_{6j} q_d`, with `k_{6j} = kLeadAll m n f = ε(n,m) κ_d(p,q)`, `d = ⌊f - f_0⌋₊`, `p = |m-n|`,
`q = |m+n|`. -/
theorem carrierPolyAll_eq_kLeadAll_mul_evenRacah6 (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p)
    (hq : |m + n| = q) :
    carrierPolyAll m n f = cc (kLeadAll m n f) * evenRacah6All m n ⌊f - chamberM m n⌋₊ := by
  obtain ⟨h1, h2⟩ := chamber_labels m n p q hp hq
  have hk := kLead_ne_zero _ _ p q h1 h2 (abs_chamberN_le m n) ⌊f - chamberM m n⌋₊
  unfold carrierPolyAll evenRacah6All evenRacah6 kLeadAll
  have hcc : cc (chamberSign m n) = cc (chamberSign m n * kLead (chamberM m n) (chamberN m n)
      ⌊f - chamberM m n⌋₊) * cc (kLead (chamberM m n) (chamberN m n) ⌊f - chamberM m n⌋₊)⁻¹ := by
    rw [← cc_mul', mul_assoc, mul_inv_cancel₀ hk, mul_one]
  rw [hcc, mul_assoc]

/-- **`lem:evendeformation6j`, every chamber** (the Racah analogue of `lem_evendeformation3`, which is already
stated for all four `3j` chambers).  With `p = |m-n|`, `q = |m+n|`, `(M,N)` the canonical data of the chamber
and `(A',B') = (chamberA, chamberB)` the reduced edges (`A↔B` swapped in chambers III, IV): `q_d =
evenRacah6All m n d` is monic of degree `d` in `ς` with coefficients in `ℝ[u,v,w]`, equals the monic Jacobi
polynomial `P̂_d^{(p,q)}` at zero scale, and on every `RacahSystem a b m n D` (`d ≤ D`) is a nonzero
`ς`-independent multiple of the Racah polynomial `R_d(λ(ς))` of `eq:physicalRacah4F3` with parameters
`(p, q, -D-1, c_min+c_max+1)`, `λ(ς) = 4A'B'ς + (A'-B')² - (c_min+½)²`.  Not covered: the analytic estimate
(`P2AnalyticEvenDegree6`). -/
theorem lem_evendeformation6_all (m n : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) (d : ℕ) :
    (evenRacah6All m n d).natDegree ≤ d ∧ (evenRacah6All m n d).coeff d = 1 ∧
      (evenRacah6All m n d).map (MvPolynomial.eval ![(0 : ℝ), 0, 0]) = jacobiMonicTau p q d ∧
      ∀ (a b : ℚ) (D : ℕ), RacahSystem a b m n D → d ≤ D →
        ∃ κ : ℝ, κ ≠ 0 ∧
          (evenRacah6All m n d).map (MvPolynomial.eval ![1 / chamberA a b m n ^ 2,
              1 / chamberB a b m n ^ 2, 1 / (chamberA a b m n * chamberB a b m n)]) =
            C κ * (racahLam (p : ℝ) (q : ℝ) (-(D : ℝ) - 1)
              ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) d).comp
              (C (4 * chamberA a b m n * chamberB a b m n) * X +
                C ((chamberA a b m n - chamberB a b m n) ^ 2 - ((cMin a b m n : ℝ) + 1 / 2) ^ 2)) := by
  obtain ⟨h1, h2⟩ := chamber_labels m n p q hp hq
  have key := lem_evendeformation6 (chamberM m n) (chamberN m n) p q h1 h2 (abs_chamberN_le m n) d
  refine ⟨key.1, key.2.1, key.2.2.1, fun a b D hR hdD => ?_⟩
  obtain ⟨κ, hκ, hκe⟩ := key.2.2.2 _ _ D (racahSystem_chamber hR) hdD
  refine ⟨κ, hκ, ?_⟩
  have e1 : ((chamberM m n : ℚ) : ℝ) - (chamberN m n : ℚ) = p := by exact_mod_cast h1
  have e2 : ((chamberM m n : ℚ) : ℝ) + (chamberN m n : ℚ) = q := by exact_mod_cast h2
  rw [wA_chamberSys, wB_chamberSys, cMin_chamber, cMax_chamber, e1, e2] at hκe
  exact hκe

/-- **`eq:sqrtfreecarrier6j` with `eq:carrierRacah6j`, every chamber.**  At every physical point
(`Phi6_carrier_all`'s hypotheses), with `p = |m-n|`, `q = |m+n|`, `M = max(|m|,|n|)`, `d = ⌊f - M⌋₊`,
`(A',B') = (chamberA, chamberB)`, `ς = (1 - cosA A' B' C)/2`:
`Φ_f = E W Π_f^{-1/2} · k_{6j} · q_d(ς; A'⁻², B'⁻², (A'B')⁻¹)`, `k_{6j} = ε(n,m) κ_d(p,q)` (`kLeadAll`),
`q_d` the even Racah deformation (`evenRacah6All`).  The sign `ε_{mn}` is inside `k_{6j}`. -/
theorem Phi6_eq_kLeadAll_mul_evenRacah6 (a b c f m n : ℚ) (p q : ℕ) (hp : |m - n| = p)
    (hq : |m + n| = q) (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) (h3 : IsTri c a b)
    (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n =
      edgeFac (chamberM m n) (chamberN m n) (chamberA a b m n) (chamberB a b m n) (wC c) *
        (Real.sqrt (piSix f (chamberA a b m n) (chamberB a b m n)))⁻¹ *
        (kLeadAll m n f *
          evalC ((1 - cosA (chamberA a b m n) (chamberB a b m n) (wC c)) / 2)
            (1 / chamberA a b m n ^ 2) (1 / chamberB a b m n ^ 2)
            (1 / (chamberA a b m n * chamberB a b m n))
            (evenRacah6All m n ⌊f - chamberM m n⌋₊)) := by
  rw [Phi6_eq_poly_all a b c f m n h1 h2 h3 h4]
  unfold carrierPolyEval
  rw [carrierPolyAll_eq_kLeadAll_mul_evenRacah6 m n f p q hp hq, map_mul, evalC_cc]

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.racahSystem_chamber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.racahSystem_chamber

/-- info: 'FormalResearch.Racah.carrierPolyAll_eq_kLeadAll_mul_evenRacah6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.carrierPolyAll_eq_kLeadAll_mul_evenRacah6

/-- info: 'FormalResearch.Racah.lem_evendeformation6_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.lem_evendeformation6_all

/-- info: 'FormalResearch.Racah.Phi6_eq_kLeadAll_mul_evenRacah6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Phi6_eq_kLeadAll_mul_evenRacah6


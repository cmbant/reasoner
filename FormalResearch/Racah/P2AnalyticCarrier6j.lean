module

public import FormalResearch.Racah.P2RacahSeed
public import FormalResearch.Racah.P2AnalyticCt

/-!
# The square-root-free carrier of the one-small `6j` family (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier` (`eq:sqrtfreecarrier`,
`eq:6jrankpoly`) together with `lem:6jseed`, `eq:6jexceptionalseed` and `eq:6jEdgeProducts`.

## Dictionary (paper symbol -> Lean symbol)

| paper | Lean |
|---|---|
| `Π_f(A,B) = ∏_{q∈Q_f} (1-q²/4A²)(1-q²/4B²)` | `piSix f A B` |
| `E_{A,B}(C) W_{6j}(x)` (squared, `eq:6jEdgeProducts`) | `edgeFac m n A B C` (`edgeSq` is the radicand) |
| `P̃_f(τ; A⁻², B⁻², (AB)⁻¹)` (`eq:6jrankpoly`) | `ptilde6 m n τ u v w d`, `d = f - m` |
| the same, as an honest polynomial | `ptPoly m n d : Polynomial (MvPolynomial (Fin 3) ℝ)` |

Everything is square-root free in the sense of the paper: `E W` never appears as a power with a
fractional exponent.  Using `(A-B+C)(-A+B+C) = 4AB (1-x)/2` and `(A+B-C)(A+B+C) = 4AB (1+x)/2`
(`eq:6jEdgeProducts`) one finds `E_{A,B}(C) W_{6j}(x) = √(∏ 𝔠 / (4AB)^{2m})` with the four central
products of `eq:6jseed`; this is `edgeFac`.  `edgeSq_eq_EW_sq` (in `P2AnalyticCarrier6jShape.lean`) proves the squared identity with
the paper's `ℛ_p(X)² = 𝔠_p(X)/X^p`.

## Results

* `ptPoly`, `ptilde6`: the carrier, defined by the square-root-free recursion in `f`
  (`eq:6jrankpoly`) with the seed start `P̃_m = √C(2m, m+n)` and, for `m = 0`, the exceptional start
  `P̃_0 = 1`, `P̃_1 = 1 - 2τ - (8AB)⁻¹` (`eq:6jexceptionalseed`).
* `ptilde6_zero`, `ptilde6_one_of_ne`, `ptilde6_one_of_eq`, `ptilde6_succ_succ`: the recursion for
  the real-valued evaluation.
* `piSix_succ`, `piSix_pos`, `piSix_nonneg`, `sqrt_piSix_succ`: `Π_{f+1} = Π_f η_{f+1}²` and positivity
  at physical ranks (`f + 1 ≤ 2A`, `adm_bounds`).
* `Phi6_seed_carrier`: the seed `Φ_m = E W Π_m^{-1/2} √C(2m,m+n)` (from `Phi6_seed`, `lem:6jseed`).

The induction (`Phi6_carrier_canonical`) is in `P2AnalyticCarrier6jInduction.lean`, the chamber
reduction in `P2AnalyticCarrier6jChambers.lean`, the shape variables, `G6`, `dZero6` and
`edgeSq_eq_EW_sq` in `P2AnalyticCarrier6jShape.lean`, the degree / coefficient / symmetry statements
in `P2AnalyticCarrier6jPoly.lean`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

/-! ### The normalisation `Π_f` and the edge factor -/

/-- `Π_f(A,B) = ∏_{q ∈ Q_f} (1 - q²/4A²)(1 - q²/4B²)`, `Q_f = {f, f-1, …}` the set of positive
numbers `f - k` (`k ∈ ℕ`): `{1,…,f}` for integer and `{1/2,…,f}` for half-integer `f`
(empty for `f = 0`). -/
noncomputable def piSix (f : ℚ) (A B : ℝ) : ℝ :=
  ∏ k ∈ Finset.range ⌈f⌉₊,
    ((1 - ((f : ℝ) - k) ^ 2 / (4 * A ^ 2)) * (1 - ((f : ℝ) - k) ^ 2 / (4 * B ^ 2)))

/-- The radicand of the edge factor: `∏ 𝔠 / (4AB)^{2m}` with the four central products of
`eq:6jseed`, `m ± n ∈ ℕ`. -/
noncomputable def edgeSq (m n : ℚ) (A B C : ℝ) : ℝ :=
  cenProd ⌊m - n⌋₊ (A - B + C) * cenProd ⌊m - n⌋₊ (-A + B + C) *
    cenProd ⌊m + n⌋₊ (A + B - C) * cenProd ⌊m + n⌋₊ (A + B + C) / (4 * A * B) ^ ⌊2 * m⌋₊

/-- The edge factor `E_{A,B}(C) W_{6j}(x) = √(edgeSq)` (`eq:6jEdgeFactors`, `eq:6jEdgeProducts`);
`m ± n ∈ ℕ` are the two edge exponents `p_max`, `p_min`. -/
noncomputable def edgeFac (m n : ℚ) (A B C : ℝ) : ℝ := Real.sqrt (edgeSq m n A B C)

/-! ### The carrier polynomials -/

/-- The carrier lives in `ℝ[u, v, w][τ]` with `u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`. -/
abbrev CarrierRing : Type := Polynomial (MvPolynomial (Fin 3) ℝ)

/-- A real constant as an element of `CarrierRing`. -/
noncomputable def cc (r : ℝ) : CarrierRing := Polynomial.C (MvPolynomial.C r)

/-- The variable `u = A⁻²`. -/
noncomputable def uVar : CarrierRing := Polynomial.C (MvPolynomial.X 0)

/-- The variable `v = B⁻²`. -/
noncomputable def vVar : CarrierRing := Polynomial.C (MvPolynomial.X 1)

/-- The variable `w = (AB)⁻¹`. -/
noncomputable def wVar : CarrierRing := Polynomial.C (MvPolynomial.X 2)

/-- The diagonal coefficient `(2f+1){f(f+1)[1-2τ-q_f] - mn}` of `eq:6jrankpoly`,
`q_f = (2f(f+1)+1-m²-n²) w/8`. -/
noncomputable def diagP (m n : ℚ) (f : ℝ) : CarrierRing :=
  cc ((2 * f + 1) * f * (f + 1)) *
      (1 - cc 2 * Polynomial.X - cc ((2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8) * wVar) -
    cc ((2 * f + 1) * m * n)

/-- `η_f² = (1 - f²u/4)(1 - f²v/4)`. -/
noncomputable def eta2P (f : ℝ) : CarrierRing :=
  (1 - cc (f ^ 2 / 4) * uVar) * (1 - cc (f ^ 2 / 4) * vVar)

/-- The start value `P̃_m = √C(2m, m+n)` (the seed; `P̃_0 = 1` for `m = n = 0`). -/
noncomputable def pt0 (m n : ℚ) : CarrierRing :=
  cc (Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ))

open Classical in
/-- The second value `P̃_{m+1}`: for `m ≠ 0` it is the recursion `eq:6jrankpoly` at `f = m`
(where the backward coefficient `R_m` vanishes); for `m = 0` it is the exceptional start
`1 - 2τ - (8AB)⁻¹` of `eq:6jexceptionalseed`. -/
noncomputable def pt1 (m n : ℚ) : CarrierRing :=
  if m = 0 then 1 - cc 2 * Polynomial.X - cc (1 / 8) * wVar
  else cc (1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1))) * diagP m n (m : ℝ) * pt0 m n

/-- **The carrier** `P̃_f`, `f = m + d` (`eq:6jrankpoly`), as a polynomial in `τ` with coefficients in
`ℝ[u,v,w]`: the square-root-free recursion
`f R_{f+1} P̃_{f+1} = (2f+1){λ_f[1-2τ-q_f] - mn} P̃_f - (f+1) R_f η_f² P̃_{f-1}`. -/
noncomputable def ptPoly (m n : ℚ) : ℕ → CarrierRing
  | 0 => pt0 m n
  | 1 => pt1 m n
  | d + 2 =>
      cc (1 / (((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1))) *
        (diagP m n ((m : ℝ) + d + 1) * ptPoly m n (d + 1) -
          cc ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1)) *
            eta2P ((m : ℝ) + d + 1) * ptPoly m n d)

/-- Evaluation of `ℝ[u,v,w][τ]` at `(τ,u,v,w)`. -/
noncomputable def evalC (τ u v w : ℝ) : CarrierRing →+* ℝ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval ![u, v, w]) τ

/-- The real-valued carrier `P̃_f(τ; u, v, w)` with `u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`. -/
noncomputable def ptilde6 (m n : ℚ) (τ u v w : ℝ) (d : ℕ) : ℝ :=
  evalC τ u v w (ptPoly m n d)

section eval

variable (τ u v w : ℝ)

@[simp] lemma evalC_cc (r : ℝ) : evalC τ u v w (cc r) = r := by
  simp [evalC, cc]

@[simp] lemma evalC_X : evalC τ u v w Polynomial.X = τ := by
  simp [evalC]

@[simp] lemma evalC_uVar : evalC τ u v w uVar = u := by
  simp [evalC, uVar]

@[simp] lemma evalC_vVar : evalC τ u v w vVar = v := by
  simp [evalC, vVar]

@[simp] lemma evalC_wVar : evalC τ u v w wVar = w := by
  simp [evalC, wVar]

lemma evalC_diagP (m n : ℚ) (f : ℝ) :
    evalC τ u v w (diagP m n f) =
      (2 * f + 1) * (f * (f + 1) * (1 - 2 * τ - (2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8 * w)
        - m * n) := by
  simp only [diagP, map_sub, map_mul, map_one, evalC_cc, evalC_X, evalC_wVar]
  ring

lemma evalC_eta2P (f : ℝ) :
    evalC τ u v w (eta2P f) = (1 - f ^ 2 / 4 * u) * (1 - f ^ 2 / 4 * v) := by
  simp only [eta2P, map_sub, map_mul, map_one, evalC_cc, evalC_uVar, evalC_vVar]

end eval

lemma ptilde6_zero (m n : ℚ) (τ u v w : ℝ) :
    ptilde6 m n τ u v w 0 = Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := by
  simp [ptilde6, ptPoly, pt0]

lemma ptilde6_one_of_eq (n : ℚ) (τ u v w : ℝ) :
    ptilde6 0 n τ u v w 1 = 1 - 2 * τ - w / 8 := by
  simp only [ptilde6, ptPoly, pt1, ↓reduceIte, map_sub, map_mul, map_one, evalC_cc, evalC_X,
    evalC_wVar]
  ring

lemma ptilde6_one_of_ne (m n : ℚ) (hm : m ≠ 0) (τ u v w : ℝ) :
    ptilde6 m n τ u v w 1 =
      1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1)) *
        ((2 * (m : ℝ) + 1) * (m * (m + 1) *
            (1 - 2 * τ - (2 * (m : ℝ) * (m + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8 * w) - m * n)) *
        Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := by
  simp only [ptilde6, ptPoly, pt1, hm, ↓reduceIte, map_mul, evalC_cc, evalC_diagP, pt0]

lemma ptilde6_succ_succ (m n : ℚ) (τ u v w : ℝ) (d : ℕ) :
    ptilde6 m n τ u v w (d + 2) =
      1 / (((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1)) *
        ((2 * ((m : ℝ) + d + 1) + 1) * (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) *
            (1 - 2 * τ - (2 * ((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2)
              / 8 * w) - m * n) * ptilde6 m n τ u v w (d + 1) -
          ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1)) *
            ((1 - ((m : ℝ) + d + 1) ^ 2 / 4 * u) * (1 - ((m : ℝ) + d + 1) ^ 2 / 4 * v)) *
            ptilde6 m n τ u v w d) := by
  simp only [ptilde6, ptPoly, map_mul, map_sub, evalC_cc, evalC_diagP, evalC_eta2P]


/-! ### Elementary lemmas: admissibility and `Π_f` -/

lemma isNat_nonneg' {x : ℚ} (h : IsNat x) : 0 ≤ x := by
  obtain ⟨k, rfl⟩ := h
  positivity

lemma isNat_of_add_one {x : ℚ} (h : IsNat (x + 1)) (hx : 0 ≤ x) : IsNat x := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => simp at hk; linarith
  | succ k => exact ⟨k, by push_cast at hk; linarith⟩

lemma isNat_add_one' {x : ℚ} (h : IsNat x) : IsNat (x + 1) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by push_cast; ring⟩

/-- A triad `(f+1, y, z)` gives the triad `(f, y, z)` as soon as the two differences that can fail
(`f + y - z` and `f - y + z`) are nonnegative. -/
lemma isTri_of_succ {f y z : ℚ} (h : IsTri (f + 1) y z) (h1 : 0 ≤ f + y - z) (h2 : 0 ≤ f - y + z) :
    IsTri f y z := by
  refine ⟨isNat_of_add_one ?_ h1, isNat_of_add_one ?_ h2, ?_⟩
  · have e : f + y - z + 1 = f + 1 + y - z := by ring
    rw [e]; exact h.1
  · have e : f - y + z + 1 = f + 1 - y + z := by ring
    rw [e]; exact h.2.1
  · have e : -f + y + z = (-(f + 1) + y + z) + 1 := by ring
    rw [e]; exact isNat_add_one' h.2.2

/-- Size bounds at a physical rank: `f + 1 ≤ 2A` and `f + 1 ≤ 2B`. -/
lemma adm_bounds {a b f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    (f : ℝ) + 1 ≤ 2 * wA a n ∧ (f : ℝ) + 1 ≤ 2 * wB b m := by
  have e1 := isNat_nonneg' h1.2.2
  have e2 := isNat_nonneg' h2.2.2
  have e1' : (0 : ℝ) ≤ -(f : ℝ) + ((b : ℝ) + m) + b := by exact_mod_cast e1
  have e2' : (0 : ℝ) ≤ -(f : ℝ) + (a : ℝ) + (a + n) := by exact_mod_cast e2
  unfold wA wB
  constructor <;> linarith

lemma piSix_zero (A B : ℝ) : piSix 0 A B = 1 := by
  simp [piSix]

/-- The factors of `Π_f`: `q = f - k` with `0 < q ≤ f`. -/
lemma piSix_nonneg (f : ℚ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hfA : (f : ℝ) ≤ 2 * A) (hfB : (f : ℝ) ≤ 2 * B) : 0 ≤ piSix f A B := by
  unfold piSix
  refine Finset.prod_nonneg fun k hk => ?_
  have hk' : k < ⌈f⌉₊ := Finset.mem_range.mp hk
  have hkf : (k : ℚ) < f := Nat.lt_ceil.mp hk'
  have hkf' : (k : ℝ) < f := by exact_mod_cast hkf
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : 0 < (f : ℝ) - k := by linarith
  have hqA : ((f : ℝ) - k) ^ 2 / (4 * A ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hqB : ((f : ℝ) - k) ^ 2 / (4 * B ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  exact mul_nonneg (by linarith) (by linarith)

lemma piSix_succ (g : ℚ) (hg : 0 ≤ g) (A B : ℝ) :
    piSix (g + 1) A B =
      piSix g A B * ((1 - ((g : ℝ) + 1) ^ 2 / (4 * A ^ 2)) * (1 - ((g : ℝ) + 1) ^ 2 / (4 * B ^ 2))) := by
  unfold piSix
  rw [Nat.ceil_add_one hg, Finset.prod_range_succ']
  push_cast
  have : ∀ k ∈ Finset.range ⌈g⌉₊, (1 - ((g : ℝ) + 1 - ((k : ℝ) + 1)) ^ 2 / (4 * A ^ 2)) *
      (1 - ((g : ℝ) + 1 - ((k : ℝ) + 1)) ^ 2 / (4 * B ^ 2)) =
      (1 - ((g : ℝ) - k) ^ 2 / (4 * A ^ 2)) * (1 - ((g : ℝ) - k) ^ 2 / (4 * B ^ 2)) := by
    intro k _; ring_nf
  rw [Finset.prod_congr rfl this]
  ring

/-- `√Π_{g+1} = √Π_g · η_{g+1}`. -/
lemma sqrt_piSix_succ (g : ℚ) (hg : 0 ≤ g) (A B : ℝ) (hpi : 0 ≤ piSix g A B) :
    Real.sqrt (piSix (g + 1) A B) = Real.sqrt (piSix g A B) * etaK A B ((g : ℝ) + 1) := by
  rw [piSix_succ g hg, Real.sqrt_mul hpi]
  rfl


/-! ### The seed in carrier form -/

lemma chiM_pow (m : ℚ) (hm : IsNat (2 * m)) (A B : ℝ) :
    chiM m A B * (4 * A * B) ^ ⌊2 * m⌋₊ = (4 * A * B) ^ (2 * ⌈m⌉₊) := by
  obtain ⟨μ, hμ⟩ := hm
  rw [hμ, Nat.floor_natCast]
  rcases Nat.even_or_odd' μ with ⟨M, hM | hM⟩
  · have hmM : m = M := by
      have : ((2 * M : ℕ) : ℚ) = 2 * m := by rw [← hM]; exact hμ.symm
      push_cast at this; linarith
    have hnat : IsNat m := ⟨M, hmM⟩
    have hchi : chiM m A B = 1 := by simp [chiM, hnat]
    rw [hchi, hmM, Nat.ceil_natCast, hM]
    ring
  · have hmM : m = M + 1 / 2 := by
      have : ((2 * M + 1 : ℕ) : ℚ) = 2 * m := by rw [← hM]; exact hμ.symm
      push_cast at this; linarith
    have hnat : ¬ IsNat m := by
      rintro ⟨n, hn⟩
      have : (2 * n : ℚ) = 2 * M + 1 := by rw [← hn, hmM]; ring
      have : 2 * n = 2 * M + 1 := by exact_mod_cast this
      omega
    have hc : ⌈m⌉₊ = M + 1 := by
      rw [Nat.ceil_eq_iff (by omega), hmM]
      constructor <;> push_cast <;> linarith
    have hchi : chiM m A B = 4 * A * B := by simp [chiM, hnat]
    rw [hchi, hc, hM]
    ring

lemma chiM_ne_zero (m : ℚ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : chiM m A B ≠ 0 := by
  unfold chiM
  split_ifs
  · exact one_ne_zero
  · positivity

lemma dProd_mul_dProd (m : ℚ) (A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    dProd m A * dProd m B = (4 * A * B) ^ (2 * ⌈m⌉₊) * piSix m A B := by
  have h : ∀ X : ℝ, X ≠ 0 → dProd m X = (4 * X ^ 2) ^ ⌈m⌉₊ *
      ∏ k ∈ Finset.range ⌈m⌉₊, (1 - ((m : ℝ) - k) ^ 2 / (4 * X ^ 2)) := by
    intro X hX
    unfold dProd
    have e : (4 * X ^ 2) ^ ⌈m⌉₊ = ∏ _k ∈ Finset.range ⌈m⌉₊, (4 * X ^ 2) := by simp
    rw [e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [h A hA, h B hB]
  unfold piSix
  rw [Finset.prod_mul_distrib]
  have : (4 * A * B) ^ (2 * ⌈m⌉₊) = (4 * A ^ 2) ^ ⌈m⌉₊ * (4 * B ^ 2) ^ ⌈m⌉₊ := by
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  rw [this]
  ring

lemma piSix_pos (f : ℚ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hfA : (f : ℝ) < 2 * A) (hfB : (f : ℝ) < 2 * B) : 0 < piSix f A B := by
  unfold piSix
  refine Finset.prod_pos fun k hk => ?_
  have hk' : k < ⌈f⌉₊ := Finset.mem_range.mp hk
  have hkf : (k : ℚ) < f := Nat.lt_ceil.mp hk'
  have hkf' : (k : ℝ) < f := by exact_mod_cast hkf
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : 0 < (f : ℝ) - k := by linarith
  have hqA : ((f : ℝ) - k) ^ 2 / (4 * A ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hqB : ((f : ℝ) - k) ^ 2 / (4 * B ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  exact mul_pos (by linarith) (by linarith)

/-- The seed `Φ_m` in carrier form: `Φ_m = E W Π_m^{-1/2} √C(2m, m+n)`
(`lem:6jseed` + `eq:6jEdgeProducts`, as used in the proof of `lem:sqrtfreecarrier`). -/
theorem Phi6_seed_carrier (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c m m n =
      edgeFac m n (wA a n) (wB b m) (wC c) * (Real.sqrt (piSix m (wA a n) (wB b m)))⁻¹ *
        Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := by
  obtain ⟨hA, hB, -, -, -⟩ := admissible_facts h1 h2
  obtain ⟨hAb, hBb⟩ := adm_bounds h1 h2
  have hpi : 0 < piSix m (wA a n) (wB b m) := piSix_pos m _ _ hA hB (by linarith) (by linarith)
  have h2m : IsNat (2 * m) := by
    have e : 2 * m = m + (b + m) - b := by ring
    rw [e]; exact h1.1
  have hchoose : (0 : ℝ) ≤ ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Phi6_seed a b c m n h1 h2 h3 h4]
  have key : seedS m n (wA a n) (wB b m) (wC c) =
      edgeSq m n (wA a n) (wB b m) (wC c) *
        (((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) / piSix m (wA a n) (wB b m)) := by
    unfold seedS edgeSq
    rw [dProd_mul_dProd m _ _ hA.ne' hB.ne', ← chiM_pow m h2m]
    have h1' := chiM_ne_zero m _ _ hA hB
    have h2' : ((4 * wA a n * wB b m) ^ ⌊2 * m⌋₊) ≠ 0 := by positivity
    have h3' := hpi.ne'
    field_simp
  rw [key, Real.sqrt_mul' _ (div_nonneg hchoose hpi.le), Real.sqrt_div' _ hpi.le]
  unfold edgeFac
  ring

end FormalResearch.Racah

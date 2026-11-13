module

public import FormalResearch.Racah.P2AnalyticLeading
public import FormalResearch.Racah.P2AnalyticCarrier6jChambers

/-!
# The `6j` leading constant `k_{6j}` in every chamber (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:WignerJacobiMonic`, `eq:kconstants`,
`lem:sqrtfreecarrier` ("their leading coefficients are `k_{3j}`, respectively `ε_{mn} k_{6j}`").

`P2AnalyticLeading.lean` identifies the leading coefficient `kLead m n d` of the carrier `P̃_{m+d}` in the
canonical sector `|n| ≤ m` only.  `P2AnalyticCarrier6jChambers.lean` reduces the four chambers to it
(`carrierAll`, `Phi6_carrier_all`).  Here the leading-coefficient statement is proved in every chamber.

## The chamber-reduced data

For `(m,n)` in chamber I `|n| ≤ m`, II `|n| ≤ -m`, III `|m| ≤ n`, IV `|m| ≤ -n`, the canonical data
`(M,N)` is `(m,n)`, `(-m,-n)`, `(n,m)`, `(-n,-m)` (`chamberM`, `chamberN`) and the sign is
`chamberSign = 1, (-1)^{m-n}, (-1)^{m-n}, 1`.  Then, for every chamber (all proved below):

* `chamberM m n = max |m| |n| = L₀` and the degree is `d = f - L₀` (`chamberM_eq_max`);
* `(M - N, M + N) = (|m-n|, |m+n|)`, so the Jacobi parameters are `(p,q) = (|m-n|,|m+n|)` in every chamber
  (`chamber_labels`);
* `chamberSign m n = ε(n,m)`, the phase `signE3 n m` of `eq:HahnAllChamberPhase` for `(M,σ) = (n,m)`
  (`chamberSign_eq_signE3`);
* the signed carrier polynomial `carrierPolyAll m n f = chamberSign · P̃_{M+d}` (a polynomial in `τ` over
  `ℝ[u,v,w]`) has exact degree `d` and leading coefficient the constant `kLeadAll m n f = ε(n,m) κ_d(p,q)`,
  `κ_d(p,q) = (-1)^d √(d!(d+p+q)!/((d+p)!(d+q)!)) (d+p+q+1)_d / d!` (`carrierPolyAll_natDegree`,
  `carrierPolyAll_coeff_top`, `kLeadAll_eq_sign_mul_kappa`), which is nonzero (`kLeadAll_ne_zero`);
* the carrier is `E · Π^{-1/2} ·` (that polynomial) at every physical point (`carrierAll_eq_poly`,
  `Phi6_eq_poly_all`);
* at zero scale it is `kLeadAll · P̂_d^{(p,q)}` (`carrierPolyZero_eq_kLeadAll_mul_monic`).

## Paper versus Lean

The paper writes `Φ_f = ε_{mn} E W Π^{-1/2} P̃_f` and says `P̃_f` has leading coefficient `ε_{mn} k_{6j}` with
`k_{6j} = ε(n,m) κ` (`eq:kconstants`).  Since `ε_{mn} = ε(n,m)` (`chamberSign_eq_signE3`) and `ε² = 1`, this says
that `P̃_f` has leading coefficient `κ_d(p,q)` (no sign) and the signed polynomial `ε P̃_f` has leading
coefficient `k_{6j} = ε κ`; this is what is proved here (`kLeadAll`).  The paper's phrase "`N`-independent
nonzero constants" is made exact: the constant is `ε(n,m) κ_d(|m-n|,|m+n|)`, independent of `u,v,w`, nonzero.
`ε_{mn}` is stated in the paper only in the lemma's text (`(-1)^{m-n}` in `|n| ≤ -m`, `|m| ≤ n`; `1` otherwise), and
`ε_{mn} = ε(n,m)` is not remarked there.  Not covered: the all-chamber Wigner form
`d^f_{nm}(arccos x) = k_{6j} W P̂` (`wignerD6_eq_kLead_mul_monic` is canonical only).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Special FormalResearch.Racah.SixJ Polynomial

/-! ### Chamber data -/

/-- The canonical `m` of the chamber of `(m,n)`: `m, -m, n, -n` in chambers I-IV. -/
noncomputable def chamberM (m n : ℚ) : ℚ :=
  if |n| ≤ m then m else if |n| ≤ -m then -m else if |m| ≤ n then n else -n

/-- The canonical `n` of the chamber of `(m,n)`: `n, -n, m, -m` in chambers I-IV. -/
noncomputable def chamberN (m n : ℚ) : ℚ :=
  if |n| ≤ m then n else if |n| ≤ -m then -n else if |m| ≤ n then m else -m

/-- The chamber sign `1, (-1)^{m-n}, (-1)^{m-n}, 1` of `carrierAll`. -/
noncomputable def chamberSign (m n : ℚ) : ℝ :=
  if |n| ≤ m then 1 else if |n| ≤ -m then (-1 : ℝ) ^ ⌊m - n⌋
  else if |m| ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ else 1

/-- The first (resp. second) centered edge of the reduced carrier: `(A,B)` in chambers I, II and `(B,A)` in
chambers III, IV. -/
noncomputable def chamberA (a b m n : ℚ) : ℝ :=
  if |n| ≤ m then wA a n else if |n| ≤ -m then wA a n else if |m| ≤ n then wB b m else wB b m

noncomputable def chamberB (a b m n : ℚ) : ℝ :=
  if |n| ≤ m then wB b m else if |n| ≤ -m then wB b m else if |m| ≤ n then wA a n else wA a n

lemma chamber_four {m n : ℚ} (c1 : ¬ |n| ≤ m) (c2 : ¬ |n| ≤ -m) (c3 : ¬ |m| ≤ n) :
    |m| ≤ -n := by
  rcases le_total 0 n with hn | hn
  · rw [abs_of_nonneg hn] at c1 c2
    exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
  · rw [abs_of_nonpos hn] at c1 c2
    rw [abs_le]; push Not at c1 c2; constructor <;> linarith

lemma abs_chamberN_le (m n : ℚ) : |chamberN m n| ≤ chamberM m n := by
  unfold chamberN chamberM
  by_cases c1 : |n| ≤ m
  · simp [c1]
  by_cases c2 : |n| ≤ -m
  · simp [c1, c2]
  by_cases c3 : |m| ≤ n
  · simp [c1, c2, c3]
  simpa [c1, c2, c3, abs_neg] using chamber_four c1 c2 c3

/-- In every chamber `M = max |m| |n| = L₀`. -/
theorem chamberM_eq_max (m n : ℚ) : chamberM m n = max |m| |n| := by
  unfold chamberM
  by_cases c1 : |n| ≤ m
  · have : |m| = m := abs_of_nonneg (le_trans (abs_nonneg n) c1)
    simp [c1, this]
  by_cases c2 : |n| ≤ -m
  · have : |m| = -m := abs_of_nonpos (by linarith [abs_nonneg n])
    simp [c1, c2, this]
  by_cases c3 : |m| ≤ n
  · have : |n| = n := abs_of_nonneg (le_trans (abs_nonneg m) c3)
    simp only [c1, c2, c3, ↓reduceIte]; rw [this, max_eq_right c3]
  · have c4 := chamber_four c1 c2 c3
    have : |n| = -n := abs_of_nonpos (by linarith [abs_nonneg m])
    simp only [c1, c2, c3, ↓reduceIte]; rw [this, max_eq_right c4]

/-- In every chamber the reduced labels satisfy `M - N = |m-n|`, `M + N = |m+n|`, so the Jacobi parameters
`(p,q)` are `(|m-n|, |m+n|)` (as naturals), and `|N| ≤ M`. -/
theorem chamber_labels (m n : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) :
    chamberM m n - chamberN m n = p ∧ chamberM m n + chamberN m n = q := by
  unfold chamberM chamberN
  by_cases c1 : |n| ≤ m
  · obtain ⟨h1, h2⟩ := abs_le.mp c1
    rw [abs_of_nonneg (by linarith)] at hp hq
    simp only [c1, ↓reduceIte]; constructor <;> linarith
  by_cases c2 : |n| ≤ -m
  · obtain ⟨h1, h2⟩ := abs_le.mp c2
    rw [abs_of_nonpos (by linarith)] at hp hq
    simp only [c1, c2, ↓reduceIte]; constructor <;> linarith
  by_cases c3 : |m| ≤ n
  · obtain ⟨h1, h2⟩ := abs_le.mp c3
    rw [abs_of_nonpos (by linarith)] at hp
    rw [abs_of_nonneg (by linarith)] at hq
    simp only [c1, c2, c3, ↓reduceIte]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := abs_le.mp (chamber_four c1 c2 c3)
    rw [abs_of_nonneg (by linarith)] at hp
    rw [abs_of_nonpos (by linarith)] at hq
    simp only [c1, c2, c3, ↓reduceIte]; constructor <;> linarith

lemma neg_one_zpow_mul_self (k : ℤ) : ((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k = 1 := by
  rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num

lemma chamberSign_mul_self (m n : ℚ) : chamberSign m n * chamberSign m n = 1 := by
  unfold chamberSign
  split_ifs
  · norm_num
  · exact neg_one_zpow_mul_self _
  · exact neg_one_zpow_mul_self _
  · norm_num

lemma chamberSign_ne_zero (m n : ℚ) : chamberSign m n ≠ 0 := by
  intro h
  have := chamberSign_mul_self m n
  rw [h] at this; norm_num at this

/-- `chamberSign m n = (-1)^{m-n}` if `m ≤ n` and `1` otherwise (it is the phase `ε(n,m)` of
`eq:HahnAllChamberPhase`, see `chamberSign_eq_signE3`). -/
lemma chamberSign_eq (m n : ℚ) :
    chamberSign m n = if m ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ else 1 := by
  unfold chamberSign
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    split_ifs with h
    · have : m = n := le_antisymm h (le_trans (le_abs_self n) c1)
      subst this; simp
    · rfl
  by_cases c2 : |n| ≤ -m
  · have h : m ≤ n := by linarith [neg_le_abs n]
    simp only [c1, c2, ↓reduceIte, h]
  by_cases c3 : |m| ≤ n
  · have h : m ≤ n := le_trans (le_abs_self m) c3
    simp only [c1, c2, c3, ↓reduceIte, h]
  · have c4 := chamber_four c1 c2 c3
    simp only [c1, c2, c3, ↓reduceIte]
    split_ifs with h
    · have : m = n := le_antisymm h (by linarith [neg_le_abs m])
      subst this; simp
    · rfl

/-- **`ε_{mn} = ε(n,m)`**: the chamber sign is the phase `ε(M,σ)` of `eq:HahnAllChamberPhase`
(`signE3`) at `(M,σ) = (n,m)`, `α = |m-n|`. -/
theorem chamberSign_eq_signE3 (m n : ℚ) (α : ℕ) (hα : |m - n| = α) :
    chamberSign m n = signE3 n m α := by
  rw [chamberSign_eq]
  unfold signE3
  by_cases h : m ≤ n
  · simp only [h, ↓reduceIte]
    rw [abs_of_nonpos (by linarith)] at hα
    have hf : ⌊m - n⌋ = -(α : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hf, zpow_neg, zpow_natCast, ← inv_pow]; norm_num
  · simp [h]

/-! ### The leading constant -/

/-- The paper's `κ_d(p,q) = (-1)^d √(d!(d+p+q)!/((d+p)!(d+q)!)) (d+p+q+1)_d / d!` (`eq:kconstants`). -/
noncomputable def kappaJac (p q d : ℕ) : ℝ :=
  wignerJacobiNorm p q d * (-1) ^ d * (ascPochhammer ℝ d).eval ((d : ℝ) + p + q + 1) /
    (d.factorial : ℝ)

lemma kappaJac_eq_jacobi (p q d : ℕ) :
    kappaJac p q d = wignerJacobiNorm p q d * ((jacobi (p : ℝ) (q : ℝ) d).coeff d * (-2) ^ d) := by
  unfold kappaJac
  rw [jacobi_coeff_self]
  have h2 : ((-2 : ℝ)) ^ d = (-1) ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
  have hk : (d.factorial : ℝ) ≠ 0 := by positivity
  rw [h2]
  field_simp

lemma wignerJacobiNorm_pos (p q d : ℕ) : 0 < wignerJacobiNorm p q d := by
  unfold wignerJacobiNorm
  exact Real.sqrt_pos.mpr (by positivity)

/-- `κ_d(p,q) ≠ 0`. -/
theorem kappaJac_ne_zero (p q d : ℕ) : kappaJac p q d ≠ 0 := by
  rw [kappaJac_eq_jacobi]
  exact mul_ne_zero (wignerJacobiNorm_pos p q d).ne' (jacobi_lead_ne_zero p q d)

/-- The signed carrier polynomial of the chamber of `(m,n)`, rank `f`: `ε · P̃_{M+d}(·; N)`,
`d = ⌊f - M⌋₊`, in `ℝ[u,v,w][τ]`. -/
noncomputable def carrierPolyAll (m n f : ℚ) : CarrierRing :=
  cc (chamberSign m n) * ptPoly (chamberM m n) (chamberN m n) ⌊f - chamberM m n⌋₊

/-- The leading constant `k_{6j}` of the signed carrier polynomial, in every chamber:
`ε · kLead M N d` (`ε = chamberSign`, `(M,N)` the reduced data, `d = ⌊f - M⌋₊`). -/
noncomputable def kLeadAll (m n f : ℚ) : ℝ :=
  chamberSign m n * kLead (chamberM m n) (chamberN m n) ⌊f - chamberM m n⌋₊

/-- The coefficient of `τ^d` in the signed carrier polynomial is the constant `kLeadAll m n f`
(independent of `u, v, w`), in every chamber and with no hypothesis on the labels. -/
theorem carrierPolyAll_coeff_top (m n f : ℚ) :
    (carrierPolyAll m n f).coeff ⌊f - chamberM m n⌋₊ = MvPolynomial.C (kLeadAll m n f) := by
  unfold carrierPolyAll kLeadAll
  rw [coeff_cc_mul, ptPoly_coeff_top _ _ (abs_chamberN_le m n), ← MvPolynomial.C_mul]

theorem carrierPolyAll_natDegree_le (m n f : ℚ) :
    (carrierPolyAll m n f).natDegree ≤ ⌊f - chamberM m n⌋₊ := by
  unfold carrierPolyAll
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_cc, zero_add]
  exact ptPoly_natDegree_le _ _ _

/-- **Closed form of `k_{6j}` in every chamber** (`eq:kconstants`): with `p = |m-n|`, `q = |m+n|`,
`d = ⌊f - max(|m|,|n|)⌋₊`, `kLeadAll m n f = ε(n,m) κ_d(p,q)`. -/
theorem kLeadAll_eq_sign_mul_kappa (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) :
    kLeadAll m n f = chamberSign m n * kappaJac p q ⌊f - chamberM m n⌋₊ := by
  obtain ⟨h1, h2⟩ := chamber_labels m n p q hp hq
  unfold kLeadAll
  rw [kLead_eq_closed _ _ p q h1 h2, kappaJac]

/-- The same in the paper's notation: `k_{6j} = ε(n,m) κ_d(p,q)` (`eq:kconstants`) with `ε = signE3 n m`. -/
theorem kLeadAll_eq_signE3_mul_kappa (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) :
    kLeadAll m n f = signE3 n m p * kappaJac p q ⌊f - max |m| |n|⌋₊ := by
  rw [kLeadAll_eq_sign_mul_kappa m n f p q hp hq, chamberSign_eq_signE3 m n p hp,
    chamberM_eq_max]

/-- **`k_{6j} ≠ 0` in every chamber.** -/
theorem kLeadAll_ne_zero (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) :
    kLeadAll m n f ≠ 0 := by
  rw [kLeadAll_eq_sign_mul_kappa m n f p q hp hq]
  exact mul_ne_zero (chamberSign_ne_zero m n) (kappaJac_ne_zero _ _ _)

/-- **Exact degree and leading coefficient of the carrier polynomial in every chamber**
(`lem:sqrtfreecarrier`): for `p = |m-n|`, `q = |m+n|` natural, the signed carrier polynomial has degree exactly
`d = ⌊f - max(|m|,|n|)⌋₊` in `τ`, and its `τ^d` coefficient is the nonzero constant
`kLeadAll m n f = ε(n,m) κ_d(p,q)`. -/
theorem carrierPolyAll_natDegree (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) :
    (carrierPolyAll m n f).natDegree = ⌊f - chamberM m n⌋₊ := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (carrierPolyAll_natDegree_le m n f) ?_
  rw [carrierPolyAll_coeff_top]
  exact (MvPolynomial.C_eq_zero.not).mpr (kLeadAll_ne_zero m n f p q hp hq)

/-! ### Link with `carrierAll` -/

/-- The carrier polynomial evaluated at the centered edges `(A,B,C)`: `τ = (1 - cosA)/2`,
`(u,v,w) = (A⁻², B⁻², (AB)⁻¹)`. -/
noncomputable def carrierPolyEval (m n f : ℚ) (A B C : ℝ) : ℝ :=
  evalC ((1 - cosA A B C) / 2) (1 / A ^ 2) (1 / B ^ 2) (1 / (A * B)) (carrierPolyAll m n f)

/-- `carrierAll` is `E · Π^{-1/2} ·` (signed carrier polynomial) with the reduced data
`(M,N)` and the reduced edges `(A',B')`, in every chamber. -/
theorem carrierAll_eq_poly (a b c f m n : ℚ) :
    carrierAll a b c f m n =
      edgeFac (chamberM m n) (chamberN m n) (chamberA a b m n) (chamberB a b m n) (wC c) *
        (Real.sqrt (piSix f (chamberA a b m n) (chamberB a b m n)))⁻¹ *
        carrierPolyEval m n f (chamberA a b m n) (chamberB a b m n) (wC c) := by
  have key : ∀ (M N : ℚ) (A B : ℝ) (s : ℝ) (d : ℕ),
      s * carrierV M N A B (wC c) f d =
        edgeFac M N A B (wC c) * (Real.sqrt (piSix f A B))⁻¹ *
          evalC ((1 - cosA A B (wC c)) / 2) (1 / A ^ 2) (1 / B ^ 2) (1 / (A * B))
            (cc s * ptPoly M N d) := by
    intro M N A B s d
    rw [map_mul, evalC_cc]
    unfold carrierV ptilde6
    ring
  unfold carrierPolyEval carrierPolyAll carrierAll chamberM chamberN chamberSign chamberA chamberB
  by_cases c1 : |n| ≤ m
  · simpa [c1] using (key m n (wA a n) (wB b m) 1 ⌊f - m⌋₊)
  by_cases c2 : |n| ≤ -m
  · simpa [c1, c2, sub_neg_eq_add] using
      (key (-m) (-n) (wA a n) (wB b m) ((-1 : ℝ) ^ ⌊m - n⌋) ⌊f + m⌋₊)
  by_cases c3 : |m| ≤ n
  · simpa [c1, c2, c3] using
      (key n m (wB b m) (wA a n) ((-1 : ℝ) ^ ⌊m - n⌋) ⌊f - n⌋₊)
  · simpa [c1, c2, c3, sub_neg_eq_add] using
      (key (-n) (-m) (wB b m) (wA a n) 1 ⌊f + n⌋₊)

/-- **The `6j` carrier identity in every chamber with the explicit polynomial**: at every physical point
`Φ_f = E W Π^{-1/2} · (ε P̃)`, where `ε P̃ = carrierPolyAll m n f` has degree `⌊f - max(|m|,|n|)⌋₊` and
leading coefficient `kLeadAll m n f = ε(n,m) κ_d(|m-n|,|m+n|) ≠ 0` (`carrierPolyAll_natDegree`,
`carrierPolyAll_coeff_top`, `kLeadAll_ne_zero`). -/
theorem Phi6_eq_poly_all (a b c f m n : ℚ) (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n =
      edgeFac (chamberM m n) (chamberN m n) (chamberA a b m n) (chamberB a b m n) (wC c) *
        (Real.sqrt (piSix f (chamberA a b m n) (chamberB a b m n)))⁻¹ *
        carrierPolyEval m n f (chamberA a b m n) (chamberB a b m n) (wC c) := by
  rw [Phi6_carrier_all a b c f m n h1 h2 h3 h4, carrierAll_eq_poly]

/-- **Zero-scale form in every chamber** (`eq:WignerJacobiMonic` at the polynomial level): for
`p = |m-n|`, `q = |m+n|`, the signed carrier polynomial at `u = v = w = 0` is `k_{6j} · P̂_d^{(p,q)}`,
`P̂` the monic Jacobi polynomial in `τ`. -/
theorem carrierPolyZero_eq_kLeadAll_mul_monic (m n f : ℚ) (p q : ℕ) (hp : |m - n| = p)
    (hq : |m + n| = q) :
    (carrierPolyAll m n f).map (MvPolynomial.eval ![(0 : ℝ), 0, 0]) =
      C (kLeadAll m n f) * jacobiMonicTau p q ⌊f - chamberM m n⌋₊ := by
  obtain ⟨h1, h2⟩ := chamber_labels m n p q hp hq
  have := ptilde6Zero_eq_kLead_mul_monic (chamberM m n) (chamberN m n) p q h1 h2
    ⌊f - chamberM m n⌋₊
  unfold carrierPolyAll kLeadAll
  rw [Polynomial.map_mul, show (cc (chamberSign m n)).map (MvPolynomial.eval ![(0 : ℝ), 0, 0]) =
      C (chamberSign m n) by simp [cc]]
  change C (chamberSign m n) * ptilde6Zero _ _ _ = _
  rw [this, ← mul_assoc, ← C_mul]

/-- info: 'FormalResearch.Racah.carrierPolyAll_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms carrierPolyAll_natDegree

/-- info: 'FormalResearch.Racah.carrierPolyAll_coeff_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms carrierPolyAll_coeff_top

/-- info: 'FormalResearch.Racah.kLeadAll_eq_sign_mul_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kLeadAll_eq_sign_mul_kappa

/-- info: 'FormalResearch.Racah.kLeadAll_eq_signE3_mul_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kLeadAll_eq_signE3_mul_kappa

/-- info: 'FormalResearch.Racah.kLeadAll_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kLeadAll_ne_zero

/-- info: 'FormalResearch.Racah.Phi6_eq_poly_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_eq_poly_all

/-- info: 'FormalResearch.Racah.carrierPolyZero_eq_kLeadAll_mul_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms carrierPolyZero_eq_kLeadAll_mul_monic

end FormalResearch.Racah

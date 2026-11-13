module

public import FormalResearch.Racah.P2AnalyticCarrier6jChambers

/-!
# The `6j` carrier in shape variables, `G6`, and the `t = 0` carrier `dZero6`
(Weyl P2, `lem:sqrtfreecarrier`, `thm:6jeven` proof, `lem:6jseed` holomorphy paragraph)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, proof of `thm:6jeven` ("use the positive
homogeneous analytic scale `S := A+B+C`, `A = Sα`, `B = Sβ`, `C = Sγ`, `t := S⁻²`") and the paragraph
after `lem:6jseed` (every central factor is `Λ^r` times a polynomial in `Λ⁻² = t`).

With `S = A+B+C`, `(α,β,γ) = (A,B,C)/S`, `t = S⁻²` every ingredient of the carrier identity is an
explicit function of `(α,β,γ,t)`:

* the central products are `S^r · Ct r ξ t` (`cenProd_scale`) and the powers of `S` cancel against
  `(4AB)^{2m}`, so the edge factor becomes `√(edgeSqT)`, `edgeSqT = ∏ Ct / (4αβ)^{2m}`;
* `Π_f(A,B) = piSixT f α β t = ∏ (1 - q² t/(4α²))(1 - q² t/(4β²))`;
* the carrier arguments are `A⁻² = t/α²`, `B⁻² = t/β²`, `(AB)⁻¹ = t/(αβ)`, and `x = cosA α β γ` is
  scale invariant.

`G6c m n d α β γ t` (canonical sector) and `G6 f m n α β γ t` (all chambers) are the resulting closed
forms, and `Phi6_eq_G6` is the exact identity `Phi6 = G6 (A/S) (B/S) (C/S) (S⁻²)` at every physical
point.  `dZero6c` is the `t = 0` carrier made explicit, `dZero6c m n d x =
√(((1-x)/2)^{m-n}((1+x)/2)^{m+n}) · P̃_{m+d}(τ; 0,0,0)`; `G6c_zero` proves `G6c … 0 = dZero6c`.
It is *not* called the Wigner `d`: its identification with `d^f_{nm}(arccos x)` is a separate
(Jacobi/Wigner) statement.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

lemma Ct_zero_t (r : ℕ) (u : ℝ) : Ct r u 0 = u ^ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | r + 2, ih =>
      rw [Ct_succ_succ, ih r (by omega)]
      ring

/-- Scaling of a central product: `𝔠_r(Sξ) = S^r · Ct r ξ (S⁻²)` (`lem:centeredshift`). -/
lemma cenProd_scale (r : ℕ) (S ξ : ℝ) (hS : S ≠ 0) :
    cenProd r (S * ξ) = S ^ r * Ct r ξ (1 / S ^ 2) := by
  have h : cenProd r (S * ξ) = S ^ r * Cprod r ξ (1 / S) := by
    unfold cenProd Cprod
    have e : (S ^ r) = ∏ _k ∈ Finset.range r, S := by simp
    rw [e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [h, Cprod_eq_Ct, div_pow, one_pow]

/-! ### Closed forms in the shape variables `(α,β,γ,t)` -/

/-- `Π_f` in shape variables: `∏ (1 - q²t/(4α²))(1 - q²t/(4β²))`, `q = f - k`. -/
noncomputable def piSixT (f : ℚ) (α β t : ℝ) : ℝ :=
  ∏ k ∈ Finset.range ⌈f⌉₊,
    ((1 - ((f : ℝ) - k) ^ 2 * t / (4 * α ^ 2)) * (1 - ((f : ℝ) - k) ^ 2 * t / (4 * β ^ 2)))

/-- The radicand of the edge factor in shape variables: the four central polynomials `Ct` over
`(4αβ)^{2m}` (`m ± n ∈ ℕ`). -/
noncomputable def edgeSqT (m n : ℚ) (α β γ t : ℝ) : ℝ :=
  Ct ⌊m - n⌋₊ (α - β + γ) t * Ct ⌊m - n⌋₊ (-α + β + γ) t *
    Ct ⌊m + n⌋₊ (α + β - γ) t * Ct ⌊m + n⌋₊ (α + β + γ) t / (4 * α * β) ^ ⌊2 * m⌋₊

/-- **The closed-form germ `G6`, canonical sector** (`thm:6jeven` proof):
`G6c m n d α β γ t = √(edgeSqT) · Π_{m+d}(α,β;t)^{-1/2} · P̃_{m+d}(τ; t/α², t/β², t/(αβ))`,
`τ = (1 - cosA α β γ)/2`. -/
noncomputable def G6c (m n : ℚ) (d : ℕ) (α β γ t : ℝ) : ℝ :=
  Real.sqrt (edgeSqT m n α β γ t) * (Real.sqrt (piSixT (m + d) α β t))⁻¹ *
    ptilde6 m n ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d

lemma floor_labels (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) :
    ⌊m - n⌋₊ = p ∧ ⌊m + n⌋₊ = q ∧ ⌊2 * m⌋₊ = p + q := by
  refine ⟨by rw [hp, Nat.floor_natCast], by rw [hq, Nat.floor_natCast], ?_⟩
  have : 2 * m = ((p + q : ℕ) : ℚ) := by push_cast; linarith
  rw [this, Nat.floor_natCast]

/-- The edge factor is the paper's `E_{A,B}(C) W_{6j}(x)` (`eq:6jEdgeFactors`) squared:
with `ℛ_p(X)² = 𝔠_p(X)/X^p`, `p_min = m - n`, `p_max = m + n`, `x = cosA A B C`,
`edgeSq = ℛ_{p_min}(A-B+C)² ℛ_{p_min}(-A+B+C)² ℛ_{p_max}(A+B-C)² ℛ_{p_max}(A+B+C)² ·
((1-x)/2)^{p_min} ((1+x)/2)^{p_max}`
(`eq:6jEdgeProducts`; valid when the four linear forms are nonzero, in particular on the physical
lattice where each is at least `1/2`). -/
lemma edgeSq_eq_EW_sq (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (A B C : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (h1 : A - B + C ≠ 0) (h2 : -A + B + C ≠ 0) (h3 : A + B - C ≠ 0)
    (h4 : A + B + C ≠ 0) :
    edgeSq m n A B C =
      (cenProd p (A - B + C) / (A - B + C) ^ p) * (cenProd p (-A + B + C) / (-A + B + C) ^ p) *
        (cenProd q (A + B - C) / (A + B - C) ^ q) * (cenProd q (A + B + C) / (A + B + C) ^ q) *
        (((1 - cosA A B C) / 2) ^ p * ((1 + cosA A B C) / 2) ^ q) := by
  obtain ⟨f1, f2, f3⟩ := floor_labels m n p q hp hq
  unfold edgeSq
  rw [f1, f2, f3]
  have e1 : (1 - cosA A B C) / 2 = (A - B + C) * (-A + B + C) / (4 * A * B) := by
    unfold cosA; field_simp; ring
  have e2 : (1 + cosA A B C) / 2 = (A + B - C) * (A + B + C) / (4 * A * B) := by
    unfold cosA; field_simp; ring
  rw [e1, e2]
  simp only [div_pow, mul_pow, pow_add]
  have := pow_ne_zero p h1
  have := pow_ne_zero p h2
  have := pow_ne_zero q h3
  have := pow_ne_zero q h4
  field_simp

lemma edgeSq_shape (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (A B C S : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    edgeSq m n A B C = edgeSqT m n (A / S) (B / S) (C / S) (1 / S ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := floor_labels m n p q hp hq
  unfold edgeSq edgeSqT
  rw [h1, h2, h3]
  have e1 : A - B + C = S * (A / S - B / S + C / S) := by field_simp
  have e2 : -A + B + C = S * (-(A / S) + B / S + C / S) := by field_simp
  have e3 : A + B - C = S * (A / S + B / S - C / S) := by field_simp
  have e4 : A + B + C = S * (A / S + B / S + C / S) := by field_simp
  have e5 : 4 * A * B = S ^ 2 * (4 * (A / S) * (B / S)) := by field_simp
  rw [e1, e2, e3, e4, e5]
  simp only [cenProd_scale _ _ _ hS]
  have : ((S ^ 2 * (4 * (A / S) * (B / S))) ^ (p + q)) =
      S ^ (2 * (p + q)) * (4 * (A / S) * (B / S)) ^ (p + q) := by
    rw [mul_pow, ← pow_mul]
  rw [this]
  have hS' : S ^ (2 * (p + q)) ≠ 0 := pow_ne_zero _ hS
  have hden : (4 * (A / S) * (B / S)) ^ (p + q) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero hA hS)) (div_ne_zero hB hS))
  rw [div_eq_div_iff (mul_ne_zero hS' hden) hden]
  ring

lemma piSix_shape (f : ℚ) (A B S : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    piSix f A B = piSixT f (A / S) (B / S) (1 / S ^ 2) := by
  unfold piSix piSixT
  refine Finset.prod_congr rfl fun k _ => ?_
  field_simp

lemma cosA_shape (A B C S : ℝ) (hS : S ≠ 0) : cosA A B C = cosA (A / S) (B / S) (C / S) := by
  unfold cosA
  by_cases hA : A = 0
  · simp [hA]
  by_cases hB : B = 0
  · simp [hB]
  field_simp

/-- **Exact shape-variable form of the canonical carrier**: with `A = Sα`, `B = Sβ`, `C = Sγ`,
`t = S⁻²`, the carrier at rank `f = m + d` equals `G6c m n d α β γ t`. -/
theorem carrierV_shape (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (A B C S : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (d : ℕ) :
    carrierV m n A B C (m + d) d = G6c m n d (A / S) (B / S) (C / S) (1 / S ^ 2) := by
  unfold carrierV G6c edgeFac
  rw [edgeSq_shape m n p q hp hq A B C S hA hB hS, piSix_shape _ A B S hA hB hS,
    cosA_shape A B C S hS]
  have e1 : 1 / A ^ 2 = 1 / S ^ 2 / (A / S) ^ 2 := by field_simp
  have e2 : 1 / B ^ 2 = 1 / S ^ 2 / (B / S) ^ 2 := by field_simp
  have e3 : 1 / (A * B) = 1 / S ^ 2 / (A / S * (B / S)) := by field_simp
  rw [e1, e2, e3]

/-! ### The identity `Phi6 = G6 (A/S) (B/S) (C/S) (S⁻²)` in every chamber -/

/-- The closed-form germ `G6 f m n α β γ t` in every chamber: the canonical `G6c` of the chamber
reduction of `carrierAll` (same chambers, signs and `α ↔ β` swaps). -/
noncomputable def G6 (f m n : ℚ) (α β γ t : ℝ) : ℝ :=
  if |n| ≤ m then G6c m n ⌊f - m⌋₊ α β γ t
  else if |n| ≤ -m then (-1 : ℝ) ^ ⌊m - n⌋ * G6c (-m) (-n) ⌊f + m⌋₊ α β γ t
  else if |m| ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ * G6c n m ⌊f - n⌋₊ β α γ t
  else G6c (-n) (-m) ⌊f + n⌋₊ β α γ t

lemma isNat_sub_of_nonneg {x y : ℚ} (hx : IsNat x) (hy : IsNat y) (h : 0 ≤ x - y) :
    IsNat (x - y) := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  have : l ≤ k := by
    have : (l : ℚ) ≤ k := by linarith
    exact_mod_cast this
  exact ⟨k - l, by push_cast [Nat.cast_sub this]; ring⟩

lemma four_nat {a b f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : f + m = f + (b + m) - b := by ring
    rw [e]; exact h1.1
  · have e : f - m = f - (b + m) + b := by ring
    rw [e]; exact h1.2.1
  · have e : f + n = f - a + (a + n) := by ring
    rw [e]; exact h2.2.1
  · have e : f - n = f + a - (a + n) := by ring
    rw [e]; exact h2.1

lemma canon_labels {f m n : ℚ} (hmn : |n| ≤ m) (a2 : IsNat (f - m))
    (a3 : IsNat (f + n)) (a4 : IsNat (f - n)) :
    (∃ p q : ℕ, m - n = p ∧ m + n = q) ∧ f = m + ((⌊f - m⌋₊ : ℕ) : ℚ) := by
  obtain ⟨hn1, hn2⟩ := abs_le.mp hmn
  refine ⟨?_, ?_⟩
  · have hp : IsNat (m - n) := by
      have e : m - n = (f - n) - (f - m) := by ring
      rw [e]; exact isNat_sub_of_nonneg a4 a2 (by linarith)
    have hq : IsNat (m + n) := by
      have e : m + n = (f + n) - (f - m) := by ring
      rw [e]; exact isNat_sub_of_nonneg a3 a2 (by linarith)
    obtain ⟨p, hp⟩ := hp
    obtain ⟨q, hq⟩ := hq
    exact ⟨p, q, hp, hq⟩
  · obtain ⟨k, hk⟩ := a2
    rw [hk, Nat.floor_natCast]; linarith

/-- Shape form in a canonical-sector chamber, from the four integrality facts. -/
lemma carrierV_shape_canon {f m n : ℚ} (hmn : |n| ≤ m) (a2 : IsNat (f - m))
    (a3 : IsNat (f + n)) (a4 : IsNat (f - n)) (A B C S : ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hS : S ≠ 0) :
    carrierV m n A B C f ⌊f - m⌋₊ = G6c m n ⌊f - m⌋₊ (A / S) (B / S) (C / S) (1 / S ^ 2) := by
  obtain ⟨⟨p, q, hp, hq⟩, hfd⟩ := canon_labels hmn a2 a3 a4
  have := carrierV_shape m n p q hp hq A B C S hA hB hS ⌊f - m⌋₊
  rw [← hfd] at this
  exact this

/-- **`Phi6 = G6 (A/S) (B/S) (C/S) (S⁻²)`** (`thm:6jeven` proof, `lem:sqrtfreecarrier`): at every
physical point and in every chamber, with `A = wA a n`, `B = wB b m`, `C = wC c`, `S = A+B+C`. -/
theorem Phi6_eq_G6 (a b c f m n : ℚ) (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n =
      G6 f m n (wA a n / (wA a n + wB b m + wC c)) (wB b m / (wA a n + wB b m + wC c))
        (wC c / (wA a n + wB b m + wC c)) (1 / (wA a n + wB b m + wC c) ^ 2) := by
  obtain ⟨hA, hB, -, -, -⟩ := admissible_facts h1 h2
  have hC : 0 < wC c := by
    have e1 := isNat_nonneg' h3.1
    have e2 := isNat_nonneg' h3.2.1
    have : (0 : ℝ) ≤ c := by
      have : (0 : ℚ) ≤ c := by linarith
      exact_mod_cast this
    unfold wC; linarith
  have hS : wA a n + wB b m + wC c ≠ 0 := by positivity
  obtain ⟨n1, n2, n3, n4⟩ := four_nat h1 h2
  rw [Phi6_carrier_all a b c f m n h1 h2 h3 h4]
  unfold carrierAll G6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    exact carrierV_shape_canon c1 n2 n3 n4 _ _ _ _ hA.ne' hB.ne' hS
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    congr 1
    have := carrierV_shape_canon (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3) (wA a n) (wB b m) (wC c) (wA a n + wB b m + wC c) hA.ne' hB.ne' hS
    simpa only [sub_neg_eq_add] using this
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    congr 1
    exact carrierV_shape_canon (f := f) (m := n) (n := m) c3 n4 n1 n2 (wB b m) (wA a n) (wC c)
      (wA a n + wB b m + wC c) hB.ne' hA.ne' hS
  have c4 : |m| ≤ -n := by
    rcases le_total 0 n with hn | hn
    · rw [abs_of_nonneg hn] at c1 c2
      exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
    · rw [abs_of_nonpos hn] at c1 c2
      rw [abs_le]; push Not at c1 c2; constructor <;> linarith
  simp only [c1, c2, c3, ↓reduceIte]
  have := carrierV_shape_canon (f := f) (m := -n) (n := -m) (by simpa using c4)
    (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1) (wB b m) (wA a n) (wC c) (wA a n + wB b m + wC c) hB.ne' hA.ne' hS
  simpa only [sub_neg_eq_add] using this

/-- info: 'FormalResearch.Racah.Phi6_eq_G6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_eq_G6

/-! ### The `t = 0` carrier -/

/-- **The `t = 0` carrier** (canonical sector), made explicit and *not* identified with a Wigner
`d`: `dZero6c m n d x = √(((1-x)/2)^{m-n} ((1+x)/2)^{m+n}) · P̃_{m+d}(τ; 0, 0, 0)`, `τ = (1-x)/2`.
Here `√(((1-x)/2)^{m-n}((1+x)/2)^{m+n}) = W_{6j}(x)` and `P̃(τ;0,0,0)` is the zero-scale value of the
carrier. -/
noncomputable def dZero6c (m n : ℚ) (d : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (((1 - x) / 2) ^ ⌊m - n⌋₊ * ((1 + x) / 2) ^ ⌊m + n⌋₊) *
    ptilde6 m n ((1 - x) / 2) 0 0 0 d

/-- The `t = 0` carrier in every chamber (same chambers, signs and `α ↔ β` swap as `G6`; the
cosine `x` is symmetric in `α, β`). -/
noncomputable def dZero6 (f m n : ℚ) (x : ℝ) : ℝ :=
  if |n| ≤ m then dZero6c m n ⌊f - m⌋₊ x
  else if |n| ≤ -m then (-1 : ℝ) ^ ⌊m - n⌋ * dZero6c (-m) (-n) ⌊f + m⌋₊ x
  else if |m| ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ * dZero6c n m ⌊f - n⌋₊ x
  else dZero6c (-n) (-m) ⌊f + n⌋₊ x

lemma piSixT_zero (f : ℚ) (α β : ℝ) : piSixT f α β 0 = 1 := by
  simp [piSixT]

lemma edgeSqT_zero (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (α β γ : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    edgeSqT m n α β γ 0 =
      ((1 - cosA α β γ) / 2) ^ ⌊m - n⌋₊ * ((1 + cosA α β γ) / 2) ^ ⌊m + n⌋₊ := by
  obtain ⟨h1, h2, h3⟩ := floor_labels m n p q hp hq
  unfold edgeSqT
  rw [h1, h2, h3]
  simp only [Ct_zero_t]
  have e1 : (1 - cosA α β γ) / 2 = (α - β + γ) * (-α + β + γ) / (4 * α * β) := by
    unfold cosA; field_simp; ring
  have e2 : (1 + cosA α β γ) / 2 = (α + β - γ) * (α + β + γ) / (4 * α * β) := by
    unfold cosA; field_simp; ring
  rw [e1, e2]
  simp only [div_pow, mul_pow, pow_add]
  ring

/-- At `t = 0` the closed form `G6c` is the explicit `t = 0` carrier `dZero6c` evaluated at the
cosine `x = cosA α β γ`. -/
theorem G6c_zero (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ) (α β γ : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    G6c m n d α β γ 0 = dZero6c m n d (cosA α β γ) := by
  unfold G6c dZero6c
  rw [edgeSqT_zero m n p q hp hq α β γ hα hβ, piSixT_zero]
  simp

/-- info: 'FormalResearch.Racah.G6c_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6c_zero

end FormalResearch.Racah

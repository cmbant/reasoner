module

public import FormalResearch.Racah.P2AnalyticNLO6j
public import FormalResearch.Racah.P2AnalyticUniform6j

/-!
# Uniform next-to-leading `6j` form (Weyl P2, `cor:uniformNLO`, `6j` half)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `cor:uniformNLO` (`eq:6juniformNLO`),
`thm:uniformedge`(b) (`eq:6juniformedge`), `thm:6jclosedcorrection` (`eq:6jclosedg`).

Route.  On the physical lattice `Φ_f = E W · Hall(τ, δ, (A+B)⁻²)` (`Phi6_edge_factor`) with `Hall`
analytic, uniformly Taylor expandable (`Phi6_uniform_edge`, `R = 2`), `W s_0 = d`.  What remains is
the identification of the first Taylor coefficient, for every strict-triangle `(A,B,C)` (not only on
compact sets):

* `s6c_one_eq`, `hasDerivAt_G6c_edge`: canonical sector, `∂_t G6c(·,t)|_{t=0}
  = (α+β)⁻² W s_1(τ;δ) - μ d`, with `μ = nlo6Mu` the `t`-derivative of the edge factor;
* `a6_one_edge`: all four chambers (`a_{f,1} = ∂_t G6(·,t)|_{t=0}`);
* `edgeW_mul_s6_one` (**`W s_1 (A+B)⁻² = G_{f,2} - e_2^{6j} d`**, every strict-triangle `(A,B,C)`):
  together with `G6even_one_eq_closed` (`G_{f,2} = G6closed`) and `e2six_eq`
  (`e_2^{6j} = -μ`, the triangle-pair identities);
* `Phi6_uniform_nlo` (**`eq:6juniformNLO`**): under `λ ≤ A/B ≤ λ⁻¹` (`eq:6jedgeratiobound`),
  uniformly on the whole physical `c`-lattice including its edges,
  `|Φ_f - E_{A,B}[d + G_{f,2} - e_2^{6j} d]| ≤ C (A+B)⁻⁴ E W`;
* `G6closed_sub_e2_eq_poly` (the polynomial form): `G_{f,2} - e_2^{6j} d = W_{6j} (A+B)⁻²
  ∑_{i ≤ f-f₀} c_i(δ) τ^i`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set

/-! ### The first Taylor coefficient of the uniform germ, canonical sector -/

/-- `∂_t Hc(τ,δ,t)` at `t = 0`: `ρ' F(F+1)(2F+1)/6 · P̃(τ;0) + q_d` with `ρ' = (α'⁻²+β'⁻²)/8`,
`α' = (1+δ)/2`, `β' = (1-δ)/2`. -/
lemma hasDerivAt_Hc_t (m n : ℚ) (d : ℕ) (hF : IsNat (2 * (m + (d : ℚ)))) (τ : ℝ) {δ : ℝ}
    (hδ : |δ| < 1) :
    HasDerivAt (fun t => Hc m n d τ δ t)
      ((((((1 + δ) / 2) ^ 2)⁻¹ + (((1 - δ) / 2) ^ 2)⁻¹) / 8 *
          (((m : ℝ) + d) * (((m : ℝ) + d) + 1) * (2 * ((m : ℝ) + d) + 1) / 6)) *
          ptilde6 m n τ 0 0 0 d + q6 m n d ((1 + δ) / 2) ((1 - δ) / 2) τ) 0 := by
  obtain ⟨hα, hβ⟩ := abs_lt_one_alpha hδ
  have hP := hasDerivAt_piSixT_t (m + (d : ℚ)) hF ((1 + δ) / 2) ((1 - δ) / 2) hα.ne' hβ.ne'
  have hsP := hP.sqrt (by rw [piSixT_zero]; exact one_ne_zero)
  have hsPi := hsP.inv (by rw [piSixT_zero]; simp)
  have hfin := hsPi.mul (hasDerivAt_Pt6 m n d ((1 + δ) / 2) ((1 - δ) / 2) τ)
  unfold Hc
  refine hfin.congr_deriv ?_
  simp only [Pi.inv_apply, piSixT_zero, Real.sqrt_one, inv_one, one_pow, Pt6_zero_t, mul_one,
    Real.sqrt_one]
  push_cast
  ring

/-- `s_1 = ∂_t Hc|_{t=0}`. -/
lemma s6c_one_eq (m n : ℚ) (d : ℕ) (hF : IsNat (2 * (m + (d : ℚ)))) (τ : ℝ) {δ : ℝ}
    (hδ : |δ| < 1) :
    s6c m n d 1 τ δ =
      (((((1 + δ) / 2) ^ 2)⁻¹ + (((1 - δ) / 2) ^ 2)⁻¹) / 8 *
          (((m : ℝ) + d) * (((m : ℝ) + d) + 1) * (2 * ((m : ℝ) + d) + 1) / 6)) *
          ptilde6 m n τ 0 0 0 d + q6 m n d ((1 + δ) / 2) ((1 - δ) / 2) τ := by
  unfold s6c taylorCoeff
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact (hasDerivAt_Hc_t m n d hF τ hδ).deriv

/-- Scaling of the ray derivative: `q_d(σα', σβ') = σ⁻² q_d(α', β')`. -/
lemma q6_scale (m n : ℚ) (d : ℕ) (α β τ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    q6 m n d α β τ = (σ ^ 2)⁻¹ * q6 m n d (α / σ) (β / σ) τ := by
  have hfun : (fun t => Pt6 m n d α β τ t) = fun t => Pt6 m n d (α / σ) (β / σ) τ (t / σ ^ 2) := by
    funext t
    unfold Pt6
    have e1 : t / α ^ 2 = t / σ ^ 2 / (α / σ) ^ 2 := by
      by_cases hα : α = 0
      · simp [hα]
      · field_simp
    have e2 : t / β ^ 2 = t / σ ^ 2 / (β / σ) ^ 2 := by
      by_cases hβ : β = 0
      · simp [hβ]
      · field_simp
    have e3 : t / (α * β) = t / σ ^ 2 / (α / σ * (β / σ)) := by
      by_cases hα : α = 0
      · simp [hα]
      · by_cases hβ : β = 0
        · simp [hβ]
        · field_simp
    rw [e1, e2, e3]
  have h1 : HasDerivAt (fun t : ℝ => t / σ ^ 2) (1 / σ ^ 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (σ ^ 2)
  have h2 : HasDerivAt (fun t => Pt6 m n d (α / σ) (β / σ) τ t)
      (q6 m n d (α / σ) (β / σ) τ) (0 / σ ^ 2) := by
    rw [zero_div]; exact hasDerivAt_Pt6 m n d (α / σ) (β / σ) τ
  have h3 := h2.comp_of_eq (0 : ℝ) h1 (by simp)
  have h4 := (hasDerivAt_Pt6 m n d α β τ)
  rw [hfun] at h4
  have := h4.unique h3
  rw [this]
  simp only [one_div]
  ring

/-- **`∂_t G6c` at `t = 0` in terms of the uniform coefficient** (canonical sector, strict-triangle
shape): `∂_t G6c(·,t)|_{t=0} = (α+β)⁻² W s_1(τ;δ) - μ dZero6c`, `μ = nlo6Mu`, `τ = (1-x)/2`,
`δ = (α-β)/(α+β)`, `W = √(((1-x)/2)^p ((1+x)/2)^q)`. -/
theorem hasDerivAt_G6c_edge (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (d : ℕ)
    {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    HasDerivAt (fun t => G6c m n d α β γ t)
      (((α + β) ^ 2)⁻¹ * edgeW p q (cosA α β γ) *
          s6c m n d 1 ((1 - cosA α β γ) / 2) ((α - β) / (α + β)) -
        nlo6Mu (p : ℝ) (q : ℝ) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ) *
          dZero6c m n d (cosA α β γ)) 0 := by
  have h := hasDerivAt_G6c_t m n p q hp hq d hz
  obtain ⟨hα, hβ, hγ, -⟩ := hz
  have hσ : 0 < α + β := by linarith
  have hδ : |(α - β) / (α + β)| < 1 := by
    rw [abs_div, abs_of_pos hσ, div_lt_one hσ]
    rw [abs_lt]; constructor <;> linarith
  have ea : (1 + (α - β) / (α + β)) / 2 = α / (α + β) := by field_simp; ring
  have eb : (1 - (α - β) / (α + β)) / 2 = β / (α + β) := by field_simp; ring
  have hF : IsNat (2 * (m + (d : ℚ))) := ⟨p + q + 2 * d, by
    have : 2 * m = ((p + q : ℕ) : ℚ) := by push_cast; linarith
    push_cast at this ⊢; linarith⟩
  have hs := s6c_one_eq m n d hF ((1 - cosA α β γ) / 2) hδ
  rw [ea, eb] at hs
  have hq6 := q6_scale m n d α β ((1 - cosA α β γ) / 2) hσ.ne'
  have hd : dZero6c m n d (cosA α β γ) =
      edgeW p q (cosA α β γ) * ptilde6 m n ((1 - cosA α β γ) / 2) 0 0 0 d := by
    obtain ⟨f1, f2, -⟩ := floor_labels m n p q hp hq
    unfold dZero6c edgeW
    rw [f1, f2]
  refine h.congr_deriv ?_
  rw [hs, hd]
  unfold edgeW
  have hq6' := hq6
  rw [hq6']
  set W := Real.sqrt (((1 - cosA α β γ) / 2) ^ p * ((1 + cosA α β γ) / 2) ^ q)
  set P0 := ptilde6 m n ((1 - cosA α β γ) / 2) 0 0 0 d
  set Q' := q6 m n d (α / (α + β)) (β / (α + β)) ((1 - cosA α β γ) / 2)
  set μ := nlo6Mu (p : ℝ) (q : ℝ) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β)) (cosA α β γ)
  field_simp
  ring

/-! ### All four chambers -/

lemma floor_abs_eq {x : ℚ} {p : ℕ} (h : x = p ∨ -x = p) : ⌊|x|⌋₊ = p := by
  rcases h with h | h
  · rw [h, abs_of_nonneg (Nat.cast_nonneg p), Nat.floor_natCast]
  · rw [← neg_neg x, h, abs_neg, abs_of_nonneg (Nat.cast_nonneg p), Nat.floor_natCast]

/-- **`a_{f,1} = ∂_t G6(·,t)|_{t=0}` in terms of the uniform coefficient `s_1`** (all four chambers,
strict-triangle shape): with `x = cosA α β γ`, `τ = (1-x)/2`, `δ = (α-β)/(α+β)`,
`a_{f,1} = (α+β)⁻² W_{6j}(x) s_1(τ;δ) - μ d`, `μ = nlo6Mu p_min p_max ρ w x`,
`d = dZero6 f m n x`. -/
theorem a6_one_edge (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m)) (n3 : IsNat (f + n))
    (n4 : IsNat (f - n)) {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    a6 f m n 1 (α, β, γ) =
      ((α + β) ^ 2)⁻¹ * edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA α β γ) *
          s6 f m n 1 ((1 - cosA α β γ) / 2) ((α - β) / (α + β)) -
        nlo6Mu (⌊|m - n|⌋₊ : ℝ) (⌊|m + n|⌋₊ : ℝ) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β))
          (cosA α β γ) * dZero6 f m n (cosA α β γ) := by
  rw [a6_one_eq_deriv]
  have hz' := swap6_mem_StrictTri hz
  unfold G6 s6 dZero6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels c1 n2 n3 n4
    rw [floor_abs_eq (Or.inl hp), floor_abs_eq (Or.inl hq)]
    exact (hasDerivAt_G6c_edge m n p q hp hq _ hz).deriv
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    have hp' : -(m - n) = p := by rw [← hp]; ring
    have hq' : -(m + n) = q := by rw [← hq]; ring
    rw [floor_abs_eq (Or.inr hp'), floor_abs_eq (Or.inr hq')]
    have h := ((hasDerivAt_G6c_edge (-m) (-n) p q hp hq ⌊f + m⌋₊ hz).const_mul
      ((-1 : ℝ) ^ ⌊m - n⌋)).deriv
    rw [h]
    ring
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    have hp' : -(m - n) = p := by rw [← hp]; ring
    have hq' : m + n = q := by rw [← hq]; ring
    rw [floor_abs_eq (Or.inr hp'), floor_abs_eq (Or.inl hq')]
    have h := ((hasDerivAt_G6c_edge n m p q hp hq ⌊f - n⌋₊ hz').const_mul
      ((-1 : ℝ) ^ ⌊m - n⌋)).deriv
    have e1 : (β - α) / (β + α) = -((α - β) / (α + β)) := by rw [add_comm β α]; ring
    have e2 : ((β ^ 2)⁻¹ + (α ^ 2)⁻¹) / 8 = ((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8 := by ring
    rw [cosA_comm', e1, e2, add_comm β α, mul_comm β α] at h
    rw [h]
    ring
  · have c4 : |m| ≤ -n := by
      rcases le_total 0 n with hn | hn
      · rw [abs_of_nonneg hn] at c1 c2
        exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
      · rw [abs_of_nonpos hn] at c1 c2
        rw [abs_le]; push Not at c1 c2; constructor <;> linarith
    simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
      (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
    have hp' : m - n = p := by rw [← hp]; ring
    have hq' : -(m + n) = q := by rw [← hq]; ring
    rw [floor_abs_eq (Or.inl hp'), floor_abs_eq (Or.inr hq')]
    have h := (hasDerivAt_G6c_edge (-n) (-m) p q hp hq ⌊f + n⌋₊ hz').deriv
    have e1 : (β - α) / (β + α) = -((α - β) / (α + β)) := by rw [add_comm β α]; ring
    have e2 : ((β ^ 2)⁻¹ + (α ^ 2)⁻¹) / 8 = ((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8 := by ring
    rw [cosA_comm', e1, e2, add_comm β α, mul_comm β α] at h
    rw [h]

/-! ### The coefficient identity `W s_1 (A+B)⁻² = G_{f,2} - e_2 d` -/

lemma nlo6Mu_smul (p q ρ w x c : ℝ) : nlo6Mu p q (c * ρ) (c * w) x = c * nlo6Mu p q ρ w x := by
  unfold nlo6Mu; ring

/-- **`G_{f,2} = (A+B)⁻² W_{6j} s_1(τ;δ) - μ d`** (every chamber, every strict-triangle `(A,B,C)`):
`G6closed` (`eq:6jclosedg`) in terms of the first uniform coefficient and the `t`-derivative `μ`
of the edge factor. -/
theorem G6closed_eq_edge (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m)) (n3 : IsNat (f + n))
    (n4 : IsNat (f - n)) {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    G6closed f m n A B C =
      ((A + B) ^ 2)⁻¹ * edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA A B C) *
          s6 f m n 1 ((1 - cosA A B C) / 2) ((A - B) / (A + B)) -
        nlo6Mu (⌊|m - n|⌋₊ : ℝ) (⌊|m + n|⌋₊ : ℝ) (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) (1 / (A * B))
          (cosA A B C) * dZero6 f m n (cosA A B C) := by
  have hshape := shape_strictTri h
  rw [← G6even_one_eq_closed f m n n1 n2 n3 n4 h]
  obtain ⟨hA, hB, hC, -⟩ := h
  have hS : 0 < A + B + C := by linarith
  have hAB : 0 < A + B := by linarith
  unfold G6even
  rw [a6_one_edge f m n n1 n2 n3 n4 hshape]
  have e1 : (((A / (A + B + C)) ^ 2)⁻¹ + ((B / (A + B + C)) ^ 2)⁻¹) / 8 =
      (A + B + C) ^ 2 * (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) := by
    field_simp
  have e2 : 1 / (A / (A + B + C) * (B / (A + B + C))) = (A + B + C) ^ 2 * (1 / (A * B)) := by
    field_simp
  have e3 : cosA (A / (A + B + C)) (B / (A + B + C)) (C / (A + B + C)) = cosA A B C :=
    (cosA_shape A B C _ hS.ne').symm
  have e4 : (A / (A + B + C) - B / (A + B + C)) / (A / (A + B + C) + B / (A + B + C)) =
      (A - B) / (A + B) := by field_simp
  have e5 : ((A / (A + B + C) + B / (A + B + C)) ^ 2)⁻¹ = (A + B + C) ^ 2 * ((A + B) ^ 2)⁻¹ := by
    field_simp
  rw [e1, e2, e3, e4, e5, nlo6Mu_smul]
  have : ((A + B + C) ^ (2 * 1))⁻¹ * (A + B + C) ^ 2 = 1 := by
    rw [mul_one]; field_simp
  linear_combination (((A + B) ^ 2)⁻¹ * edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA A B C) *
          s6 f m n 1 ((1 - cosA A B C) / 2) ((A - B) / (A + B)) -
        nlo6Mu (⌊|m - n|⌋₊ : ℝ) (⌊|m + n|⌋₊ : ℝ) (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) (1 / (A * B))
          (cosA A B C) * dZero6 f m n (cosA A B C)) * this

/-! ### The paper's `e_2^{6j}` -/

/-- The paper's `e_2^{6j}` (homogeneous degree `-2` term of `log E_{A,B}(C)`):
`-p(p²-1)/48 [(A-B+C)⁻² + (-A+B+C)⁻²] - q(q²-1)/48 [(A+B-C)⁻² + (A+B+C)⁻²]`, `p = p_min`,
`q = p_max`. -/
noncomputable def e2six (p q : ℕ) (A B C : ℝ) : ℝ :=
  -((p : ℝ) * ((p : ℝ) ^ 2 - 1) / 48) * (1 / (A - B + C) ^ 2 + 1 / (-A + B + C) ^ 2) -
    (q : ℝ) * ((q : ℝ) ^ 2 - 1) / 48 * (1 / (A + B - C) ^ 2 + 1 / (A + B + C) ^ 2)

/-- `e_2^{6j} = -μ`, `μ = nlo6Mu` (the triangle-pair identities `eq:trianglePairIdentities`). -/
theorem e2six_eq (p q : ℕ) {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    e2six p q A B C =
      -nlo6Mu (p : ℝ) (q : ℝ) (((A ^ 2)⁻¹ + (B ^ 2)⁻¹) / 8) (1 / (A * B)) (cosA A B C) := by
  have hxI := nlo6_cosA_mem_Ioo h
  obtain ⟨hA, hB, hC, h1, h2, h3⟩ := h
  have hx1 : 0 < 1 - cosA A B C := by linarith [hxI.2]
  have hx2 : 0 < 1 + cosA A B C := by linarith [hxI.1]
  have p12 := nlo6_pair12 A B C hA.ne' hB.ne' (by linarith) (by linarith) hx1.ne'
  have p34 := nlo6_pair34 A B C hA.ne' hB.ne' (by linarith) (by linarith) hx2.ne'
  unfold e2six nlo6Mu nlo6cc
  simp only [one_div, ← inv_pow] at *
  rw [p12, p34]
  ring

/-- **`W s_1 (A+B)⁻² = G_{f,2} - e_2^{6j} d`** (every chamber, every strict-triangle `(A,B,C)`),
with `G_{f,2} = G6closed` (`eq:6jclosedg`), `d = d^f_{nm}(arccos x)`, `x = cosA A B C`,
`τ = (1-x)/2`, `δ = (A-B)/(A+B)`. -/
theorem edgeW_mul_s6_one (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) {A B C : ℝ} (h : (A, B, C) ∈ StrictTri) :
    ((A + B) ^ 2)⁻¹ * edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA A B C) *
        s6 f m n 1 ((1 - cosA A B C) / 2) ((A - B) / (A + B)) =
      G6closed f m n A B C -
        e2six ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ A B C * wignerSmallDx f n m (cosA A B C) := by
  have hxI := nlo6_cosA_mem_Ioo h
  have hx : cosA A B C ∈ Icc (-1 : ℝ) 1 := ⟨hxI.1.le, hxI.2.le⟩
  have k := G6closed_eq_edge f m n n1 n2 n3 n4 h
  rw [e2six_eq _ _ h, dZero6_eq_wignerD f m n n1 n2 n3 n4 hx] at *
  rw [k]
  ring

/-- **`eq:6juniformNLO`** (`cor:uniformNLO`, `6j` half; proved, Lean form).  Fix admissible
`f, m, n` (the four triads of the `6j` family) and `0 < λ < 1`.  There are `C, S₀` such that for
every physical admissible point with `λ ≤ A/B ≤ λ⁻¹` (`eq:6jedgeratiobound`, needed as in
`thm:uniformedge`(b)) and `S = A + B ≥ S₀`, with `A = wA a n`, `B = wB b m`, `C = wC c`,
`x = cosA A B C`, `d = d^f_{nm}(arccos x)`, `p_min = ⌊|m-n|⌋₊`, `p_max = ⌊|m+n|⌋₊`,
`|Φ_f - E_{A,B}(C) [d + G_{f,2} - e_2^{6j} d]| ≤ C (A+B)⁻⁴ E_{A,B}(C) W_{6j}(x)`,
with `G_{f,2} = G6closed` (`eq:6jclosedg`), `e_2^{6j} = e2six`.  The bound holds on the whole
physical `c`-lattice, up to the edges `x = ±1` (no compact subset of the strict triangles is
assumed). -/
theorem Phi6_uniform_nlo (f m n : ℚ) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → lam * wB b m ≤ wA a n → wA a n ≤ wB b m / lam →
      S₀ ≤ wA a n + wB b m →
      |Phi6 a b c f m n -
          edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
            (wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) +
              G6closed f m n (wA a n) (wB b m) (wC c) -
              e2six ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
                wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)))| ≤
        C / (wA a n + wB b m) ^ 4 *
          edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) := by
  obtain ⟨C, S₀, h⟩ := Phi6_uniform_edge f m n hlam0 hlam1 2
  refine ⟨C, S₀, fun a b c h1 h2 h3 h4 hl1 hl2 hS0 => ?_⟩
  have key := h a b c h1 h2 h3 h4 hl1 hl2 hS0
  obtain ⟨hA, hB, hC, hSpos⟩ := physical_scale_pos h1 h2 h3
  obtain ⟨e1, e2, e3, e4⟩ := phys_edge_args h1 h2 h3 h4
  obtain ⟨n1, n2, n3, n4⟩ := four_nat h1 h2
  have hp : (0 : ℝ) < ((⌊|m - n|⌋₊ : ℕ) : ℝ) + 1 := by positivity
  have hq : (0 : ℝ) < ((⌊|m + n|⌋₊ : ℕ) : ℝ) + 1 := by positivity
  have hst : (wA a n, wB b m, wC c) ∈ StrictTri :=
    ⟨hA, hB, hC, by linarith, by linarith, by linarith⟩
  have hxI := nlo6_cosA_mem_Ioo hst
  have hx : cosA (wA a n) (wB b m) (wC c) ∈ Icc (-1 : ℝ) 1 := ⟨hxI.1.le, hxI.2.le⟩
  have h0 := edgeW_mul_s6_zero f m n (cosA (wA a n) (wB b m) (wC c))
    ((wA a n - wB b m) / (wA a n + wB b m))
  rw [dZero6_eq_wignerD f m n n1 n2 n3 n4 hx] at h0
  have h1' := edgeW_mul_s6_one f m n n1 n2 n3 n4 hst
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero, div_one,
    mul_one] at key
  have e : 2 * 2 = 4 := rfl
  rw [e] at key
  unfold edgeEW at key ⊢
  set E := edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c)
  set W := edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA (wA a n) (wB b m) (wC c))
  set s0 := s6 f m n 0 ((1 - cosA (wA a n) (wB b m) (wC c)) / 2)
    ((wA a n - wB b m) / (wA a n + wB b m))
  set s1 := s6 f m n 1 ((1 - cosA (wA a n) (wB b m) (wC c)) / 2)
    ((wA a n - wB b m) / (wA a n + wB b m))
  have hS : 0 < wA a n + wB b m := by linarith
  have hid : E * W * (s0 + s1 / (wA a n + wB b m) ^ 2) =
      E * (wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) +
        G6closed f m n (wA a n) (wB b m) (wC c) -
        e2six ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
          wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c))) := by
    have h2' : W * s1 / (wA a n + wB b m) ^ 2 =
        G6closed f m n (wA a n) (wB b m) (wC c) -
          e2six ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
            wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) := by
      rw [← h1']; field_simp
    linear_combination E * h0 + E * h2'
  rw [hid] at key
  calc _ ≤ _ := key
    _ = _ := by ring

/-- **The polynomial form** (`cor:uniformNLO`, last two sentences): for each `δ ∈ (-1,1)` there are
coefficients `c_i(δ)` such that at every strict-triangle `(A,B,C)` with `(A-B)/(A+B) = δ`,
`G_{f,2} - e_2^{6j} d = W_{6j}(x) (A+B)⁻² ∑_{i ≤ f - f₀} c_i τ^i`, `f₀ = max(|m|,|n|)`,
`τ = (1-x)/2`.  So the combination is `W` times a polynomial of degree at most `f - f₀` in `τ`,
and its apparent endpoint poles cancel: the only endpoint powers are those of `W`. -/
theorem G6closed_sub_e2_eq_poly (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m))
    (n3 : IsNat (f + n)) (n4 : IsNat (f - n)) {δ : ℝ} (hδ : |δ| < 1) :
    ∃ c : ℕ → ℝ, ∀ A B C : ℝ, (A, B, C) ∈ StrictTri → (A - B) / (A + B) = δ →
      G6closed f m n A B C -
          e2six ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ A B C * wignerSmallDx f n m (cosA A B C) =
        edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (cosA A B C) * ((A + B) ^ 2)⁻¹ *
          ∑ i ∈ Finset.range (⌊f - max |m| |n|⌋₊ + 1), c i * ((1 - cosA A B C) / 2) ^ i := by
  have hs : ∃ c : ℕ → ℝ, ∀ τ : ℝ, s6 f m n 1 τ δ =
      ∑ i ∈ Finset.range (⌊f - max |m| |n|⌋₊ + 1), c i * τ ^ i := by
    unfold s6
    by_cases c1 : |n| ≤ m
    · simp only [c1, ↓reduceIte]
      have hm : max |m| |n| = m := by
        rw [abs_of_nonneg (le_trans (abs_nonneg n) c1)]; exact max_eq_left c1
      rw [hm]
      exact ⟨fun i => cKc m n ⌊f - m⌋₊ i 1 δ, fun τ => s6c_eq_sum m n _ 1 τ hδ⟩
    by_cases c2 : |n| ≤ -m
    · simp only [c1, c2, ↓reduceIte]
      have hm : max |m| |n| = -m := by
        rw [abs_of_nonpos (by linarith [abs_nonneg n] : m ≤ 0)]
        exact max_eq_left c2
      rw [hm, sub_neg_eq_add]
      exact ⟨fun i => (-1 : ℝ) ^ ⌊m - n⌋ * cKc (-m) (-n) ⌊f + m⌋₊ i 1 δ, fun τ => by
        rw [s6c_eq_sum (-m) (-n) _ 1 τ hδ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring⟩
    by_cases c3 : |m| ≤ n
    · simp only [c1, c2, c3, ↓reduceIte]
      have hm : max |m| |n| = n := by
        rw [abs_of_nonneg (le_trans (abs_nonneg m) c3)]; exact max_eq_right c3
      rw [hm]
      have hδ' : |-δ| < 1 := by rwa [abs_neg]
      exact ⟨fun i => (-1 : ℝ) ^ ⌊m - n⌋ * cKc n m ⌊f - n⌋₊ i 1 (-δ), fun τ => by
        rw [s6c_eq_sum n m _ 1 τ hδ', Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring⟩
    · have c4 : |m| ≤ -n := by
        rcases le_total 0 n with hn | hn
        · rw [abs_of_nonneg hn] at c1 c2
          exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
        · rw [abs_of_nonpos hn] at c1 c2
          rw [abs_le]; push Not at c1 c2; constructor <;> linarith
      simp only [c1, c2, c3, ↓reduceIte]
      have hm : max |m| |n| = -n := by
        rw [abs_of_nonpos (by linarith [abs_nonneg m] : n ≤ 0)]
        exact max_eq_right c4
      rw [hm, sub_neg_eq_add]
      have hδ' : |-δ| < 1 := by rwa [abs_neg]
      exact ⟨fun i => cKc (-n) (-m) ⌊f + n⌋₊ i 1 (-δ), fun τ => s6c_eq_sum (-n) (-m) _ 1 τ hδ'⟩
  obtain ⟨c, hc⟩ := hs
  refine ⟨c, fun A B C h hδe => ?_⟩
  rw [← edgeW_mul_s6_one f m n n1 n2 n3 n4 h, hδe, hc]
  ring

/-- info: 'FormalResearch.Racah.hasDerivAt_G6c_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_G6c_edge

/-- info: 'FormalResearch.Racah.a6_one_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms a6_one_edge

/-- info: 'FormalResearch.Racah.edgeW_mul_s6_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeW_mul_s6_one

/-- info: 'FormalResearch.Racah.Phi6_uniform_nlo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_uniform_nlo

/-- info: 'FormalResearch.Racah.G6closed_sub_e2_eq_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6closed_sub_e2_eq_poly

end FormalResearch.Racah

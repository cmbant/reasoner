module

public import FormalResearch.Racah.P2AnalyticCarrierRacahAll

/-!
# Degree bounds and the `O(ε²)` estimate for the even Racah deformation (Weyl P2, `lem:evendeformation6j`,
`eq:evendeformationbound`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:evendeformation6j`: "the coefficient of `ς^{d-j}`
is a polynomial of degree at most `j` in `ε²`, `ε = S⁻¹`, whose coefficients are rational in `δ²` with
denominator `(1-δ²)^j`", and `eq:evendeformationbound`
`sup_{0≤ς≤1, |δ|≤δ₀} |q_d(ς; ε, δ) - P̂_d^{(p,p')}(ς)| ≤ C ε²`.

The paper proves these from the Racah difference operator `ℒ_ε`.  The Lean route uses the carrier recurrence
`eq:6jrankpoly` instead.  Writing `u = A⁻²`, `v = B⁻²`, `w = (AB)⁻¹`, the coefficients of `P̃` are
polynomials in `s₁ = u+v`, `s₂ = uv`, `w` (the recurrence involves `u, v` only through
`η_f² = 1 - (f²/4)s₁ + (f⁴/16)s₂`), and a monomial `τ^i s₁^a s₂^b w^c` occurs only when its **weight**
`i + 2a + 2b + c ≤ d` (`FilS`; the diagonal coefficient has weight `1` (`τ` or `w`), the backward coefficient
`η²` has weight `2`, and `P̃_{f+1}` is obtained from `P̃_f` (weight `+1`) and `P̃_{f-1}` (weight `+2`)).
In `ε = S⁻¹`, `δ = (A-B)/S`: `u = 4ε²/(1+δ)²`, `v = 4ε²/(1-δ)²`, `w = 4ε²/(1-δ²)`, so
`s₁ = 8ε²(1+δ²)/(1-δ²)²`, `s₂ = 16ε⁴/(1-δ²)²`, and the weight bound is exactly the paper's degree and
denominator bound.

* `ptPoly_inFil`: `P̃_{m+d}` is in the weight-`d` filtration `InFil d` (all `m, n`);
* `evenRacah6All_coeff_form`: **the degree bound of `lem:evendeformation6j`**: the coefficient of `ς^{d-j}` of `q_d`
  at `(u,v,w) = (4ε²/(1+δ)², 4ε²/(1-δ)², 4ε²/(1-δ²))` is `∑_{s ≤ j} ε^{2s} M_s(δ²)/(1-δ²)^j` with
  `M_s ∈ ℝ[X]` independent of `ε, δ`;
* `shapeEval`, `shapeEval_eq_AB`: `q_d(ς; ε, δ)` and its relation to `A, B`;
* `evenRacah6All_bound`: **`eq:evendeformationbound`**, in every chamber (`q_d = evenRacah6All`), for
  `0 < ε ≤ 1`, `|δ| ≤ δ₀ < 1`, `0 ≤ ς ≤ 1`.

Not formalised: the Racah difference operator `ℒ_ε` and the evenness argument of the paper (not needed: the
weight bound is proved from the recurrence).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

/-! ### The weight filtration -/

/-- The weight of a monomial `s₁^a s₂^b w^c`: `2a + 2b + c`. -/
def wtS (s : Fin 3 →₀ ℕ) : ℕ := 2 * s 0 + 2 * s 1 + s 2

/-- `P ∈ ℝ[s₁,s₂,w][τ]` lies in the weight filtration of level `d`: every monomial `τ^i s^s` of `P` has
`i + wtS s ≤ d`. -/
def FilS (d : ℕ) (P : Polynomial (MvPolynomial (Fin 3) ℝ)) : Prop :=
  ∀ i s, (P.coeff i).coeff s ≠ 0 → i + wtS s ≤ d

lemma FilS.mono {d e : ℕ} {P : CarrierRing} (h : FilS d P) (he : d ≤ e) : FilS e P :=
  fun i s hs => (h i s hs).trans he

lemma FilS.add {d : ℕ} {P Q : CarrierRing} (hP : FilS d P) (hQ : FilS d Q) : FilS d (P + Q) := by
  intro i s hs
  rw [Polynomial.coeff_add] at hs
  have hs' : (P.coeff i).coeff s + (Q.coeff i).coeff s ≠ 0 := hs
  by_cases h : (P.coeff i).coeff s = 0
  · rw [h, zero_add] at hs'; exact hQ i s hs'
  · exact hP i s h

lemma FilS.neg {d : ℕ} {P : CarrierRing} (hP : FilS d P) : FilS d (-P) := by
  intro i s hs
  rw [Polynomial.coeff_neg, MvPolynomial.coeff_neg] at hs
  exact hP i s (neg_ne_zero.mp hs)

lemma FilS.sub {d : ℕ} {P Q : CarrierRing} (hP : FilS d P) (hQ : FilS d Q) : FilS d (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

lemma FilS.mul {d e : ℕ} {P Q : CarrierRing} (hP : FilS d P) (hQ : FilS e Q) :
    FilS (d + e) (P * Q) := by
  intro k s hs
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum] at hs
  obtain ⟨⟨i, j⟩, hij, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  rw [MvPolynomial.coeff_mul] at h1
  obtain ⟨⟨s1, s2⟩, hs12, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have e1 := hP i s1 (left_ne_zero_of_mul h2)
  have e2 := hQ j s2 (right_ne_zero_of_mul h2)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij hs12
  have w : wtS s = wtS s1 + wtS s2 := by
    subst hs12; simp only [wtS, Finsupp.add_apply]; omega
  omega

lemma FilS_C {j : ℕ} (p : MvPolynomial (Fin 3) ℝ) (hp : ∀ s, p.coeff s ≠ 0 → wtS s ≤ j) :
    FilS j (Polynomial.C p) := by
  intro i s hs
  rw [Polynomial.coeff_C] at hs
  by_cases hi : i = 0
  · subst hi; simpa using hp s (by simpa using hs)
  · simp [hi] at hs

lemma FilS_cc (r : ℝ) : FilS 0 (cc r) := by
  refine FilS_C _ fun s hs => ?_
  rw [MvPolynomial.coeff_C] at hs
  split_ifs at hs with h
  · subst h; simp [wtS]
  · exact absurd rfl hs

lemma FilS_one : FilS 0 (1 : CarrierRing) := by
  have : (1 : CarrierRing) = cc 1 := by simp [cc]
  rw [this]; exact FilS_cc 1

lemma FilS_X : FilS 1 (Polynomial.X : CarrierRing) := by
  intro i s hs
  rw [Polynomial.coeff_X] at hs
  split_ifs at hs with h
  · subst h
    have : s = 0 := by
      by_contra hne
      exact hs (by simp [MvPolynomial.coeff_one, Ne.symm hne])
    simp [this, wtS]
  · simp at hs

lemma FilS_var (k : Fin 3) {j : ℕ} (hj : wtS (Finsupp.single k 1) ≤ j) :
    FilS j (Polynomial.C (MvPolynomial.X k) : CarrierRing) := by
  refine FilS_C _ fun s hs => ?_
  rw [MvPolynomial.coeff_X] at hs
  split_ifs at hs with h
  · rw [← h]; exact hj
  · exact absurd rfl hs

/-- The variable `s₁ = u + v`, `s₂ = u v`, `w` of the filtered ring. -/
noncomputable abbrev sVar1 : CarrierRing := Polynomial.C (MvPolynomial.X 0)
noncomputable abbrev sVar2 : CarrierRing := Polynomial.C (MvPolynomial.X 1)

/-- `η_f²` in the variables `s₁ = u+v`, `s₂ = uv`. -/
noncomputable def eta2S (f : ℝ) : CarrierRing :=
  1 - cc (f ^ 2 / 4) * sVar1 + cc (f ^ 4 / 16) * sVar2

/-- The ring map `ℝ[s₁,s₂,w] → ℝ[u,v,w]`, `s₁ ↦ u+v`, `s₂ ↦ uv`, `w ↦ w`. -/
noncomputable def phiS : MvPolynomial (Fin 3) ℝ →+* MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 2]

lemma phiS_C (r : ℝ) : phiS (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [phiS]

lemma phiS_X0 : phiS (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [phiS]

lemma phiS_X1 : phiS (MvPolynomial.X 1) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [phiS]

lemma phiS_X2 : phiS (MvPolynomial.X 2) = MvPolynomial.X 2 := by
  simp [phiS]

lemma eval_phiS (u v w : ℝ) (c : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.eval ![u, v, w] (phiS c) = MvPolynomial.eval ![u + v, u * v, w] c := by
  have : (MvPolynomial.eval ![u, v, w]).comp phiS = MvPolynomial.eval ![u + v, u * v, w] := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [phiS]
    · intro i; fin_cases i <;> simp [phiS]
  exact RingHom.congr_fun this c

/-- Pushing forward along `phiS`. -/
noncomputable def pushS : CarrierRing →+* CarrierRing := Polynomial.mapRingHom phiS

lemma evalC_pushS (τ u v w : ℝ) (P : CarrierRing) :
    evalC τ u v w (pushS P) = evalC τ (u + v) (u * v) w P := by
  unfold evalC pushS
  rw [Polynomial.coe_eval₂RingHom, Polynomial.coe_mapRingHom, Polynomial.eval₂_map,
    Polynomial.coe_eval₂RingHom]
  congr 1
  apply RingHom.ext
  intro c
  exact eval_phiS u v w c

lemma pushS_cc (r : ℝ) : pushS (cc r) = cc r := by
  simp [pushS, cc, phiS_C]

lemma pushS_X : pushS (Polynomial.X : CarrierRing) = Polynomial.X := by
  simp [pushS]

lemma pushS_wVar : pushS wVar = wVar := by
  simp [pushS, wVar, phiS_X2]

lemma pushS_diagP (m n : ℚ) (f : ℝ) : pushS (diagP m n f) = diagP m n f := by
  unfold diagP
  simp only [map_sub, map_mul, map_one, pushS_cc, pushS_X, pushS_wVar]

lemma pushS_eta2S (f : ℝ) : pushS (eta2S f) = eta2P f := by
  unfold eta2S eta2P
  have h1 : pushS sVar1 = uVar + vVar := by
    simp only [pushS, Polynomial.coe_mapRingHom, Polynomial.map_C, phiS_X0, uVar, vVar,
      Polynomial.C_add]
  have h2 : pushS sVar2 = uVar * vVar := by
    simp only [pushS, Polynomial.coe_mapRingHom, Polynomial.map_C, phiS_X1, uVar, vVar,
      Polynomial.C_mul]
  simp only [map_add, map_sub, map_mul, map_one, pushS_cc, h1, h2]
  have : cc (f ^ 4 / 16) = cc (f ^ 2 / 4) * cc (f ^ 2 / 4) := by
    rw [← cc_mul']; congr 1; ring
  rw [this]; ring

/-- `Q` is the push-forward of an element of the weight-`d` filtration. -/
def InFil (d : ℕ) (Q : CarrierRing) : Prop := ∃ P, FilS d P ∧ Q = pushS P

lemma InFil.mono {d e : ℕ} {Q : CarrierRing} (h : InFil d Q) (he : d ≤ e) : InFil e Q := by
  obtain ⟨P, hP, rfl⟩ := h; exact ⟨P, hP.mono he, rfl⟩

lemma InFil.mul {d e : ℕ} {Q R : CarrierRing} (hQ : InFil d Q) (hR : InFil e R) :
    InFil (d + e) (Q * R) := by
  obtain ⟨P, hP, rfl⟩ := hQ; obtain ⟨P', hP', rfl⟩ := hR
  exact ⟨P * P', hP.mul hP', by rw [map_mul]⟩

lemma InFil.sub {d : ℕ} {Q R : CarrierRing} (hQ : InFil d Q) (hR : InFil d R) : InFil d (Q - R) := by
  obtain ⟨P, hP, rfl⟩ := hQ; obtain ⟨P', hP', rfl⟩ := hR
  exact ⟨P - P', hP.sub hP', by rw [map_sub]⟩

lemma InFil_cc (r : ℝ) : InFil 0 (cc r) := ⟨cc r, FilS_cc r, (pushS_cc r).symm⟩

lemma InFil_diagP (m n : ℚ) (f : ℝ) : InFil 1 (diagP m n f) := by
  refine ⟨diagP m n f, ?_, (pushS_diagP m n f).symm⟩
  have hw : FilS 1 wVar := FilS_var 2 (by simp [wtS])
  have h1 : FilS 1 (cc 2 * Polynomial.X) := by simpa using (FilS_cc 2).mul FilS_X
  have h2 : FilS 1 (cc ((2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8) * wVar) := by
    simpa using (FilS_cc _).mul hw
  have h3 : FilS 1 ((1 : CarrierRing) - cc 2 * Polynomial.X -
      cc ((2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8) * wVar) :=
    ((FilS_one.mono (Nat.zero_le 1)).sub h1).sub h2
  have h4 : FilS 1 (cc ((2 * f + 1) * f * (f + 1)) * ((1 : CarrierRing) - cc 2 * Polynomial.X -
      cc ((2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8) * wVar)) := by
    simpa using (FilS_cc _).mul h3
  exact h4.sub ((FilS_cc _).mono (Nat.zero_le 1))

lemma InFil_eta2P (f : ℝ) : InFil 2 (eta2P f) := by
  refine ⟨eta2S f, ?_, (pushS_eta2S f).symm⟩
  have h1 : FilS 2 sVar1 := FilS_var 0 (by simp [wtS])
  have h2 : FilS 2 sVar2 := FilS_var 1 (by simp [wtS])
  have h3 : FilS 2 (cc (f ^ 2 / 4) * sVar1) := by simpa using (FilS_cc _).mul h1
  have h4 : FilS 2 (cc (f ^ 4 / 16) * sVar2) := by simpa using (FilS_cc _).mul h2
  unfold eta2S
  exact (((FilS_one.mono (Nat.zero_le 2)).sub h3)).add h4

lemma InFil_pt0 (m n : ℚ) : InFil 0 (pt0 m n) := InFil_cc _

lemma InFil_pt1 (m n : ℚ) : InFil 1 (pt1 m n) := by
  unfold pt1
  split_ifs
  · refine ⟨1 - cc 2 * Polynomial.X - cc (1 / 8) * wVar, ?_, ?_⟩
    · have hw : FilS 1 wVar := FilS_var 2 (by simp [wtS])
      have h1 : FilS 1 (cc 2 * Polynomial.X) := by simpa using (FilS_cc 2).mul FilS_X
      have h2 : FilS 1 (cc (1 / 8) * wVar) := by simpa using (FilS_cc _).mul hw
      exact ((FilS_one.mono (Nat.zero_le 1)).sub h1).sub h2
    · simp [pushS_cc, pushS_X, pushS_wVar]
  · simpa using ((InFil_cc _).mul (InFil_diagP m n (m : ℝ))).mul (InFil_pt0 m n)

/-- **The weight bound** (`lem:evendeformation6j`, degree bound): `P̃_{m+d}` lies in the weight-`d`
filtration, for all `m, n`. -/
theorem ptPoly_inFil (m n : ℚ) (d : ℕ) : InFil d (ptPoly m n d) := by
  have key : ∀ d, InFil d (ptPoly m n d) ∧ InFil (d + 1) (ptPoly m n (d + 1)) := by
    intro d
    induction d with
    | zero => exact ⟨InFil_pt0 m n, InFil_pt1 m n⟩
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      show InFil (d + 2) (ptPoly m n (d + 2))
      unfold ptPoly
      have h1 := ((InFil_diagP m n ((m : ℝ) + d + 1)).mul ih.2)
      have h2 := (((InFil_cc ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1))).mul
        (InFil_eta2P ((m : ℝ) + d + 1))).mul ih.1)
      have h3 := h1.sub (h2.mono (by omega : 0 + 2 + d ≤ 1 + (d + 1)))
      have h4 := (InFil_cc (1 / (((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1)))).mul h3
      exact h4.mono (by omega)
  exact (key d).1

/-! ### The coefficient form: degree `≤ j` in `ε²`, denominator `(1-δ²)^j` -/

open Polynomial in
/-- The coefficient form of a filtered polynomial coefficient: if every monomial `s₁^a s₂^b w^c` of `c`
has weight `2a+2b+c ≤ j`, then at `s₁ = 8ε²(1+δ²)/(1-δ²)²`, `s₂ = 16ε⁴/(1-δ²)²`, `w = 4ε²/(1-δ²)`,
`c = ∑_{s ≤ j} ε^{2s} M_s(δ²)/(1-δ²)^j` for polynomials `M_s ∈ ℝ[X]` independent of `ε, δ`. -/
theorem coeff_form_aux (c : MvPolynomial (Fin 3) ℝ) (j : ℕ) (hc : ∀ s, c.coeff s ≠ 0 → wtS s ≤ j) :
    ∃ M : ℕ → ℝ[X], ∀ ε δ : ℝ, δ ^ 2 ≠ 1 →
      MvPolynomial.eval ![8 * ε ^ 2 * (1 + δ ^ 2) / (1 - δ ^ 2) ^ 2, 16 * ε ^ 4 / (1 - δ ^ 2) ^ 2,
          4 * ε ^ 2 / (1 - δ ^ 2)] c =
        ∑ s ∈ Finset.range (j + 1), ε ^ (2 * s) * (M s).eval (δ ^ 2) / (1 - δ ^ 2) ^ j := by
  classical
  refine ⟨fun s => ∑ t ∈ c.support,
    if t 0 + 2 * t 1 + t 2 = s then
      Polynomial.C (c.coeff t * 8 ^ (t 0) * 16 ^ (t 1) * 4 ^ (t 2)) * (1 + Polynomial.X) ^ (t 0) *
        (1 - Polynomial.X) ^ (j - (2 * t 0 + 2 * t 1 + t 2))
    else 0, fun ε δ hδ => ?_⟩
  have hD : (1 - δ ^ 2) ≠ 0 := fun h => hδ (by linarith)
  rw [MvPolynomial.eval_eq' ]
  simp only [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  simp_rw [Polynomial.eval_finsetSum, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hw := hc t (MvPolynomial.mem_support_iff.mp ht)
  simp only [wtS] at hw
  have hs : t 0 + 2 * t 1 + t 2 < j + 1 := by omega
  rw [Finset.sum_eq_single (t 0 + 2 * t 1 + t 2)]
  · simp only [ite_true, eval_mul, eval_C, eval_pow, eval_add, eval_sub, eval_one, eval_X]
    obtain ⟨e, he⟩ : ∃ e, j = e + (2 * t 0 + 2 * t 1 + t 2) := ⟨j - (2 * t 0 + 2 * t 1 + t 2), by omega⟩
    have hj : j - (2 * t 0 + 2 * t 1 + t 2) = e := by omega
    rw [hj, he, pow_add]
    have e1 : ε ^ (2 * (t 0 + 2 * t 1 + t 2)) = (ε ^ 2) ^ (t 0) * (ε ^ 4) ^ (t 1) * (ε ^ 2) ^ (t 2) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    have e2 : (1 - δ ^ 2) ^ (2 * t 0 + 2 * t 1 + t 2) =
        ((1 - δ ^ 2) ^ 2) ^ (t 0) * ((1 - δ ^ 2) ^ 2) ^ (t 1) * (1 - δ ^ 2) ^ (t 2) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e1, e2]
    field_simp
    simp only [mul_pow, div_pow]
    field_simp
  · intro s _ hne
    simp [Ne.symm hne]
  · intro hn; exact absurd (Finset.mem_range.mpr hs) hn

open Polynomial in
/-- **The degree bound of `lem:evendeformation6j`** for a carrier-type polynomial `Q` of weight `d`
(`InFil d Q`): the coefficient of `ς^{d-j}` at `(u,v,w) = (4ε²/(1+δ)², 4ε²/(1-δ)², 4ε²/(1-δ²))` is
`∑_{s ≤ j} ε^{2s} M_s(δ²)/(1-δ²)^j`: a polynomial of degree at most `j` in `ε²` whose coefficients are
polynomials in `δ²` divided by `(1-δ²)^j`. -/
theorem coeff_form (Q : CarrierRing) (d : ℕ) (hQ : InFil d Q) (j : ℕ) (hj : j ≤ d) :
    ∃ M : ℕ → ℝ[X], ∀ ε δ : ℝ, δ ^ 2 ≠ 1 →
      MvPolynomial.eval ![4 * ε ^ 2 / (1 + δ) ^ 2, 4 * ε ^ 2 / (1 - δ) ^ 2,
          4 * ε ^ 2 / (1 - δ ^ 2)] (Q.coeff (d - j)) =
        ∑ s ∈ Finset.range (j + 1), ε ^ (2 * s) * (M s).eval (δ ^ 2) / (1 - δ ^ 2) ^ j := by
  obtain ⟨P, hP, rfl⟩ := hQ
  obtain ⟨M, hM⟩ := coeff_form_aux (P.coeff (d - j)) j (fun s hs => by
    have := hP (d - j) s hs; omega)
  refine ⟨M, fun ε δ hδ => ?_⟩
  rw [← hM ε δ hδ]
  have h1 : (1 + δ) ≠ 0 := fun h => hδ (by nlinarith)
  have h2 : (1 - δ) ≠ 0 := fun h => hδ (by nlinarith)
  have h3 : (1 - δ ^ 2) ≠ 0 := fun h => hδ (by linarith)
  have e1 : 4 * ε ^ 2 / (1 + δ) ^ 2 + 4 * ε ^ 2 / (1 - δ) ^ 2 =
      8 * ε ^ 2 * (1 + δ ^ 2) / (1 - δ ^ 2) ^ 2 := by
    field_simp; ring
  have e2 : 4 * ε ^ 2 / (1 + δ) ^ 2 * (4 * ε ^ 2 / (1 - δ) ^ 2) =
      16 * ε ^ 4 / (1 - δ ^ 2) ^ 2 := by
    field_simp; ring
  have hc : (pushS P).coeff (d - j) = phiS (P.coeff (d - j)) := Polynomial.coeff_map _ _
  rw [hc, eval_phiS, e1, e2]

/-- The even Racah deformation `q_d(ς; ε, δ)` of the paper at `S = ε⁻¹`: the polynomial `Q` evaluated at
`(u,v,w) = (A⁻², B⁻², (AB)⁻¹)` with `A = S(1+δ)/2`, `B = S(1-δ)/2`. -/
noncomputable def shapeEval (Q : CarrierRing) (τ ε δ : ℝ) : ℝ :=
  evalC τ (4 * ε ^ 2 / (1 + δ) ^ 2) (4 * ε ^ 2 / (1 - δ) ^ 2) (4 * ε ^ 2 / (1 - δ ^ 2)) Q

/-- For `A, B > 0`, `S = A + B`, `ε = 1/S`, `δ = (A-B)/S`: `q_d(ς; ε, δ)` is `q_d` at
`(A⁻², B⁻², (AB)⁻¹)`. -/
theorem shapeEval_eq_AB (Q : CarrierRing) (τ A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    shapeEval Q τ (1 / (A + B)) ((A - B) / (A + B)) =
      evalC τ (1 / A ^ 2) (1 / B ^ 2) (1 / (A * B)) Q := by
  unfold shapeEval
  have hS : 0 < A + B := by linarith
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hS' := hS.ne'
  have f1 : 1 + (A - B) / (A + B) = 2 * A / (A + B) := by field_simp; ring
  have f2 : 1 - (A - B) / (A + B) = 2 * B / (A + B) := by field_simp; ring
  have f3 : 1 - ((A - B) / (A + B)) ^ 2 = 4 * A * B / (A + B) ^ 2 := by field_simp; ring
  have e1 : 4 * (1 / (A + B)) ^ 2 / (1 + (A - B) / (A + B)) ^ 2 = 1 / A ^ 2 := by
    rw [f1]; field_simp; norm_num
  have e2 : 4 * (1 / (A + B)) ^ 2 / (1 - (A - B) / (A + B)) ^ 2 = 1 / B ^ 2 := by
    rw [f2]; field_simp; norm_num
  have e3 : 4 * (1 / (A + B)) ^ 2 / (1 - ((A - B) / (A + B)) ^ 2) = 1 / (A * B) := by
    rw [f3]; field_simp
  rw [e1, e2, e3]

/-! ### The estimate `eq:evendeformationbound` -/

lemma mv_sub_const_le (c : MvPolynomial (Fin 3) ℝ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin 3 → ℝ) (r : ℝ), 0 ≤ r → r ≤ K → (∀ i, 0 ≤ x i ∧ x i ≤ r) →
      |MvPolynomial.eval x c - MvPolynomial.eval ![0, 0, 0] c| ≤ C * r := by
  induction c using MvPolynomial.induction_on with
  | C a => exact ⟨0, le_rfl, fun x r hr _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, h1, hC1⟩ := hp
    obtain ⟨C2, h2, hC2⟩ := hq
    refine ⟨C1 + C2, add_nonneg h1 h2, fun x r hr hrK hx => ?_⟩
    have a1 := hC1 x r hr hrK hx
    have a2 := hC2 x r hr hrK hx
    simp only [map_add]
    calc |MvPolynomial.eval x p + MvPolynomial.eval x q -
          (MvPolynomial.eval ![0, 0, 0] p + MvPolynomial.eval ![0, 0, 0] q)|
        = |(MvPolynomial.eval x p - MvPolynomial.eval ![0, 0, 0] p) +
          (MvPolynomial.eval x q - MvPolynomial.eval ![0, 0, 0] q)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ C1 * r + C2 * r := add_le_add a1 a2
      _ = _ := by ring
  | mul_X p i hp =>
    obtain ⟨C1, h1, hC1⟩ := hp
    refine ⟨|MvPolynomial.eval ![0, 0, 0] p| + C1 * K, by positivity, fun x r hr hrK hx => ?_⟩
    have a1 := hC1 x r hr hrK hx
    have h0 : MvPolynomial.eval ![0, 0, 0] (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ) = 0 := by
      fin_cases i <;> simp
    simp only [map_mul, MvPolynomial.eval_X, h0, mul_zero, sub_zero]
    have b1 : |MvPolynomial.eval x p| ≤ |MvPolynomial.eval ![0, 0, 0] p| + C1 * K := by
      have : |MvPolynomial.eval x p| ≤ |MvPolynomial.eval ![0, 0, 0] p| +
          |MvPolynomial.eval x p - MvPolynomial.eval ![0, 0, 0] p| := by
        calc |MvPolynomial.eval x p| = |MvPolynomial.eval ![0, 0, 0] p +
              (MvPolynomial.eval x p - MvPolynomial.eval ![0, 0, 0] p)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have : C1 * r ≤ C1 * K := mul_le_mul_of_nonneg_left hrK h1
      linarith
    rw [abs_mul, abs_of_nonneg (hx i).1]
    calc |MvPolynomial.eval x p| * x i ≤ (|MvPolynomial.eval ![0, 0, 0] p| + C1 * K) * r :=
          mul_le_mul b1 (hx i).2 (hx i).1 (by positivity)
      _ = _ := by ring

lemma evalC_sub_zero_le (Q : CarrierRing) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ u v w r : ℝ), 0 ≤ τ → τ ≤ 1 → 0 ≤ r → r ≤ K → 0 ≤ u → u ≤ r → 0 ≤ v →
      v ≤ r → 0 ≤ w → w ≤ r → |evalC τ u v w Q - evalC τ 0 0 0 Q| ≤ C * r := by
  choose Cf hC0 hCf using fun i => mv_sub_const_le (Q.coeff i) K hK
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), Cf i,
    Finset.sum_nonneg fun i _ => hC0 i, fun τ u v w r hτ0 hτ1 hr hrK hu0 hu1 hv0 hv1 hw0 hw1 => ?_⟩
  have hx : ∀ i, 0 ≤ (![u, v, w] : Fin 3 → ℝ) i ∧ (![u, v, w] : Fin 3 → ℝ) i ≤ r := by
    intro i; fin_cases i <;> simp [hu0, hu1, hv0, hv1, hw0, hw1]
  have e : ∀ a b c : ℝ, evalC τ a b c Q =
      ∑ i ∈ Finset.range (Q.natDegree + 1), MvPolynomial.eval ![a, b, c] (Q.coeff i) * τ ^ i := by
    intro a b c
    unfold evalC
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  rw [e, e, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul, abs_of_nonneg (pow_nonneg hτ0 i)]
  have := hCf i ![u, v, w] r hr hrK hx
  calc |MvPolynomial.eval ![u, v, w] (Q.coeff i) - MvPolynomial.eval ![0, 0, 0] (Q.coeff i)| * τ ^ i
      ≤ (Cf i * r) * 1 := mul_le_mul this (pow_le_one₀ hτ0 hτ1) (pow_nonneg hτ0 i)
        (mul_nonneg (hC0 i) hr)
    _ = _ := by ring

/-- **`eq:evendeformationbound`** (`lem:evendeformation6j`), every chamber.  For `p = |m-n|`, `q = |m+n|`,
`d`, and `0 ≤ δ₀ < 1`, there is `C` with
`|q_d(ς; ε, δ) - P̂_d^{(p,q)}(ς)| ≤ C ε²` for all `0 < ε ≤ 1`, `|δ| ≤ δ₀`, `0 ≤ ς ≤ 1`
(`q_d = evenRacah6All m n d`, `P̂ = jacobiMonicTau`).  In the paper's variables `ε = (A+B)⁻¹`,
`δ = (A-B)/(A+B)` (`shapeEval_eq_AB`). -/
theorem evenRacah6All_bound (m n : ℚ) (p q : ℕ) (hp : |m - n| = p) (hq : |m + n| = q) (d : ℕ)
    (δ₀ : ℝ) (h0 : 0 ≤ δ₀) (h1 : δ₀ < 1) :
    ∃ C : ℝ, ∀ ε δ τ : ℝ, 0 < ε → ε ≤ 1 → |δ| ≤ δ₀ → 0 ≤ τ → τ ≤ 1 →
      |shapeEval (evenRacah6All m n d) τ ε δ - (jacobiMonicTau p q d).eval τ| ≤ C * ε ^ 2 := by
  have hz : ∀ τ : ℝ, evalC τ 0 0 0 (evenRacah6All m n d) = (jacobiMonicTau p q d).eval τ := by
    intro τ
    obtain ⟨h1', h2'⟩ := chamber_labels m n p q hp hq
    have := (lem_evendeformation6 (chamberM m n) (chamberN m n) p q h1' h2'
      (abs_chamberN_le m n) d).2.2.1
    unfold evenRacah6All
    rw [← this]
    unfold evalC
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval_map]
  set K : ℝ := 4 / (1 - δ₀) ^ 2 with hK
  have hd0 : 0 < 1 - δ₀ := by linarith
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨C0, hC0, hC⟩ := evalC_sub_zero_le (evenRacah6All m n d) K hK0
  refine ⟨C0 * K, fun ε δ τ hε hε1 hδ hτ0 hτ1 => ?_⟩
  obtain ⟨hδ1, hδ2⟩ := abs_le.mp hδ
  have hp1 : 0 < 1 + δ := by linarith
  have hp2 : 0 < 1 - δ := by linarith
  have hp3 : 0 < 1 - δ ^ 2 := by nlinarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε2' : ε ^ 2 ≤ 1 := by nlinarith
  have hb : 4 * ε ^ 2 / (1 - δ₀) ^ 2 = K * ε ^ 2 := by rw [hK]; ring
  have hle : ∀ y : ℝ, (1 - δ₀) ^ 2 ≤ y → 4 * ε ^ 2 / y ≤ K * ε ^ 2 := by
    intro y hy
    rw [← hb]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hy
  have hu := hle ((1 + δ) ^ 2) (by nlinarith)
  have hv := hle ((1 - δ) ^ 2) (by nlinarith)
  have hw := hle (1 - δ ^ 2) (by nlinarith)
  have := hC τ _ _ _ (K * ε ^ 2) hτ0 hτ1 (by positivity)
    (by nlinarith) (by positivity) hu (by positivity) hv (by positivity) hw
  unfold shapeEval
  rw [← hz τ]
  calc _ ≤ C0 * (K * ε ^ 2) := this
    _ = _ := by ring

lemma evenRacah6All_inFil (m n : ℚ) (d : ℕ) : InFil d (evenRacah6All m n d) := by
  unfold evenRacah6All evenRacah6
  simpa using (InFil_cc _).mul (ptPoly_inFil (chamberM m n) (chamberN m n) d)

open Polynomial in
/-- **`lem:evendeformation6j`, degree and denominator bound** (every chamber): the coefficient of
`ς^{d-j}` of `q_d = evenRacah6All m n d` (`j ≤ d`) at `ε = S⁻¹`, `δ = (A-B)/S` is
`∑_{s ≤ j} ε^{2s} M_s(δ²) / (1-δ²)^j`, i.e. a polynomial of degree at most `j` in `ε²` whose coefficients are
polynomials in `δ²` over `(1-δ²)^j` (`M_s ∈ ℝ[X]` independent of `ε, δ`). -/
theorem evenRacah6All_coeff_form (m n : ℚ) (d j : ℕ) (hj : j ≤ d) :
    ∃ M : ℕ → ℝ[X], ∀ ε δ : ℝ, δ ^ 2 ≠ 1 →
      MvPolynomial.eval ![4 * ε ^ 2 / (1 + δ) ^ 2, 4 * ε ^ 2 / (1 - δ) ^ 2,
          4 * ε ^ 2 / (1 - δ ^ 2)] ((evenRacah6All m n d).coeff (d - j)) =
        ∑ s ∈ Finset.range (j + 1), ε ^ (2 * s) * (M s).eval (δ ^ 2) / (1 - δ ^ 2) ^ j :=
  coeff_form _ d (evenRacah6All_inFil m n d) j hj

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.ptPoly_inFil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.ptPoly_inFil

/-- info: 'FormalResearch.Racah.evenRacah6All_coeff_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.evenRacah6All_coeff_form

/-- info: 'FormalResearch.Racah.evenRacah6All_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.evenRacah6All_bound


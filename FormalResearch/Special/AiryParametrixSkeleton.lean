module

public import FormalResearch.Special.AiryParametrixTaylor

/-!
# Parametrix defect, part 3: the parity skeleton

The exact shift identity (`AiryShift`) writes the parametrix defect as `Ai · 𝔄 + Ai' · 𝔅` with
`𝔄 = G₊ C(s₊) + G₋ C(s₋) - c g`, `𝔅 = G₊ S(s₊) + G₋ S(s₋)`, where `s± = (ζ(q±h) - ζ(q))/h = ±ζ' + hζ''/2 + O(h²)`
and `G± = A(q ± h/2) g(q ± h) = G₀ ± h G₁ + O(h²)`.  After the rescaling `Δ = h^{1/3} s`, `X = h^{-2/3} ζ`, the
Taylor polynomials of `C`, `S` become `e(s) + h o(s)` (`e` even, `o` odd; `C`) and `a(s) + h b(s)` (`a` odd, `b`
even; `S/h^{1/3}`) with `ζ` entering only as a parameter, and the cancellation of the orders `h⁰` and `h¹` is
*pure parity*: the two links are exchanged by `s ↦ -s`.  This file proves that statement for abstract
functions `e, o` (resp. `a, b`) with bounded derivatives, with explicit constants:

* `sk_even_odd`: `|G₊(e(s₊) + h o(s₊)) + G₋(e(s₋) + h o(s₋)) - 2 G₀ e(ζ')| ≤ K h²`;
* `sk_odd_even`: `|G₊(a(s₊) + h b(s₊)) + G₋(a(s₋) + h b(s₋)) - h T| ≤ K h²` with
  `T = G₀ ζ'' a'(ζ') + 2 G₁ a(ζ') + 2 G₀ b(ζ')`.

The functions enter only through explicit bounds on `|e|, |e'|, |e''|, |o|, |o'|` on `[-S, S]`, so the same
statement serves the polynomial truncations of the window lemma (`AiryParametrixDefect`) and, with the exact
`Ch(ζσ²)`, `σ Sh(ζσ²)`, a future uniform version.  Proved; no asymptotic input.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- First-order estimate on `[-S, S]`. -/
lemma sk_t1 {f f1 : ℝ → ℝ} {S M : ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hM : ∀ x, |x| ≤ S → |f1 x| ≤ M) {x y : ℝ} (hx : |x| ≤ S) (hy : |y| ≤ S) :
    |f y - f x| ≤ M * |y - x| := by
  have hsub : uIcc x y ⊆ Icc (-S) S :=
    uIcc_subset_Icc ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f1) (C := M) (x := x) (y := y)
    (fun z _ => (hf z).hasDerivWithinAt)
    (fun z hz => by
      have := hsub hz
      exact hM z (abs_le.2 ⟨this.1, this.2⟩)) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-- Second-order estimate on `[-S, S]`: `|f(x+d) - f(x) - f'(x) d| ≤ M d²`. -/
lemma sk_t2 {f f1 f2 : ℝ → ℝ} {S M : ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hM : ∀ x, |x| ≤ S → |f2 x| ≤ M) {x d : ℝ}
    (hx : |x| ≤ S) (hxd : |x + d| ≤ S) : |f (x + d) - f x - f1 x * d| ≤ M * d ^ 2 := by
  have hsub : uIcc x (x + d) ⊆ Icc (-S) S :=
    uIcc_subset_Icc ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      ⟨by linarith [neg_abs_le (x + d)], by linarith [le_abs_self (x + d)]⟩
  set g : ℝ → ℝ := fun y => f y - f1 x * y with hg
  have hgd : ∀ y, HasDerivAt g (f1 y - f1 x) y := fun y => by
    have := (hf y).fun_sub ((hasDerivAt_id y).const_mul (f1 x))
    simpa [hg] using this
  have hb : ∀ y ∈ uIcc x (x + d), |f1 y - f1 x| ≤ M * |d| := by
    intro y hy
    have hyS : |y| ≤ S := abs_le.2 ⟨(hsub hy).1, (hsub hy).2⟩
    have h1 := sk_t1 hf1 hM hx hyS
    have h2 : |y - x| ≤ |d| := by
      rcases le_total 0 d with hd | hd
      · rw [uIcc_of_le (by linarith)] at hy
        rw [abs_of_nonneg (by linarith [hy.1]), abs_of_nonneg hd]; linarith [hy.2]
      · rw [uIcc_of_ge (by linarith)] at hy
        rw [abs_of_nonpos (by linarith [hy.2]), abs_of_nonpos hd]; linarith [hy.1]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
    calc |f1 y - f1 x| ≤ M * |y - x| := h1
      _ ≤ M * |d| := mul_le_mul_of_nonneg_left h2 hM0
  have := (convex_uIcc x (x + d)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun y => f1 y - f1 x) (C := M * |d|) (x := x) (y := x + d)
    (fun z _ => (hgd z).hasDerivWithinAt) (fun z hz => by simpa [Real.norm_eq_abs] using hb z hz)
    left_mem_uIcc right_mem_uIcc
  simp only [hg, Real.norm_eq_abs, add_sub_cancel_left] at this
  have e : f (x + d) - f1 x * (x + d) - (f x - f1 x * x) = f (x + d) - f x - f1 x * d := by ring
  rw [e] at this
  calc |f (x + d) - f x - f1 x * d| ≤ M * |d| * |d| := this
    _ = M * d ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Parity skeleton for `𝔄`** (even part `e`, odd part `o`; all bounds on `[-S, S]`). -/
theorem sk_even_odd {e e1 e2 o o1 : ℝ → ℝ} {S E0 M1 M2 N0 N1 : ℝ}
    (he : ∀ x, HasDerivAt e (e1 x) x) (he1 : ∀ x, HasDerivAt e1 (e2 x) x)
    (ho : ∀ x, HasDerivAt o (o1 x) x)
    (hepar : ∀ x, e (-x) = e x) (hopar : ∀ x, o (-x) = -o x)
    (hE0 : ∀ x, |x| ≤ S → |e x| ≤ E0) (hM1 : ∀ x, |x| ≤ S → |e1 x| ≤ M1)
    (hM2 : ∀ x, |x| ≤ S → |e2 x| ≤ M2) (hN0 : ∀ x, |x| ≤ S → |o x| ≤ N0)
    (hN1 : ∀ x, |x| ≤ S → |o1 x| ≤ N1)
    {h z1 z2 G0 G1 ep em gp gm B Ee Γ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hz2 : |z2| ≤ B) (hG0 : |G0| ≤ B) (hG1 : |G1| ≤ B)
    (hep : |ep| ≤ Ee * h ^ 2) (hem : |em| ≤ Ee * h ^ 2)
    (hgp : |gp| ≤ Γ * h ^ 2) (hgm : |gm| ≤ Γ * h ^ 2)
    (hsp : |z1 + h * z2 / 2 + ep| ≤ S) (hsm : |-z1 + h * z2 / 2 + em| ≤ S) (hz1S : |z1| ≤ S) :
    |(G0 + h * G1 + gp) * (e (z1 + h * z2 / 2 + ep) + h * o (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (e (-z1 + h * z2 / 2 + em) + h * o (-z1 + h * z2 / 2 + em)) -
        2 * G0 * e z1| ≤
      (B * (2 * M1 * Ee + 2 * M2 * (B / 2 + Ee) ^ 2) + B * M1 * (B + 2 * Ee) + 2 * Γ * E0 +
        B * N1 * (B + 2 * Ee) + 2 * B * N0 + 2 * Γ * N0) * h ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hz2
  have hEe : 0 ≤ Ee := by
    by_contra hneg
    have := (abs_nonneg ep).trans hep
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith
  have hΓ : 0 ≤ Γ := by
    by_contra hneg
    have := (abs_nonneg gp).trans hgp
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith
  -- the two points
  set dp : ℝ := h * z2 / 2 + ep with hdp
  set dm : ℝ := -(h * z2 / 2 + em) with hdm
  set P : ℝ := z1 + dp with hP
  set Q : ℝ := z1 + dm with hQ
  have hP' : z1 + h * z2 / 2 + ep = P := by simp [hP, hdp]; ring
  have hQ' : -z1 + h * z2 / 2 + em = -Q := by simp [hQ, hdm]; ring
  rw [hP'] at hsp ⊢
  rw [hQ'] at hsm ⊢
  have hPS : |P| ≤ S := hsp
  have hQS : |Q| ≤ S := by rw [← abs_neg]; exact hsm
  rw [hepar Q, hopar Q]
  -- size of the increments
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hdp_b : |dp| ≤ h * (B / 2 + Ee) := by
    calc |dp| ≤ |h * z2 / 2| + |ep| := abs_add_le _ _
      _ ≤ h * (B / 2) + Ee * h ^ 2 := by
          have : |h * z2 / 2| = h * |z2| / 2 := by
            rw [abs_div, abs_mul, abs_of_pos hh0]; norm_num
          rw [this]; have := mul_le_mul_of_nonneg_left hz2 hh0.le; linarith
      _ ≤ h * (B / 2 + Ee) := by nlinarith
  have hdm_b : |dm| ≤ h * (B / 2 + Ee) := by
    calc |dm| = |h * z2 / 2 + em| := by rw [hdm, abs_neg]
      _ ≤ |h * z2 / 2| + |em| := abs_add_le _ _
      _ ≤ h * (B / 2) + Ee * h ^ 2 := by
          have : |h * z2 / 2| = h * |z2| / 2 := by
            rw [abs_div, abs_mul, abs_of_pos hh0]; norm_num
          rw [this]; have := mul_le_mul_of_nonneg_left hz2 hh0.le; linarith
      _ ≤ h * (B / 2 + Ee) := by nlinarith
  have hdiff : |dp - dm| ≤ h * (B + 2 * Ee) := by
    have : dp - dm = h * z2 + ep + em := by simp [hdp, hdm]; ring
    rw [this]
    calc |h * z2 + ep + em| ≤ |h * z2| + |ep| + |em| := by
          calc _ ≤ |h * z2 + ep| + |em| := abs_add_le _ _
            _ ≤ _ := by linarith [abs_add_le (h * z2) ep]
      _ ≤ h * B + Ee * h ^ 2 + Ee * h ^ 2 := by
          rw [abs_mul, abs_of_pos hh0]
          have := mul_le_mul_of_nonneg_left hz2 hh0.le
          linarith
      _ ≤ h * (B + 2 * Ee) := by nlinarith
  have hsum : |dp + dm| ≤ 2 * Ee * h ^ 2 := by
    have : dp + dm = ep - em := by simp [hdp, hdm]; ring
    rw [this]
    calc |ep - em| ≤ |ep| + |em| := abs_sub _ _
      _ ≤ 2 * Ee * h ^ 2 := by linarith
  -- Taylor expansions
  have hPe : |e P - e z1 - e1 z1 * dp| ≤ M2 * dp ^ 2 := by
    have := sk_t2 he he1 hM2 hz1S (d := dp) (by rwa [← hP])
    simpa [hP] using this
  have hQe : |e Q - e z1 - e1 z1 * dm| ≤ M2 * dm ^ 2 := by
    have := sk_t2 he he1 hM2 hz1S (d := dm) (by rwa [← hQ])
    simpa [hQ] using this
  have hdp2 : dp ^ 2 ≤ (h * (B / 2 + Ee)) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hdp_b]) (abs_le.1 hdp_b).2
    exact this
  have hdm2 : dm ^ 2 ≤ (h * (B / 2 + Ee)) ^ 2 := by
    exact sq_le_sq' (by linarith [abs_le.1 hdm_b]) (abs_le.1 hdm_b).2
  have hM20 : 0 ≤ M2 := (abs_nonneg _).trans (hM2 z1 hz1S)
  have hM10 : 0 ≤ M1 := (abs_nonneg _).trans (hM1 z1 hz1S)
  have hN00 : 0 ≤ N0 := (abs_nonneg _).trans (hN0 z1 hz1S)
  have hE00 : 0 ≤ E0 := (abs_nonneg _).trans (hE0 z1 hz1S)
  have hN10 : 0 ≤ N1 := (abs_nonneg _).trans (hN1 z1 hz1S)
  have hRp : |e P - e z1 - e1 z1 * dp| ≤ M2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by
    calc _ ≤ M2 * dp ^ 2 := hPe
      _ ≤ M2 * (h * (B / 2 + Ee)) ^ 2 := mul_le_mul_of_nonneg_left hdp2 hM20
      _ = M2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by ring
  have hRm : |e Q - e z1 - e1 z1 * dm| ≤ M2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by
    calc _ ≤ M2 * dm ^ 2 := hQe
      _ ≤ M2 * (h * (B / 2 + Ee)) ^ 2 := mul_le_mul_of_nonneg_left hdm2 hM20
      _ = M2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by ring
  -- differences of values at P and Q
  have hPQ : P - Q = dp - dm := by simp [hP, hQ]
  have heD : |e P - e Q| ≤ M1 * (h * (B + 2 * Ee)) := by
    have := sk_t1 he hM1 hQS hPS
    rw [hPQ] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdiff hM10)
  have hoD : |o P - o Q| ≤ N1 * (h * (B + 2 * Ee)) := by
    have := sk_t1 ho hN1 hQS hPS
    rw [hPQ] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdiff hN10)
  have heP := hE0 P hPS
  have heQ := hE0 Q hQS
  have hoP := hN0 P hPS
  have hoQ := hN0 Q hQS
  have he1z := hM1 z1 hz1S
  -- algebra
  have key : (G0 + h * G1 + gp) * (e P + h * o P) + (G0 - h * G1 + gm) * (e Q + h * -o Q) -
        2 * G0 * e z1 =
      G0 * (e1 z1 * (dp + dm) + (e P - e z1 - e1 z1 * dp) + (e Q - e z1 - e1 z1 * dm)) +
      h * G1 * (e P - e Q) + gp * e P + gm * e Q + h * G0 * (o P - o Q) +
      h ^ 2 * G1 * (o P + o Q) + h * gp * o P - h * gm * o Q := by ring
  rw [key]
  have t1 : |G0 * (e1 z1 * (dp + dm) + (e P - e z1 - e1 z1 * dp) + (e Q - e z1 - e1 z1 * dm))| ≤
      B * (2 * M1 * Ee + 2 * M2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
    rw [abs_mul]
    have : |e1 z1 * (dp + dm) + (e P - e z1 - e1 z1 * dp) + (e Q - e z1 - e1 z1 * dm)| ≤
        (2 * M1 * Ee + 2 * M2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
      calc _ ≤ |e1 z1 * (dp + dm)| + |e P - e z1 - e1 z1 * dp| + |e Q - e z1 - e1 z1 * dm| := by
            calc _ ≤ |e1 z1 * (dp + dm) + (e P - e z1 - e1 z1 * dp)| + _ := abs_add_le _ _
              _ ≤ _ := by linarith [abs_add_le (e1 z1 * (dp + dm)) (e P - e z1 - e1 z1 * dp)]
        _ ≤ M1 * (2 * Ee * h ^ 2) + M2 * (B / 2 + Ee) ^ 2 * h ^ 2 + M2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by
            rw [abs_mul]
            have := mul_le_mul he1z hsum (abs_nonneg _) hM10
            linarith
        _ = _ := by ring
    calc |G0| * _ ≤ B * ((2 * M1 * Ee + 2 * M2 * (B / 2 + Ee) ^ 2) * h ^ 2) :=
          mul_le_mul hG0 this (abs_nonneg _) hB0
      _ = _ := by ring
  have hBE : 0 ≤ B + 2 * Ee := by positivity
  have t2 : |h * G1 * (e P - e Q)| ≤ B * M1 * (B + 2 * Ee) * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have := mul_le_mul_of_nonneg_left heD (mul_nonneg hh0.le (abs_nonneg G1))
    calc h * |G1| * |e P - e Q| ≤ h * |G1| * (M1 * (h * (B + 2 * Ee))) := this
      _ = |G1| * (M1 * (B + 2 * Ee) * h ^ 2) := by ring
      _ ≤ B * (M1 * (B + 2 * Ee) * h ^ 2) := mul_le_mul_of_nonneg_right hG1 (by positivity)
      _ = _ := by ring
  have t3 : |gp * e P| ≤ Γ * E0 * h ^ 2 := by
    rw [abs_mul]
    calc |gp| * |e P| ≤ (Γ * h ^ 2) * E0 := mul_le_mul hgp heP (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t4 : |gm * e Q| ≤ Γ * E0 * h ^ 2 := by
    rw [abs_mul]
    calc |gm| * |e Q| ≤ (Γ * h ^ 2) * E0 := mul_le_mul hgm heQ (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t5 : |h * G0 * (o P - o Q)| ≤ B * N1 * (B + 2 * Ee) * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have := mul_le_mul_of_nonneg_left hoD (mul_nonneg hh0.le (abs_nonneg G0))
    calc h * |G0| * |o P - o Q| ≤ h * |G0| * (N1 * (h * (B + 2 * Ee))) := this
      _ = |G0| * (N1 * (B + 2 * Ee) * h ^ 2) := by ring
      _ ≤ B * (N1 * (B + 2 * Ee) * h ^ 2) := mul_le_mul_of_nonneg_right hG0 (by positivity)
      _ = _ := by ring
  have t6 : |h ^ 2 * G1 * (o P + o Q)| ≤ 2 * B * N0 * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ h ^ 2)]
    have h1 : |o P + o Q| ≤ 2 * N0 := (abs_add_le _ _).trans (by linarith)
    have := mul_le_mul hG1 h1 (abs_nonneg _) hB0
    calc h ^ 2 * |G1| * |o P + o Q| = h ^ 2 * (|G1| * |o P + o Q|) := by ring
      _ ≤ h ^ 2 * (B * (2 * N0)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * B * N0 * h ^ 2 := by ring
  have t7 : |h * gp * o P| ≤ Γ * N0 * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have := mul_le_mul hgp hoP (abs_nonneg _) (by positivity)
    calc h * |gp| * |o P| = h * (|gp| * |o P|) := by ring
      _ ≤ h * (Γ * h ^ 2 * N0) := mul_le_mul_of_nonneg_left this hh0.le
      _ ≤ 1 * (Γ * h ^ 2 * N0) := by
          apply mul_le_mul_of_nonneg_right hh1 (by positivity)
      _ = _ := by ring
  have t8 : |h * gm * o Q| ≤ Γ * N0 * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have := mul_le_mul hgm hoQ (abs_nonneg _) (by positivity)
    calc h * |gm| * |o Q| = h * (|gm| * |o Q|) := by ring
      _ ≤ h * (Γ * h ^ 2 * N0) := mul_le_mul_of_nonneg_left this hh0.le
      _ ≤ 1 * (Γ * h ^ 2 * N0) := by
          apply mul_le_mul_of_nonneg_right hh1 (by positivity)
      _ = _ := by ring
  rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 t8 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2,
    t7.1, t7.2, t8.1, t8.2]

/-- Increments of the two shifted arguments: with `dp = h z2/2 + ep`, `dm = -(h z2/2 + em)`. -/
lemma sk_incr {h z2 ep em B Ee : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hz2 : |z2| ≤ B)
    (hep : |ep| ≤ Ee * h ^ 2) (hem : |em| ≤ Ee * h ^ 2) (hEe : 0 ≤ Ee) :
    |h * z2 / 2 + ep| ≤ h * (B / 2 + Ee) ∧ |-(h * z2 / 2 + em)| ≤ h * (B / 2 + Ee) ∧
      |(h * z2 / 2 + ep) + -(h * z2 / 2 + em)| ≤ 2 * Ee * h ^ 2 := by
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hz2h : |h * z2 / 2| ≤ h * (B / 2) := by
    rw [abs_div, abs_mul, abs_of_pos hh0]
    have := mul_le_mul_of_nonneg_left hz2 hh0.le
    norm_num; linarith
  refine ⟨?_, ?_, ?_⟩
  · calc |h * z2 / 2 + ep| ≤ |h * z2 / 2| + |ep| := abs_add_le _ _
      _ ≤ h * (B / 2) + Ee * h ^ 2 := by linarith
      _ ≤ h * (B / 2 + Ee) := by nlinarith
  · calc |-(h * z2 / 2 + em)| = |h * z2 / 2 + em| := abs_neg _
      _ ≤ |h * z2 / 2| + |em| := abs_add_le _ _
      _ ≤ h * (B / 2) + Ee * h ^ 2 := by linarith
      _ ≤ h * (B / 2 + Ee) := by nlinarith
  · have : (h * z2 / 2 + ep) + -(h * z2 / 2 + em) = ep - em := by ring
    rw [this]
    calc |ep - em| ≤ |ep| + |em| := abs_sub _ _
      _ ≤ 2 * Ee * h ^ 2 := by linarith

/-- The purely real core of `sk_odd_even` (all function values are atoms). -/
lemma sk_oe_alg {h G0 G1 gp gm z2 ep em B Ee Γ A0 A1 A2 Bb Bb1 aP aQ a0 a1z bP bQ b0 dp dm : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hB0 : 0 ≤ B) (hEe : 0 ≤ Ee) (hΓ : 0 ≤ Γ) (hA10 : 0 ≤ A1)
    (hM20 : 0 ≤ A2) (_hBb10 : 0 ≤ Bb1) (hBb0 : 0 ≤ Bb)
    (hG0 : |G0| ≤ B) (hG1 : |G1| ≤ B) (hgp : |gp| ≤ Γ * h ^ 2) (hgm : |gm| ≤ Γ * h ^ 2)
    (hdp : dp = h * z2 / 2 + ep) (hdm : dm = -(h * z2 / 2 + em))
    (hsum : |ep + em| ≤ 2 * Ee * h ^ 2) (hsum' : |dp + dm| ≤ 2 * Ee * h ^ 2)
    (hRp : |aP - a0 - a1z * dp| ≤ A2 * (B / 2 + Ee) ^ 2 * h ^ 2)
    (hRm : |aQ - a0 - a1z * dm| ≤ A2 * (B / 2 + Ee) ^ 2 * h ^ 2)
    (hbP : |bP - b0| ≤ Bb1 * (h * (B / 2 + Ee))) (hbQ : |bQ - b0| ≤ Bb1 * (h * (B / 2 + Ee)))
    (haP : |aP| ≤ A0) (haQ : |aQ| ≤ A0) (hbPb : |bP| ≤ Bb) (hbQb : |bQ| ≤ Bb)
    (ha1z : |a1z| ≤ A1) :
    |(G0 + h * G1 + gp) * (aP + h * bP) + (G0 - h * G1 + gm) * (-aQ + h * bQ) -
        h * (G0 * z2 * a1z + 2 * G1 * a0 + 2 * G0 * b0)| ≤
      (2 * B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) + 2 * Γ * A0 +
        2 * B * Bb1 * (B / 2 + Ee) + 2 * B * Bb + 2 * Γ * Bb) * h ^ 2 := by
  have key : (G0 + h * G1 + gp) * (aP + h * bP) + (G0 - h * G1 + gm) * (-aQ + h * bQ) -
        h * (G0 * z2 * a1z + 2 * G1 * a0 + 2 * G0 * b0) =
      G0 * (a1z * (ep + em) + (aP - a0 - a1z * dp) - (aQ - a0 - a1z * dm)) +
      h * G1 * (a1z * (dp + dm) + (aP - a0 - a1z * dp) + (aQ - a0 - a1z * dm)) +
      (gp * aP - gm * aQ) +
      h * G0 * ((bP - b0) + (bQ - b0)) + h ^ 2 * G1 * (bP - bQ) +
      (h * gp * bP + h * gm * bQ) := by
    rw [hdp, hdm]; ring
  rw [key]
  have t1 : |G0 * (a1z * (ep + em) + (aP - a0 - a1z * dp) - (aQ - a0 - a1z * dm))| ≤
      B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
    rw [abs_mul]
    have : |a1z * (ep + em) + (aP - a0 - a1z * dp) - (aQ - a0 - a1z * dm)| ≤
        (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
      have h1 : |a1z * (ep + em)| ≤ A1 * (2 * Ee * h ^ 2) := by
        rw [abs_mul]; exact mul_le_mul ha1z hsum (abs_nonneg _) hA10
      have h2 := abs_le.1 h1
      have h3 := abs_le.1 hRp
      have h4 := abs_le.1 hRm
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
    calc |G0| * _ ≤ B * ((2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2) :=
          mul_le_mul hG0 this (abs_nonneg _) hB0
      _ = _ := by ring
  have t2 : |h * G1 * (a1z * (dp + dm) + (aP - a0 - a1z * dp) + (aQ - a0 - a1z * dm))| ≤
      B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have : |a1z * (dp + dm) + (aP - a0 - a1z * dp) + (aQ - a0 - a1z * dm)| ≤
        (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by
      have h1 : |a1z * (dp + dm)| ≤ A1 * (2 * Ee * h ^ 2) := by
        rw [abs_mul]; exact mul_le_mul ha1z hsum' (abs_nonneg _) hA10
      have h2 := abs_le.1 h1
      have h3 := abs_le.1 hRp
      have h4 := abs_le.1 hRm
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
    have hc : 0 ≤ B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2 := by positivity
    calc h * |G1| * _ ≤ h * (B * ((2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hG1 this (abs_nonneg _) hB0) hh0.le
      _ = h * (B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2) := by ring
      _ ≤ 1 * (B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) * h ^ 2) :=
          mul_le_mul_of_nonneg_right hh1 hc
      _ = _ := by ring
  have t3 : |gp * aP - gm * aQ| ≤ 2 * Γ * A0 * h ^ 2 := by
    calc |gp * aP - gm * aQ| ≤ |gp * aP| + |gm * aQ| := abs_sub _ _
      _ ≤ (Γ * h ^ 2) * A0 + (Γ * h ^ 2) * A0 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hgp haP (abs_nonneg _) (by positivity))
            (mul_le_mul hgm haQ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have t4 : |h * G0 * ((bP - b0) + (bQ - b0))| ≤ 2 * B * Bb1 * (B / 2 + Ee) * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hh0]
    have : |(bP - b0) + (bQ - b0)| ≤ 2 * (Bb1 * (h * (B / 2 + Ee))) :=
      (abs_add_le _ _).trans (by linarith)
    calc h * |G0| * _ ≤ h * B * (2 * (Bb1 * (h * (B / 2 + Ee)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hG0 hh0.le) this (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t5 : |h ^ 2 * G1 * (bP - bQ)| ≤ 2 * B * Bb * h ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ h ^ 2)]
    have h1 : |bP - bQ| ≤ 2 * Bb := (abs_sub _ _).trans (by linarith)
    calc h ^ 2 * |G1| * |bP - bQ| ≤ h ^ 2 * B * (2 * Bb) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hG1 (by positivity)) h1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t6 : |h * gp * bP + h * gm * bQ| ≤ 2 * Γ * Bb * h ^ 2 := by
    have u1 : |h * gp * bP| ≤ Γ * Bb * h ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hh0]
      have := mul_le_mul hgp hbPb (abs_nonneg _) (by positivity)
      calc h * |gp| * |bP| = h * (|gp| * |bP|) := by ring
        _ ≤ h * (Γ * h ^ 2 * Bb) := mul_le_mul_of_nonneg_left this hh0.le
        _ ≤ 1 * (Γ * h ^ 2 * Bb) := mul_le_mul_of_nonneg_right hh1 (by positivity)
        _ = _ := by ring
    have u2 : |h * gm * bQ| ≤ Γ * Bb * h ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hh0]
      have := mul_le_mul hgm hbQb (abs_nonneg _) (by positivity)
      calc h * |gm| * |bQ| = h * (|gm| * |bQ|) := by ring
        _ ≤ h * (Γ * h ^ 2 * Bb) := mul_le_mul_of_nonneg_left this hh0.le
        _ ≤ 1 * (Γ * h ^ 2 * Bb) := mul_le_mul_of_nonneg_right hh1 (by positivity)
        _ = _ := by ring
    calc _ ≤ |h * gp * bP| + |h * gm * bQ| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [abs_le] at t1 t2 t3 t4 t5 t6 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1, t6.2]

/-- **Parity skeleton for `𝔅`** (odd part `a`, even part `b`): the `h¹` coefficient is
`T = G₀ ζ'' a'(ζ') + 2 G₁ a(ζ') + 2 G₀ b(ζ')`. -/
theorem sk_odd_even {a a1 a2 b b1 : ℝ → ℝ} {S A0 A1 A2 Bb Bb1 : ℝ}
    (ha : ∀ x, HasDerivAt a (a1 x) x) (ha1 : ∀ x, HasDerivAt a1 (a2 x) x)
    (hb : ∀ x, HasDerivAt b (b1 x) x)
    (hapar : ∀ x, a (-x) = -a x) (hbpar : ∀ x, b (-x) = b x)
    (hA0 : ∀ x, |x| ≤ S → |a x| ≤ A0) (hA1 : ∀ x, |x| ≤ S → |a1 x| ≤ A1)
    (hA2 : ∀ x, |x| ≤ S → |a2 x| ≤ A2) (hBb : ∀ x, |x| ≤ S → |b x| ≤ Bb)
    (hBb1 : ∀ x, |x| ≤ S → |b1 x| ≤ Bb1)
    {h z1 z2 G0 G1 ep em gp gm B Ee Γ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hz2 : |z2| ≤ B) (hG0 : |G0| ≤ B) (hG1 : |G1| ≤ B)
    (hep : |ep| ≤ Ee * h ^ 2) (hem : |em| ≤ Ee * h ^ 2)
    (hgp : |gp| ≤ Γ * h ^ 2) (hgm : |gm| ≤ Γ * h ^ 2)
    (hsp : |z1 + h * z2 / 2 + ep| ≤ S) (hsm : |-z1 + h * z2 / 2 + em| ≤ S) (hz1S : |z1| ≤ S) :
    |(G0 + h * G1 + gp) * (a (z1 + h * z2 / 2 + ep) + h * b (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (a (-z1 + h * z2 / 2 + em) + h * b (-z1 + h * z2 / 2 + em)) -
        h * (G0 * z2 * a1 z1 + 2 * G1 * a z1 + 2 * G0 * b z1)| ≤
      (2 * B * (2 * A1 * Ee + 2 * A2 * (B / 2 + Ee) ^ 2) + 2 * Γ * A0 +
        2 * B * Bb1 * (B / 2 + Ee) + 2 * B * Bb + 2 * Γ * Bb) * h ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hz2
  have hEe : 0 ≤ Ee := by
    by_contra hneg
    have := (abs_nonneg ep).trans hep
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith
  have hΓ : 0 ≤ Γ := by
    by_contra hneg
    have := (abs_nonneg gp).trans hgp
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (pow_pos hh0 2)
    linarith
  obtain ⟨hdp_b, hdm_b, hsum'⟩ := sk_incr hh0 hh1 hz2 hep hem hEe
  have hsum : |ep + em| ≤ 2 * Ee * h ^ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hP' : z1 + h * z2 / 2 + ep = z1 + (h * z2 / 2 + ep) := by ring
  have hQ' : -z1 + h * z2 / 2 + em = -(z1 + -(h * z2 / 2 + em)) := by ring
  rw [hP'] at hsp ⊢
  rw [hQ'] at hsm ⊢
  rw [hapar, hbpar]
  have hQS : |z1 + -(h * z2 / 2 + em)| ≤ S := by rwa [abs_neg] at hsm
  have hM20 : 0 ≤ A2 := (abs_nonneg _).trans (hA2 z1 hz1S)
  have hA10 : 0 ≤ A1 := (abs_nonneg _).trans (hA1 z1 hz1S)
  have hBb10 : 0 ≤ Bb1 := (abs_nonneg _).trans (hBb1 z1 hz1S)
  have hBb0 : 0 ≤ Bb := (abs_nonneg _).trans (hBb z1 hz1S)
  have hD0 : 0 ≤ B / 2 + Ee := by positivity
  have hPa := sk_t2 ha ha1 hA2 hz1S (d := h * z2 / 2 + ep) hsp
  have hQa := sk_t2 ha ha1 hA2 hz1S (d := -(h * z2 / 2 + em)) hQS
  have hdp2 : (h * z2 / 2 + ep) ^ 2 ≤ (h * (B / 2 + Ee)) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.1 hdp_b]) (abs_le.1 hdp_b).2
  have hdm2 : (-(h * z2 / 2 + em)) ^ 2 ≤ (h * (B / 2 + Ee)) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.1 hdm_b]) (abs_le.1 hdm_b).2
  have hRp : |a (z1 + (h * z2 / 2 + ep)) - a z1 - a1 z1 * (h * z2 / 2 + ep)| ≤
      A2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by
    calc _ ≤ A2 * (h * z2 / 2 + ep) ^ 2 := hPa
      _ ≤ A2 * (h * (B / 2 + Ee)) ^ 2 := mul_le_mul_of_nonneg_left hdp2 hM20
      _ = A2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by ring
  have hRm : |a (z1 + -(h * z2 / 2 + em)) - a z1 - a1 z1 * (-(h * z2 / 2 + em))| ≤
      A2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by
    calc _ ≤ A2 * (-(h * z2 / 2 + em)) ^ 2 := hQa
      _ ≤ A2 * (h * (B / 2 + Ee)) ^ 2 := mul_le_mul_of_nonneg_left hdm2 hM20
      _ = A2 * (B / 2 + Ee) ^ 2 * h ^ 2 := by ring
  have hbP : |b (z1 + (h * z2 / 2 + ep)) - b z1| ≤ Bb1 * (h * (B / 2 + Ee)) := by
    have := sk_t1 hb hBb1 hz1S hsp
    have e : z1 + (h * z2 / 2 + ep) - z1 = h * z2 / 2 + ep := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdp_b hBb10)
  have hbQ : |b (z1 + -(h * z2 / 2 + em)) - b z1| ≤ Bb1 * (h * (B / 2 + Ee)) := by
    have := sk_t1 hb hBb1 hz1S hQS
    have e : z1 + -(h * z2 / 2 + em) - z1 = -(h * z2 / 2 + em) := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdm_b hBb10)
  exact sk_oe_alg hh0 hh1 hB0 hEe hΓ hA10 hM20 hBb10 hBb0 hG0 hG1 hgp hgm rfl rfl hsum hsum'
    hRp hRm hbP hbQ (hA0 _ hsp) (hA0 _ hQS) (hBb _ hsp) (hBb _ hQS) (hA1 _ hz1S)

end FormalResearch.Special

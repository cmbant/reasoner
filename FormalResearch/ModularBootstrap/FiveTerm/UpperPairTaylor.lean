module

public import Mathlib

/-!
# Taylor and ratio estimates for a scale function and a weight (FIVE-U; `cts:tip-shared` (b), setup)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C11$_0$ (`cts:tip-shared`) (b),
"Setup" of the proof of (b1).

For a scale function `s` (derivatives `s1, s2, s3` given explicitly) with `s' > 0`, `|s''| ≤ C₀ s'/a`,
`|s'''| ≤ C₀ s'/a²` on `[1,∞)` (`ScaleHyp`) and a weight `w` with `w > 0`, `|w'| ≤ C₀ w/a`, `|w''| ≤ C₀ w/a²`
(`WeightHyp`), for `n ≥ 2` and `|m| ≤ n/2`:

* `ratio_bounds`: `e^{-C₀} f(n) ≤ f(ξ) ≤ e^{C₀} f(n)` on `|ξ-n| ≤ n/2` (`f = s'` or `w`);
* `ScaleHyp.taylor`, `WeightHyp.taylor`: the second- and first-order Taylor expansions at `n` with the
  remainders `O(|m|³ s'(n)/n²)` and `O(m² w(n)/n²)`;
* `ScaleHyp.varsigma_le`: a point `x` in cell `n` has offset `|(s(n)-x)/s'(n)| ≤ 3/4` for `n ≥ 3C₀+2`;
* `ScaleHyp.dist_right/left`: `|s(n±m) - x| ≥ (e^{-C₀}/2) m s'(n)`.

All statements are proved.
-/

@[expose] public section

open Set

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma bound_of_deriv_bound {g g' : ℝ → ℝ} {L Bc : ℝ} {k : ℕ}
    (hg : ∀ x ∈ Icc 0 L, HasDerivAt g (g' x) x) (h0 : g 0 = 0)
    (hb : ∀ x ∈ Icc 0 L, |g' x| ≤ Bc * x ^ k) (t : ℝ) (ht : t ∈ Icc 0 L) :
    |g t| ≤ Bc * t ^ (k + 1) / (k + 1) := by
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Bc * x ^ (k + 1) / (k + 1)) (Bc * x ^ k) x := by
    intro x
    have := ((hasDerivAt_pow (k + 1) x).const_mul Bc).div_const ((k : ℝ) + 1)
    convert this using 1
    simp only [Nat.add_sub_cancel]
    have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [this]; field_simp
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := L)
    (f := g) (f' := g') (B := fun x : ℝ => Bc * x ^ (k + 1) / (k + 1)) (B' := fun x => Bc * x ^ k)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) (by simp [h0]) hB
    (fun x hx => hb x ⟨hx.1, hx.2.le⟩) ht
  simpa using this

/-- Third-order Taylor bound on `[0, L]` with a bound on the third derivative. -/
lemma taylor3_pos {φ φ1 φ2 φ3 : ℝ → ℝ} {L B : ℝ}
    (h0 : ∀ x ∈ Icc 0 L, HasDerivAt φ (φ1 x) x) (h1 : ∀ x ∈ Icc 0 L, HasDerivAt φ1 (φ2 x) x)
    (h2 : ∀ x ∈ Icc 0 L, HasDerivAt φ2 (φ3 x) x) (hB : ∀ x ∈ Icc 0 L, |φ3 x| ≤ B)
    (t : ℝ) (ht : t ∈ Icc 0 L) :
    |φ t - φ 0 - t * φ1 0 - t ^ 2 / 2 * φ2 0| ≤ B * t ^ 3 / 6 := by
  have hL : 0 ≤ L := ht.1.trans ht.2
  have s2 : ∀ x ∈ Icc 0 L, |φ2 x - φ2 0| ≤ B * x ^ 1 / (0 + 1) := by
    intro x hx
    have := bound_of_deriv_bound (g := fun x => φ2 x - φ2 0) (g' := φ3) (L := L) (Bc := B) (k := 0)
      (fun y hy => (h2 y hy).sub_const _) (by simp) (fun y hy => by simpa using hB y hy) x hx
    simpa using this
  have s1 : ∀ x ∈ Icc 0 L, |φ1 x - φ1 0 - x * φ2 0| ≤ B * x ^ 2 / 2 := by
    intro x hx
    have := bound_of_deriv_bound (g := fun x => φ1 x - φ1 0 - x * φ2 0) (g' := fun x => φ2 x - φ2 0)
      (L := L) (Bc := B) (k := 1)
      (fun y hy => by
        have := ((h1 y hy).sub_const (φ1 0)).sub ((hasDerivAt_id y).mul_const (φ2 0))
        have e : (fun x => φ1 x - φ1 0 - x * φ2 0) = (fun x => φ1 x - φ1 0) - fun x => id x * φ2 0 := by
          funext x; simp
        rw [e]; exact this.congr_deriv (by simp))
      (by simp) (fun y hy => by simpa using s2 y hy) x hx
    norm_num at this ⊢
    exact this
  have := bound_of_deriv_bound (g := fun x => φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0)
    (g' := fun x => φ1 x - φ1 0 - x * φ2 0) (L := L) (Bc := B / 2) (k := 2)
    (fun y hy => by
      have a1 := ((h0 y hy).sub_const (φ 0)).sub ((hasDerivAt_id y).mul_const (φ1 0))
      have a2 := ((hasDerivAt_pow 2 y).div_const 2).mul_const (φ2 0)
      have := a1.sub a2
      have e : (fun x => φ x - φ 0 - x * φ1 0 - x ^ 2 / 2 * φ2 0) =
          ((fun x => φ x - φ 0) - fun x => id x * φ1 0) - fun x => x ^ 2 / 2 * φ2 0 := by
        funext x; simp
      rw [e]; exact this.congr_deriv (by simp))
    (by simp) (fun y hy => by have := s1 y hy; linarith) t ht
  norm_num at this ⊢
  linarith


/-- Second-order Taylor bound on `[0, L]` with a bound on the second derivative. -/
lemma taylor2_pos {φ φ1 φ2 : ℝ → ℝ} {L B : ℝ}
    (h0 : ∀ x ∈ Icc 0 L, HasDerivAt φ (φ1 x) x) (h1 : ∀ x ∈ Icc 0 L, HasDerivAt φ1 (φ2 x) x)
    (hB : ∀ x ∈ Icc 0 L, |φ2 x| ≤ B) (t : ℝ) (ht : t ∈ Icc 0 L) :
    |φ t - φ 0 - t * φ1 0| ≤ B * t ^ 2 / 2 := by
  have s1 : ∀ x ∈ Icc 0 L, |φ1 x - φ1 0| ≤ B * x ^ 0 * x ^ 1 / 1 := by
    intro x hx
    have := bound_of_deriv_bound (g := fun x => φ1 x - φ1 0) (g' := φ2) (L := L) (Bc := B) (k := 0)
      (fun y hy => (h1 y hy).sub_const _) (by simp) (fun y hy => by simpa using hB y hy) x hx
    simpa using this
  have := bound_of_deriv_bound (g := fun x => φ x - φ 0 - x * φ1 0) (g' := fun x => φ1 x - φ1 0)
    (L := L) (Bc := B) (k := 1)
    (fun y hy => by
      have := ((h0 y hy).sub_const (φ 0)).sub ((hasDerivAt_id y).mul_const (φ1 0))
      have e : (fun x => φ x - φ 0 - x * φ1 0) = (fun x => φ x - φ 0) - fun x => id x * φ1 0 := by
        funext x; simp
      rw [e]; exact this.congr_deriv (by simp))
    (by simp) (fun y hy => by simpa using s1 y hy) t ht
  norm_num at this ⊢
  exact this

/-- Two-sided version of `taylor3_pos` on `[-L, L]`. -/
lemma taylor3_symm {φ φ1 φ2 φ3 : ℝ → ℝ} {L B : ℝ}
    (h0 : ∀ x ∈ Icc (-L) L, HasDerivAt φ (φ1 x) x) (h1 : ∀ x ∈ Icc (-L) L, HasDerivAt φ1 (φ2 x) x)
    (h2 : ∀ x ∈ Icc (-L) L, HasDerivAt φ2 (φ3 x) x) (hB : ∀ x ∈ Icc (-L) L, |φ3 x| ≤ B)
    (t : ℝ) (ht : t ∈ Icc (-L) L) :
    |φ t - φ 0 - t * φ1 0 - t ^ 2 / 2 * φ2 0| ≤ B * |t| ^ 3 / 6 := by
  have hL : 0 ≤ L := by linarith [ht.1, ht.2]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact taylor3_pos (fun x hx => h0 x ⟨by linarith [hx.1], hx.2⟩) (fun x hx => h1 x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => h2 x ⟨by linarith [hx.1], hx.2⟩) (fun x hx => hB x ⟨by linarith [hx.1], hx.2⟩) t ⟨h, ht.2⟩
  · have mem : ∀ x ∈ Icc 0 L, -x ∈ Icc (-L) L := fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := taylor3_pos (φ := fun x => φ (-x)) (φ1 := fun x => -φ1 (-x)) (φ2 := fun x => φ2 (-x))
      (φ3 := fun x => -φ3 (-x)) (L := L) (B := B)
      (fun x hx => ((h0 (-x) (mem x hx)).comp x (hasDerivAt_neg x)).congr_deriv (by simp))
      (fun x hx => (((h1 (-x) (mem x hx)).comp x (hasDerivAt_neg x)).neg).congr_deriv (by simp))
      (fun x hx => ((h2 (-x) (mem x hx)).comp x (hasDerivAt_neg x)).congr_deriv (by simp))
      (fun x hx => by simpa using hB (-x) (mem x hx)) (-t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [neg_neg, neg_zero] at this
    calc |φ t - φ 0 - t * φ1 0 - t ^ 2 / 2 * φ2 0|
        = |φ t - φ 0 - (-t) * -φ1 0 - (-t) ^ 2 / 2 * φ2 0| := by congr 1; ring
      _ ≤ B * (-t) ^ 3 / 6 := this
      _ = B * |t| ^ 3 / 6 := by rw [abs_of_nonpos h]

/-- Two-sided version of `taylor2_pos` on `[-L, L]`. -/
lemma taylor2_symm {φ φ1 φ2 : ℝ → ℝ} {L B : ℝ}
    (h0 : ∀ x ∈ Icc (-L) L, HasDerivAt φ (φ1 x) x) (h1 : ∀ x ∈ Icc (-L) L, HasDerivAt φ1 (φ2 x) x)
    (hB : ∀ x ∈ Icc (-L) L, |φ2 x| ≤ B) (t : ℝ) (ht : t ∈ Icc (-L) L) :
    |φ t - φ 0 - t * φ1 0| ≤ B * t ^ 2 / 2 := by
  have hL : 0 ≤ L := by linarith [ht.1, ht.2]
  rcases le_total 0 t with h | h
  · exact taylor2_pos (fun x hx => h0 x ⟨by linarith [hx.1], hx.2⟩) (fun x hx => h1 x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => hB x ⟨by linarith [hx.1], hx.2⟩) t ⟨h, ht.2⟩
  · have mem : ∀ x ∈ Icc 0 L, -x ∈ Icc (-L) L := fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have := taylor2_pos (φ := fun x => φ (-x)) (φ1 := fun x => -φ1 (-x)) (φ2 := fun x => φ2 (-x))
      (L := L) (B := B)
      (fun x hx => ((h0 (-x) (mem x hx)).comp x (hasDerivAt_neg x)).congr_deriv (by simp))
      (fun x hx => (((h1 (-x) (mem x hx)).comp x (hasDerivAt_neg x)).neg).congr_deriv (by simp))
      (fun x hx => by simpa using hB (-x) (mem x hx)) (-t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [neg_neg, neg_zero] at this
    calc |φ t - φ 0 - t * φ1 0| = |φ t - φ 0 - (-t) * -φ1 0| := by congr 1; ring
      _ ≤ B * (-t) ^ 2 / 2 := this
      _ = B * t ^ 2 / 2 := by ring


/-- A positive function with `|f'| ≤ C₀ f / a` has bounded log-oscillation on `[n/2, 3n/2]`. -/
lemma log_ratio_bound {f f1 : ℝ → ℝ} {C0 n ξ : ℝ} (hC0 : 0 ≤ C0)
    (hd : ∀ a, 1 ≤ a → HasDerivAt f (f1 a) a) (hpos : ∀ a, 1 ≤ a → 0 < f a)
    (hb : ∀ a, 1 ≤ a → |f1 a| ≤ C0 * f a / a) (hn : 2 ≤ n) (hξ : |ξ - n| ≤ n / 2) :
    |Real.log (f ξ) - Real.log (f n)| ≤ 2 * C0 * |ξ - n| / n := by
  have hs : Convex ℝ (Icc (n / 2) (3 * n / 2)) := convex_Icc _ _
  have hξm := abs_le.mp hξ
  have mem : ∀ a ∈ Icc (n / 2) (3 * n / 2), 1 ≤ a := fun a ha => by linarith [ha.1]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun a => Real.log (f a))
    (f' := fun a => f1 a / f a) (C := 2 * C0 / n) (s := Icc (n / 2) (3 * n / 2)) (x := n) (y := ξ)
    (fun a ha => ((hd a (mem a ha)).log (hpos a (mem a ha)).ne').hasDerivWithinAt)
    (fun a ha => by
      have h1 := mem a ha
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos a h1), div_le_iff₀ (hpos a h1)]
      have h2 := hb a h1
      have h3 : C0 * f a / a ≤ 2 * C0 / n * f a := by
        rw [div_le_iff₀ (by linarith [ha.1])]
        have : 2 * C0 / n * f a * a = C0 * f a * (2 * a / n) := by field_simp
        rw [this]
        have h4 : 1 ≤ 2 * a / n := by rw [le_div_iff₀ (by linarith)]; linarith [ha.1]
        nlinarith only [mul_nonneg hC0 (hpos a h1).le, h4]
      exact h2.trans h3)
    hs ⟨by linarith, by linarith⟩ ⟨by linarith [hξm.1], by linarith [hξm.2]⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc _ ≤ 2 * C0 / n * |ξ - n| := this
    _ = _ := by ring

/-- Hypotheses on a scale function `s` (first three derivatives given explicitly):
`s' > 0`, `|s''| ≤ C₀ s'/a`, `|s'''| ≤ C₀ s'/a²` on `[1, ∞)`. -/
structure ScaleHyp (s s1 s2 s3 : ℝ → ℝ) (C0 : ℝ) : Prop where
  c0 : 0 ≤ C0
  d0 : ∀ a, 1 ≤ a → HasDerivAt s (s1 a) a
  d1 : ∀ a, 1 ≤ a → HasDerivAt s1 (s2 a) a
  d2 : ∀ a, 1 ≤ a → HasDerivAt s2 (s3 a) a
  pos : ∀ a, 1 ≤ a → 0 < s1 a
  b2 : ∀ a, 1 ≤ a → |s2 a| ≤ C0 * s1 a / a
  b3 : ∀ a, 1 ≤ a → |s3 a| ≤ C0 * s1 a / a ^ 2

/-- Hypotheses on a weight `w`: `w > 0`, `|w'| ≤ C₀ w/a`, `|w''| ≤ C₀ w/a²` on `[1, ∞)`. -/
structure WeightHyp (w w1 w2 : ℝ → ℝ) (C0 : ℝ) : Prop where
  c0 : 0 ≤ C0
  d0 : ∀ a, 1 ≤ a → HasDerivAt w (w1 a) a
  d1 : ∀ a, 1 ≤ a → HasDerivAt w1 (w2 a) a
  pos : ∀ a, 1 ≤ a → 0 < w a
  b1 : ∀ a, 1 ≤ a → |w1 a| ≤ C0 * w a / a
  b2 : ∀ a, 1 ≤ a → |w2 a| ≤ C0 * w a / a ^ 2

/-- Two-sided ratio bounds `e^{-C₀} ≤ f(ξ)/f(n) ≤ e^{C₀}` on `|ξ - n| ≤ n/2`. -/
lemma ratio_bounds {f f1 : ℝ → ℝ} {C0 n ξ : ℝ} (hC0 : 0 ≤ C0)
    (hd : ∀ a, 1 ≤ a → HasDerivAt f (f1 a) a) (hpos : ∀ a, 1 ≤ a → 0 < f a)
    (hb : ∀ a, 1 ≤ a → |f1 a| ≤ C0 * f a / a) (hn : 2 ≤ n) (hξ : |ξ - n| ≤ n / 2) :
    Real.exp (-C0) * f n ≤ f ξ ∧ f ξ ≤ Real.exp C0 * f n := by
  have h := log_ratio_bound hC0 hd hpos hb hn hξ
  have h1 : 2 * C0 * |ξ - n| / n ≤ C0 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith only [mul_le_mul_of_nonneg_left hξ hC0]
  have h2 := abs_le.mp (h.trans h1)
  have hn1 : 1 ≤ n := by linarith
  have hξ1 : 1 ≤ ξ := by linarith [(abs_le.mp hξ).1]
  have e1 : f ξ = f n * Real.exp (Real.log (f ξ) - Real.log (f n)) := by
    rw [Real.exp_sub, Real.exp_log (hpos _ hξ1), Real.exp_log (hpos _ hn1)]; field_simp [(hpos _ hn1).ne']
  constructor
  · have := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h2.1) (hpos _ hn1).le
    rw [e1]; linarith
  · have := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h2.2) (hpos _ hn1).le
    rw [e1]; linarith


lemma ScaleHyp.s1_ratio {s s1 s2 s3 : ℝ → ℝ} {C0 n ξ : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hn : 2 ≤ n)
    (hξ : |ξ - n| ≤ n / 2) : Real.exp (-C0) * s1 n ≤ s1 ξ ∧ s1 ξ ≤ Real.exp C0 * s1 n :=
  ratio_bounds h.c0 h.d1 h.pos h.b2 hn hξ

lemma ScaleHyp.taylor {s s1 s2 s3 : ℝ → ℝ} {C0 n m : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hn : 2 ≤ n)
    (hm : |m| ≤ n / 2) :
    |s (n + m) - s n - m * s1 n - m ^ 2 / 2 * s2 n| ≤ 4 * C0 * Real.exp C0 * s1 n / n ^ 2 * |m| ^ 3 / 6 := by
  have hn1 : 1 ≤ n := by linarith
  have hmI : m ∈ Icc (-(n / 2)) (n / 2) := abs_le.mp hm
  have mem : ∀ x ∈ Icc (-(n / 2)) (n / 2), 1 ≤ n + x := fun x hx => by linarith [hx.1]
  have := taylor3_symm (φ := fun t => s (n + t)) (φ1 := fun t => s1 (n + t)) (φ2 := fun t => s2 (n + t))
    (φ3 := fun t => s3 (n + t)) (L := n / 2) (B := 4 * C0 * Real.exp C0 * s1 n / n ^ 2)
    (fun x hx => (h.d0 (n + x) (mem x hx)).comp_const_add n x)
    (fun x hx => (h.d1 (n + x) (mem x hx)).comp_const_add n x)
    (fun x hx => (h.d2 (n + x) (mem x hx)).comp_const_add n x)
    (fun x hx => by
      have hx1 : |n + x - n| ≤ n / 2 := by simpa using abs_le.mpr hx
      have hr := (h.s1_ratio hn hx1).2
      have hpos := h.pos (n + x) (mem x hx)
      have hb := h.b3 (n + x) (mem x hx)
      have hnx : n / 2 ≤ n + x := by linarith [hx.1]
      calc |s3 (n + x)| ≤ C0 * s1 (n + x) / (n + x) ^ 2 := hb
        _ ≤ C0 * (Real.exp C0 * s1 n) / (n / 2) ^ 2 := by
            apply div_le_div₀ (mul_nonneg h.c0 (mul_nonneg (Real.exp_pos _).le (h.pos n hn1).le))
              (mul_le_mul_of_nonneg_left hr h.c0)
              (by positivity) (pow_le_pow_left₀ (by positivity) hnx 2)
        _ = 4 * C0 * Real.exp C0 * s1 n / n ^ 2 := by field_simp; norm_num) m hmI
  simpa using this

lemma WeightHyp.taylor {w w1 w2 : ℝ → ℝ} {C0 n m : ℝ} (h : WeightHyp w w1 w2 C0) (hn : 2 ≤ n)
    (hm : |m| ≤ n / 2) :
    |w (n + m) - w n - m * w1 n| ≤ 4 * C0 * Real.exp C0 * w n / n ^ 2 * m ^ 2 / 2 := by
  have hn1 : 1 ≤ n := by linarith
  have hmI : m ∈ Icc (-(n / 2)) (n / 2) := abs_le.mp hm
  have mem : ∀ x ∈ Icc (-(n / 2)) (n / 2), 1 ≤ n + x := fun x hx => by linarith [hx.1]
  have := taylor2_symm (φ := fun t => w (n + t)) (φ1 := fun t => w1 (n + t)) (φ2 := fun t => w2 (n + t))
    (L := n / 2) (B := 4 * C0 * Real.exp C0 * w n / n ^ 2)
    (fun x hx => (h.d0 (n + x) (mem x hx)).comp_const_add n x)
    (fun x hx => (h.d1 (n + x) (mem x hx)).comp_const_add n x)
    (fun x hx => by
      have hx1 : |n + x - n| ≤ n / 2 := by simpa using abs_le.mpr hx
      have hr := (ratio_bounds h.c0 h.d0 h.pos h.b1 hn hx1).2
      have hpos := h.pos (n + x) (mem x hx)
      have hb := h.b2 (n + x) (mem x hx)
      have hnx : n / 2 ≤ n + x := by linarith [hx.1]
      calc |w2 (n + x)| ≤ C0 * w (n + x) / (n + x) ^ 2 := hb
        _ ≤ C0 * (Real.exp C0 * w n) / (n / 2) ^ 2 := by
            apply div_le_div₀ (mul_nonneg h.c0 (mul_nonneg (Real.exp_pos _).le (h.pos n hn1).le))
              (mul_le_mul_of_nonneg_left hr h.c0)
              (by positivity) (pow_le_pow_left₀ (by positivity) hnx 2)
        _ = 4 * C0 * Real.exp C0 * w n / n ^ 2 := by field_simp; norm_num) m hmI
  simpa using this


lemma ScaleHyp.mvt {s s1 s2 s3 : ℝ → ℝ} {C0 a b : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hab : a < b)
    (ha : 1 ≤ a) : ∃ ξ ∈ Ioo a b, s b - s a = s1 ξ * (b - a) := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope s s1 hab
    (fun x hx => (h.d0 x (ha.trans hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => h.d0 x (ha.trans hx.1.le))
  exact ⟨ξ, hξ, by rw [hd]; field_simp [(sub_pos.mpr hab).ne']⟩

lemma exp_third_le : Real.exp (1 / 3) ≤ 3 / 2 := by
  have h1 : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 < Real.exp (1 / 3) := Real.exp_pos _
  by_contra hcon
  have : (3 / 2 : ℝ) ^ 3 < Real.exp (1 / 3) ^ 3 := pow_lt_pow_left₀ (not_le.mp hcon) (by norm_num) (by norm_num)
  rw [h1] at this
  norm_num at this h2
  linarith

lemma ScaleHyp.s1_fine {s s1 s2 s3 : ℝ → ℝ} {C0 n ξ : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hn : 3 * C0 + 2 ≤ n)
    (hξ : |ξ - n| ≤ 1 / 2) : s1 ξ ≤ 3 / 2 * s1 n := by
  have hC0 := h.c0
  have hn2 : 2 ≤ n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hξ' : |ξ - n| ≤ n / 2 := hξ.trans (by linarith)
  have hl := log_ratio_bound hC0 h.d1 h.pos h.b2 hn2 hξ'
  have h1 : 2 * C0 * |ξ - n| / n ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [mul_le_mul_of_nonneg_left hξ (by linarith : (0:ℝ) ≤ 2 * C0), hn, hC0]
  have hξ1 : 1 ≤ ξ := by linarith [(abs_le.mp hξ).1]
  have e1 : s1 ξ = s1 n * Real.exp (Real.log (s1 ξ) - Real.log (s1 n)) := by
    rw [Real.exp_sub, Real.exp_log (h.pos _ hξ1), Real.exp_log (h.pos _ hn1)]; field_simp [(h.pos _ hn1).ne']
  have h2 : Real.exp (Real.log (s1 ξ) - Real.log (s1 n)) ≤ 3 / 2 :=
    (Real.exp_le_exp.mpr ((le_abs_self _).trans (hl.trans h1))).trans exp_third_le
  rw [e1]
  nlinarith only [mul_le_mul_of_nonneg_left h2 (h.pos _ hn1).le]

/-- The offset `ς = (s(n) - x)/s'(n)` of a point `x` in cell `n` is at most `3/4`. -/
lemma ScaleHyp.varsigma_le {s s1 s2 s3 : ℝ → ℝ} {C0 n x : ℝ} (h : ScaleHyp s s1 s2 s3 C0)
    (hn : 3 * C0 + 2 ≤ n) (hx1 : s (n - 1 / 2) ≤ x) (hx2 : x ≤ s (n + 1 / 2)) :
    |(s n - x) / s1 n| ≤ 3 / 4 := by
  have hC0 := h.c0
  have hn1 : 1 ≤ n := by linarith
  have hp := h.pos n hn1
  obtain ⟨ξ1, hξ1, e1⟩ := h.mvt (a := n) (b := n + 1 / 2) (by linarith) hn1
  obtain ⟨ξ2, hξ2, e2⟩ := h.mvt (a := n - 1 / 2) (b := n) (by linarith) (by linarith)
  have b1 := h.s1_fine hn (ξ := ξ1) (by rw [abs_le]; constructor <;> linarith [hξ1.1, hξ1.2])
  have b2 := h.s1_fine hn (ξ := ξ2) (by rw [abs_le]; constructor <;> linarith [hξ2.1, hξ2.2])
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  have c1 : s (n + 1 / 2) - s n ≤ 3 / 4 * s1 n := by
    have : s1 ξ1 * (n + 1 / 2 - n) ≤ 3 / 2 * s1 n * (1 / 2) := by
      apply mul_le_mul b1 (by linarith) (by linarith) (by positivity)
    nlinarith only [e1, this]
  have c2 : s n - s (n - 1 / 2) ≤ 3 / 4 * s1 n := by
    have : s1 ξ2 * (n - (n - 1 / 2)) ≤ 3 / 2 * s1 n * (1 / 2) := by
      apply mul_le_mul b2 (by linarith) (by linarith) (by positivity)
    nlinarith only [e2, this]
  constructor <;> nlinarith only [c1, c2, hx1, hx2]


/-- Lower bound for the distance from `x` (in cell `n`) to the site `n + m`, `1 ≤ m ≤ n/2`. -/
lemma ScaleHyp.dist_right {s s1 s2 s3 : ℝ → ℝ} {C0 n x m : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hn : 2 ≤ n)
    (hm1 : 1 ≤ m) (hm : m ≤ n / 2) (hx2 : x ≤ s (n + 1 / 2)) :
    Real.exp (-C0) / 2 * m * s1 n ≤ s (n + m) - x := by
  have hn1 : 1 ≤ n := by linarith
  obtain ⟨ξ, hξ, e⟩ := h.mvt (a := n + 1 / 2) (b := n + m) (by linarith) (by linarith)
  have hr := (h.s1_ratio hn (ξ := ξ) (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])).1
  have hp := h.pos n hn1
  have hE : 0 < Real.exp (-C0) := Real.exp_pos _
  have : Real.exp (-C0) * s1 n * (n + m - (n + 1 / 2)) ≤ s1 ξ * (n + m - (n + 1 / 2)) :=
    mul_le_mul_of_nonneg_right hr (by linarith)
  have h2 : 0 ≤ Real.exp (-C0) * s1 n := by positivity
  nlinarith only [this, e, hx2, h2, hm1]

/-- Lower bound for the distance from `x` (in cell `n`) to the site `n - m`, `1 ≤ m ≤ n/2`. -/
lemma ScaleHyp.dist_left {s s1 s2 s3 : ℝ → ℝ} {C0 n x m : ℝ} (h : ScaleHyp s s1 s2 s3 C0) (hn : 2 ≤ n)
    (hm1 : 1 ≤ m) (hm : m ≤ n / 2) (hx1 : s (n - 1 / 2) ≤ x) :
    Real.exp (-C0) / 2 * m * s1 n ≤ x - s (n - m) := by
  have hn1 : 1 ≤ n := by linarith
  obtain ⟨ξ, hξ, e⟩ := h.mvt (a := n - m) (b := n - 1 / 2) (by linarith) (by linarith)
  have hr := (h.s1_ratio hn (ξ := ξ) (by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])).1
  have hp := h.pos n hn1
  have hE : 0 < Real.exp (-C0) := Real.exp_pos _
  have : Real.exp (-C0) * s1 n * (n - 1 / 2 - (n - m)) ≤ s1 ξ * (n - 1 / 2 - (n - m)) :=
    mul_le_mul_of_nonneg_right hr (by linarith)
  have h2 : 0 ≤ Real.exp (-C0) * s1 n := by positivity
  nlinarith only [this, e, hx1, h2, hm1]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.ScaleHyp.taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScaleHyp.taylor

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.ScaleHyp.varsigma_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScaleHyp.varsigma_le

end FormalResearch.ModularBootstrap.FiveTerm

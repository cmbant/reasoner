module

public import FormalResearch.SignUncertainty.UctWExp

/-!
# Weak weighted expansions: pure powers of `h` allowed (F2a, `uct:bump-weighted` far band)

`WExp` of `UctWExp.lean` forbids pure powers of `h` (monomials `h^n v^0`, `n ≥ 1`), which is right for `E₀` but not for the `v`-derivatives of its
expansion (`∂_v v = 1`).  `WExpW N k0 a0 f` is the same notion with the *weak* weighted polynomials `WPolyW` (only `k ≤ 3n`): sums, products, bounds and smooth
atoms, with the same norm estimates.  `WExp.toW` embeds the strong class.  Used for `h² K''` in `UctE0Deriv.lean`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MvPolynomial Finset

namespace FormalResearch.SignUncertainty

/-- Weak weighted polynomials: every monomial `h^n v^k` has `k ≤ 3 n`. -/
def WPolyW (P : P2) : Prop := ∀ d : Fin 2 →₀ ℕ, P.coeff d ≠ 0 → d 1 ≤ 3 * d 0

lemma WPoly.toW {P : P2} (hP : WPoly P) : WPolyW P := fun d hd => (hP d hd).1

lemma WPolyW.zero : WPolyW 0 := fun d hd => absurd (by simp) hd

lemma WPolyW.add {P Q : P2} (hP : WPolyW P) (hQ : WPolyW Q) : WPolyW (P + Q) := by
  intro d hd
  have hd' : P.coeff d + Q.coeff d ≠ 0 := by simpa using hd
  by_cases h1 : P.coeff d = 0
  · rw [h1, zero_add] at hd'; exact hQ d hd'
  · exact hP d h1

lemma WPolyW.mul {P Q : P2} (hP : WPolyW P) (hQ : WPolyW Q) : WPolyW (P * Q) := by
  intro d hd
  classical
  rw [MvPolynomial.coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have hsum := Finset.mem_antidiagonal.mp hef
  have h1 : P.coeff e ≠ 0 := fun h => hne (by simp [h])
  have h2 : Q.coeff f ≠ 0 := fun h => hne (by simp [h])
  have h3 := hP e h1
  have h4 := hQ f h2
  have hd0 : d 0 = e 0 + f 0 := by rw [← hsum]; rfl
  have hd1 : d 1 = e 1 + f 1 := by rw [← hsum]; rfl
  omega

lemma WPolyW.const (a : ℂ) : WPolyW (MvPolynomial.C a) := (WPoly.const a).toW

lemma WPolyW.wmono {n k : ℕ} (hk : k ≤ 3 * n) (a : ℂ) : WPolyW (wmono n k a) := by
  classical
  intro d hd
  rw [wmono_eq, MvPolynomial.coeff_monomial] at hd
  by_cases h : Finsupp.single 0 n + Finsupp.single 1 k = d
  · subst h; simpa using hk
  · simp [h] at hd

lemma norm_wev_le_w {P : P2} (hP : WPolyW P) {k0 h v : ℝ} (hr : WReg k0 h v) :
    ‖wev h v P‖ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * wx h v ^ (d 0) := by
  rw [wev_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_mon_le hr (hP d (by simpa using hd))) (norm_nonneg _)

lemma norm_wev_le_cnorm_w {P : P2} (hP : WPolyW P) {k0 h v : ℝ} (hr : WReg k0 h v) (hk0 : k0 ≤ 1) :
    ‖wev h v P‖ ≤ cnorm P := by
  refine (norm_wev_le_w hP hr).trans (Finset.sum_le_sum fun d _ => ?_)
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  calc ‖P.coeff d‖ * wx h v ^ (d 0) ≤ ‖P.coeff d‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (norm_nonneg _)
    _ = _ := mul_one _

lemma norm_wev_le_x_w {P : P2} (hP : WPolyW P) (h0 : MvPolynomial.constantCoeff P = 0) {k0 h v : ℝ}
    (hr : WReg k0 h v) (hk0 : k0 ≤ 1) : ‖wev h v P‖ ≤ cnorm P * wx h v := by
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  refine (norm_wev_le_w hP hr).trans ?_
  rw [cnorm, Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  have hdc : P.coeff d ≠ 0 := by simpa using hd
  have hd0 : 1 ≤ d 0 := by
    by_contra hcon
    have h0' : d 0 = 0 := by omega
    have h1' : d 1 = 0 := by have := hP d hdc; omega
    have : d = 0 := by ext i; fin_cases i <;> simp [h0', h1']
    subst this
    exact hdc (by simpa [MvPolynomial.constantCoeff_eq] using h0)
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hx0 hx1 (by omega)) (norm_nonneg _)

/-- `f(h,v) = P(h,v) + O(x^N)` on `WReg k0`, `P` a *weak* weighted polynomial with constant term `a0`. -/
def WExpW (N : ℕ) (k0 : ℝ) (a0 : ℂ) (f : ℝ → ℝ → ℂ) : Prop :=
  ∃ (P : P2) (C : ℝ), WPolyW P ∧ MvPolynomial.constantCoeff P = a0 ∧ 0 ≤ C ∧
    ∀ h v : ℝ, WReg k0 h v → ‖f h v - wev h v P‖ ≤ C * wx h v ^ N

lemma WExp.toW {N : ℕ} {k0 : ℝ} {a0 : ℂ} {f : ℝ → ℝ → ℂ} (hf : WExp N k0 a0 f) : WExpW N k0 a0 f := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  exact ⟨P, C, hP.toW, hc, hC, hb⟩

namespace WExpW

variable {N : ℕ} {k0 : ℝ} {a0 b0 : ℂ} {f g : ℝ → ℝ → ℂ}

lemma const (a : ℂ) : WExpW N k0 a (fun _ _ => a) := (WExp.const a).toW

lemma congr (hf : WExpW N k0 a0 f) (hfg : ∀ h v, WReg k0 h v → f h v = g h v) : WExpW N k0 a0 g := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  exact ⟨P, C, hP, hc, hC, fun h v hr => by rw [← hfg h v hr]; exact hb h v hr⟩

lemma congr_a (hf : WExpW N k0 a0 f) (h0 : a0 = b0) : WExpW N k0 b0 f := h0 ▸ hf

lemma add (hf : WExpW N k0 a0 f) (hg : WExpW N k0 b0 g) :
    WExpW N k0 (a0 + b0) (fun h v => f h v + g h v) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  obtain ⟨Q, D, hQ, hd, hD, hb'⟩ := hg
  refine ⟨P + Q, C + D, hP.add hQ, by simp [hc, hd], by positivity, fun h v hr => ?_⟩
  have e : f h v + g h v - wev h v (P + Q) = (f h v - wev h v P) + (g h v - wev h v Q) := by
    rw [map_add]; ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hb h v hr) (hb' h v hr))

lemma mul (hk0 : k0 ≤ 1) (hf : WExpW N k0 a0 f) (hg : WExpW N k0 b0 g) :
    WExpW N k0 (a0 * b0) (fun h v => f h v * g h v) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  obtain ⟨Q, D, hQ, hd, hD, hb'⟩ := hg
  refine ⟨P * Q, C * (cnorm Q + D) + cnorm P * D, hP.mul hQ, by simp [hc, hd], by
    have := cnorm_nonneg P; have := cnorm_nonneg Q; positivity, fun h v hr => ?_⟩
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  have hxN : wx h v ^ N ≤ 1 := pow_le_one₀ hx0 hx1
  have hgn : ‖g h v‖ ≤ cnorm Q + D := by
    have h1 := norm_wev_le_cnorm_w hQ hr hk0
    have h2 := hb' h v hr
    have : ‖g h v‖ ≤ ‖wev h v Q‖ + ‖g h v - wev h v Q‖ := by
      calc ‖g h v‖ = ‖wev h v Q + (g h v - wev h v Q)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith [mul_le_of_le_one_right hD hxN]
  have e : f h v * g h v - wev h v (P * Q) = (f h v - wev h v P) * g h v + wev h v P * (g h v - wev h v Q) := by
    rw [map_mul]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hPn := norm_wev_le_cnorm_w hP hr hk0
  have t1 : ‖f h v - wev h v P‖ * ‖g h v‖ ≤ C * wx h v ^ N * (cnorm Q + D) :=
    mul_le_mul (hb h v hr) hgn (norm_nonneg _) (by positivity)
  have t2 : ‖wev h v P‖ * ‖g h v - wev h v Q‖ ≤ cnorm P * (D * wx h v ^ N) :=
    mul_le_mul hPn (hb' h v hr) (norm_nonneg _) (cnorm_nonneg P)
  nlinarith [t1, t2]

lemma bound {C : ℝ} (hf : ∀ h v, WReg k0 h v → ‖f h v‖ ≤ C * wx h v ^ N) (hC : 0 ≤ C) : WExpW N k0 0 f :=
  ⟨0, C, WPolyW.zero, by simp, hC, fun h v hr => by simpa using hf h v hr⟩

lemma mono {k1 : ℝ} (hk : k1 ≤ k0) (hf : WExpW N k0 a0 f) : WExpW N k1 a0 f := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  exact ⟨P, C, hP, hc, hC, fun h v hr => hb h v ⟨hr.1, hr.2.trans hk⟩⟩

/-- A function with a weak expansion of order `N ≥ 1` and zero constant term is `O(x)`. -/
lemma norm_le_x (hk0 : k0 ≤ 1) (hN : 1 ≤ N) (hf : WExpW N k0 0 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h v : ℝ, WReg k0 h v → ‖f h v‖ ≤ C * wx h v := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  refine ⟨cnorm P + C, by have := cnorm_nonneg P; positivity, fun h v hr => ?_⟩
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  have hxN : wx h v ^ N ≤ wx h v := pow_le_of_le_one hx0 hx1 (by omega)
  have h1 := norm_wev_le_x_w hP hc hr hk0
  have h2 := hb h v hr
  have : ‖f h v‖ ≤ ‖wev h v P‖ + ‖f h v - wev h v P‖ := by
    calc ‖f h v‖ = ‖wev h v P + (f h v - wev h v P)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  nlinarith [mul_le_mul_of_nonneg_left hxN hC]

/-- A function with a weak expansion is bounded on the region. -/
lemma norm_le_const (hk0 : k0 ≤ 1) (hf : WExpW N k0 a0 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h v : ℝ, WReg k0 h v → ‖f h v‖ ≤ C := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  refine ⟨cnorm P + C, by have := cnorm_nonneg P; positivity, fun h v hr => ?_⟩
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  have hxN : wx h v ^ N ≤ 1 := pow_le_one₀ hx0 hx1
  have h1 := norm_wev_le_cnorm_w hP hr hk0
  have h2 := hb h v hr
  have : ‖f h v‖ ≤ ‖wev h v P‖ + ‖f h v - wev h v P‖ := by
    calc ‖f h v‖ = ‖wev h v P + (f h v - wev h v P)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  nlinarith [mul_le_of_le_one_right hC hxN]

/-- The pure power `h^m` (`m ≥ 1`). -/
lemma hpow (m : ℕ) (hm : 1 ≤ m) : WExpW N k0 0 (fun h _ => (h : ℂ) ^ m) := by
  refine ⟨wmono m 0 1, 0, WPolyW.wmono (by omega) 1, ?_, le_rfl, fun h v _ => ?_⟩
  · simp [wmono, zero_pow (by omega : m ≠ 0)]
  · simp [wev_wmono]

/-- `h^m g(h v)` for smooth `g` and `m ≥ 1`. -/
lemma hpow_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hN : 1 ≤ N) (hk : 0 < k0) (hk1 : k0 ≤ 1) (m : ℕ)
    (hm : 1 ≤ m) : WExpW N k0 0 (fun h v => (h : ℂ) ^ m * g (h * v)) := by
  have := (hpow (N := N) (k0 := k0) m hm).mul hk1 (WExp.of_smooth hg hN hk).toW
  rw [zero_mul] at this
  exact this

/-- `h⁻¹ g(h v)` for smooth `g` vanishing to order `2` at `0`: `h^{l-1} v^l`, `l ≥ 2`. -/
lemma inv_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hN : 1 ≤ N) (hk : 0 < k0)
    (h0 : ∀ l < 2, iteratedDeriv l g 0 = 0) :
    WExpW N k0 0 (fun h v => (((h)⁻¹ : ℝ) : ℂ) * g (h * v)) := by
  obtain ⟨C, hC, hT⟩ := taylor_poly_bound hg N hk
  set gl : ℕ → ℂ := fun l => iteratedDeriv l g 0 / (l.factorial : ℂ) with hgl
  have hgl0 : ∀ l < 2, gl l = 0 := fun l hl => by simp [hgl, h0 l hl]
  set P : P2 := ∑ l ∈ Finset.Icc 2 N, wmono (l - 1) l (gl l) with hP
  have hPp : WPolyW P := by
    refine fun d hd => ?_
    classical
    rw [hP, MvPolynomial.coeff_sum] at hd
    obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    have hl2 := (Finset.mem_Icc.mp hl).1
    have := WPolyW.wmono (n := l - 1) (k := l) (by omega) (gl l) d hne
    exact this
  refine ⟨P, C, hPp, ?_, hC, fun h v hr => ?_⟩
  · rw [hP, map_sum]
    refine Finset.sum_eq_zero fun l hl => ?_
    have := (Finset.mem_Icc.mp hl).1
    simp [wmono, zero_pow (by omega : l - 1 ≠ 0)]
  · have hh := hr.1
    have hwP : wev h v P = ∑ l ∈ Finset.Icc 2 N, (((h)⁻¹ : ℝ) : ℂ) * ((gl l) * ((h * v : ℝ) : ℂ) ^ l) := by
      rw [hP, map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl2 := (Finset.mem_Icc.mp hl).1
      rw [wev_wmono]
      have hpow : (h : ℂ) ^ l = (h : ℂ) ^ (l - 1) * (h : ℂ) := by
        rw [← pow_succ]; congr 1; omega
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      push_cast
      rw [mul_pow, hpow]
      field_simp
    have hz : |h * v| ≤ k0 := by
      rw [abs_mul, abs_of_pos hh]; exact (WExp.abs_mul_le_wx hh).trans hr.2
    have hT' := hT (h * v) hz
    have hsub : Finset.Icc 2 N ⊆ Finset.range (N + 1) := fun l hl => by
      have := (Finset.mem_Icc.mp hl).2; exact Finset.mem_range.mpr (by omega)
    have hsum : ∑ l ∈ Finset.range (N + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l =
        ∑ l ∈ Finset.Icc 2 N, (gl l) * ((h * v : ℝ) : ℂ) ^ l := by
      symm
      refine Finset.sum_subset hsub fun l hl hnl => ?_
      have : l < 2 := by
        by_contra hcon
        exact hnl (Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hl; omega⟩)
      simp [hgl0 l this]
    have e : (((h)⁻¹ : ℝ) : ℂ) * g (h * v) - wev h v P =
        (((h)⁻¹ : ℝ) : ℂ) * (g (h * v) - ∑ l ∈ Finset.range (N + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l) := by
      rw [hwP, hsum, ← Finset.mul_sum]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hpow' : (h)⁻¹ * (C * |h * v| ^ (N + 1)) = C * (h ^ N * |v| ^ (N + 1)) := by
      rw [abs_mul, abs_of_pos hh, mul_pow]
      field_simp
      ring
    calc (h)⁻¹ * ‖g (h * v) - ∑ l ∈ Finset.range (N + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l‖
        ≤ (h)⁻¹ * (C * |h * v| ^ (N + 1)) := mul_le_mul_of_nonneg_left hT' (by positivity)
      _ = C * (h ^ N * |v| ^ (N + 1)) := hpow'
      _ ≤ C * wx h v ^ N := mul_le_mul_of_nonneg_left (WExp.pow_abs_le_wx v hh (N + 1) N (by omega)) hC

end WExpW

end FormalResearch.SignUncertainty

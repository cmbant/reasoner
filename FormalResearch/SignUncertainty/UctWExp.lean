module

public import FormalResearch.SignUncertainty.UctWExpTaylor
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Weighted expansions in the two scales `(h, v)` (F2a, `uct:bump-weighted`)

For `h > 0`, `v ∈ ℝ` put `x = h (1+|v|)^3`; `WReg k0 h v` is `0 < h`, `x ≤ k0`.  A *weighted polynomial* is an element of `ℂ[h, v]` all of whose monomials
`h^n v^k` satisfy `k ≤ 3n` (so `|h^n v^k| ≤ x^n`).  `WExp N k0 a0 f` says `f(h,v) = P(h,v) + O(x^N)` on `WReg k0` for a weighted polynomial `P`
with constant term `a0`.  This class is closed under sums, products (`WExp.mul`), and truncated exponentials of expansions with zero constant term (`WExp.exp`);
smooth functions of `h v` are in it (`WExp.of_smooth`).  `WExp.expansion` truncates the polynomial at weight `< N`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MvPolynomial Finset

namespace FormalResearch.SignUncertainty

/-- The region `0 < h`, `h (1+|v|)^3 ≤ k0`. -/
def WReg (k0 h v : ℝ) : Prop := 0 < h ∧ h * (1 + |v|) ^ 3 ≤ k0

/-- `x = h (1+|v|)^3`. -/
def wx (h v : ℝ) : ℝ := h * (1 + |v|) ^ 3

abbrev P2 := MvPolynomial (Fin 2) ℂ

/-- Evaluation at `(h, v)`. -/
noncomputable def wev (h v : ℝ) : P2 →+* ℂ := MvPolynomial.eval ![(h : ℂ), (v : ℂ)]

/-- Weighted polynomials: every monomial `h^n v^k` has `k ≤ 3 n`, and `k = 0` forces `n = 0` (no pure powers of `h`). -/
def WPoly (P : P2) : Prop := ∀ d : Fin 2 →₀ ℕ, P.coeff d ≠ 0 → d 1 ≤ 3 * d 0 ∧ (d 1 = 0 → d 0 = 0)

lemma wx_nonneg {h v : ℝ} (hh : 0 < h) : 0 ≤ wx h v := by unfold wx; positivity

lemma WReg.wx_le {k0 h v : ℝ} (hr : WReg k0 h v) : wx h v ≤ k0 := hr.2

lemma WPoly.zero : WPoly 0 := fun d hd => absurd (by simp) hd

lemma WPoly.add {P Q : P2} (hP : WPoly P) (hQ : WPoly Q) : WPoly (P + Q) := by
  intro d hd
  have hd' : P.coeff d + Q.coeff d ≠ 0 := by simpa using hd
  by_cases h1 : P.coeff d = 0
  · rw [h1, zero_add] at hd'; exact hQ d hd'
  · exact hP d h1

lemma WPoly.mul {P Q : P2} (hP : WPoly P) (hQ : WPoly Q) : WPoly (P * Q) := by
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
  refine ⟨by omega, fun h => ?_⟩
  have := h3.2 (by omega)
  have := h4.2 (by omega)
  omega

lemma WPoly.const (a : ℂ) : WPoly (MvPolynomial.C a) := by
  intro d hd
  classical
  rw [MvPolynomial.coeff_C] at hd
  by_cases h : 0 = d
  · subst h; simp
  · simp [h] at hd

lemma WPoly.smul {P : P2} (hP : WPoly P) (a : ℂ) : WPoly (MvPolynomial.C a * P) := (WPoly.const a).mul hP

lemma WPoly.one : WPoly 1 := by simpa using WPoly.const (1 : ℂ)

lemma WPoly.pow {P : P2} (hP : WPoly P) : ∀ m : ℕ, WPoly (P ^ m)
  | 0 => by simpa using WPoly.one
  | m + 1 => by rw [pow_succ]; exact (WPoly.pow hP m).mul hP

lemma WPoly.sum {ι : Type*} (s : Finset ι) {F : ι → P2} (h : ∀ i ∈ s, WPoly (F i)) : WPoly (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WPoly.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The monomial `a h^n v^k`. -/
noncomputable def wmono (n k : ℕ) (a : ℂ) : P2 := MvPolynomial.C a * X 0 ^ n * X 1 ^ k

lemma wev_wmono (h v : ℝ) (n k : ℕ) (a : ℂ) : wev h v (wmono n k a) = a * (h : ℂ) ^ n * (v : ℂ) ^ k := by
  simp [wev, wmono]

lemma wmono_eq (n k : ℕ) (a : ℂ) : wmono n k a = MvPolynomial.monomial (Finsupp.single 0 n + Finsupp.single 1 k) a := by
  rw [wmono, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul]
  simp

lemma WPoly.wmono {n k : ℕ} (hk : k ≤ 3 * n) (hk1 : k = 0 → n = 0) (a : ℂ) : WPoly (wmono n k a) := by
  classical
  intro d hd
  rw [wmono_eq, MvPolynomial.coeff_monomial] at hd
  by_cases h : Finsupp.single 0 n + Finsupp.single 1 k = d
  · subst h; simpa using ⟨hk, hk1⟩
  · simp [h] at hd

lemma wev_C (h v : ℝ) (a : ℂ) : wev h v (MvPolynomial.C a) = a := by simp [wev]

lemma wev_eq (h v : ℝ) (P : P2) :
    wev h v P = ∑ d ∈ P.support, P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) := by
  unfold wev
  rw [MvPolynomial.eval_eq']
  simp [Fin.prod_univ_two]

lemma norm_mon_le {k0 h v : ℝ} (hr : WReg k0 h v) {d : Fin 2 →₀ ℕ} (hd : d 1 ≤ 3 * d 0) :
    ‖(h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)‖ ≤ wx h v ^ (d 0) := by
  have hh := hr.1
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hh]
  have h1 : |v| ^ (d 1) ≤ (1 + |v|) ^ (d 1) := pow_le_pow_left₀ (abs_nonneg v) (by linarith) _
  have h2 : (1 + |v|) ^ (d 1) ≤ (1 + |v|) ^ (3 * d 0) := pow_le_pow_right₀ (by linarith [abs_nonneg v]) hd
  have : wx h v ^ (d 0) = h ^ (d 0) * (1 + |v|) ^ (3 * d 0) := by
    unfold wx; rw [mul_pow, ← pow_mul, mul_comm 3 (d 0)]
  rw [this]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

/-- Sum of the absolute values of the coefficients. -/
noncomputable def cnorm (P : P2) : ℝ := ∑ d ∈ P.support, ‖P.coeff d‖

lemma cnorm_nonneg (P : P2) : 0 ≤ cnorm P := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_wev_le {P : P2} (hP : WPoly P) {k0 h v : ℝ} (hr : WReg k0 h v) :
    ‖wev h v P‖ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * wx h v ^ (d 0) := by
  rw [wev_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_mon_le hr (hP d (by simpa using hd)).1) (norm_nonneg _)

lemma norm_wev_le_cnorm {P : P2} (hP : WPoly P) {k0 h v : ℝ} (hr : WReg k0 h v) (hk0 : k0 ≤ 1) :
    ‖wev h v P‖ ≤ cnorm P := by
  refine (norm_wev_le hP hr).trans (Finset.sum_le_sum fun d _ => ?_)
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  calc ‖P.coeff d‖ * wx h v ^ (d 0) ≤ ‖P.coeff d‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (norm_nonneg _)
    _ = _ := mul_one _

lemma norm_wev_le_x {P : P2} (hP : WPoly P) (h0 : MvPolynomial.constantCoeff P = 0) {k0 h v : ℝ}
    (hr : WReg k0 h v) (hk0 : k0 ≤ 1) : ‖wev h v P‖ ≤ cnorm P * wx h v := by
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  refine (norm_wev_le hP hr).trans ?_
  rw [cnorm, Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  have hdc : P.coeff d ≠ 0 := by simpa using hd
  have hd0 : 1 ≤ d 0 := by
    by_contra hcon
    have h0' : d 0 = 0 := by omega
    have h1' : d 1 = 0 := by have := (hP d hdc).1; omega
    have : d = 0 := by ext i; fin_cases i <;> simp [h0', h1']
    subst this
    exact hdc (by simpa [MvPolynomial.constantCoeff_eq] using h0)
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hx0 hx1 (by omega)) (norm_nonneg _)

/-- `f(h,v) = P(h,v) + O(x^N)` on `WReg k0`, `P` a weighted polynomial with constant term `a0`. -/
def WExp (N : ℕ) (k0 : ℝ) (a0 : ℂ) (f : ℝ → ℝ → ℂ) : Prop :=
  ∃ (P : P2) (C : ℝ), WPoly P ∧ MvPolynomial.constantCoeff P = a0 ∧ 0 ≤ C ∧
    ∀ h v : ℝ, WReg k0 h v → ‖f h v - wev h v P‖ ≤ C * wx h v ^ N

namespace WExp

variable {N : ℕ} {k0 : ℝ} {a0 b0 : ℂ} {f g : ℝ → ℝ → ℂ}

lemma const (a : ℂ) : WExp N k0 a (fun _ _ => a) :=
  ⟨MvPolynomial.C a, 0, WPoly.const a, by simp, le_rfl, fun h v _ => by simp [wev_C]⟩

lemma congr (hf : WExp N k0 a0 f) (hfg : ∀ h v, WReg k0 h v → f h v = g h v) : WExp N k0 a0 g := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  exact ⟨P, C, hP, hc, hC, fun h v hr => by rw [← hfg h v hr]; exact hb h v hr⟩

lemma add (hf : WExp N k0 a0 f) (hg : WExp N k0 b0 g) : WExp N k0 (a0 + b0) (fun h v => f h v + g h v) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  obtain ⟨Q, D, hQ, hd, hD, hb'⟩ := hg
  refine ⟨P + Q, C + D, hP.add hQ, by simp [hc, hd], by positivity, fun h v hr => ?_⟩
  have e : f h v + g h v - wev h v (P + Q) = (f h v - wev h v P) + (g h v - wev h v Q) := by
    rw [map_add]; ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hb h v hr) (hb' h v hr))

lemma mul (hk0 : k0 ≤ 1) (hf : WExp N k0 a0 f) (hg : WExp N k0 b0 g) :
    WExp N k0 (a0 * b0) (fun h v => f h v * g h v) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  obtain ⟨Q, D, hQ, hd, hD, hb'⟩ := hg
  refine ⟨P * Q, C * (cnorm Q + D) + cnorm P * D, hP.mul hQ, by simp [hc, hd], by
    have := cnorm_nonneg P; have := cnorm_nonneg Q; positivity, fun h v hr => ?_⟩
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  have hxN : wx h v ^ N ≤ 1 := pow_le_one₀ hx0 hx1
  have hgn : ‖g h v‖ ≤ cnorm Q + D := by
    have h1 := norm_wev_le_cnorm hQ hr hk0
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
  have hPn := norm_wev_le_cnorm hP hr hk0
  have t1 : ‖f h v - wev h v P‖ * ‖g h v‖ ≤ C * wx h v ^ N * (cnorm Q + D) :=
    mul_le_mul (hb h v hr) hgn (norm_nonneg _) (by positivity)
  have t2 : ‖wev h v P‖ * ‖g h v - wev h v Q‖ ≤ cnorm P * (D * wx h v ^ N) :=
    mul_le_mul hPn (hb' h v hr) (norm_nonneg _) (cnorm_nonneg P)
  nlinarith [t1, t2]

lemma bound {C : ℝ} (hf : ∀ h v, WReg k0 h v → ‖f h v‖ ≤ C * wx h v ^ N) (hC : 0 ≤ C) : WExp N k0 0 f :=
  ⟨0, C, WPoly.zero, by simp, hC, fun h v hr => by simpa using hf h v hr⟩

lemma mono {k1 : ℝ} (hk : k1 ≤ k0) (hf : WExp N k0 a0 f) : WExp N k1 a0 f := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  exact ⟨P, C, hP, hc, hC, fun h v hr => hb h v ⟨hr.1, hr.2.trans hk⟩⟩

lemma neg (hf : WExp N k0 a0 f) : WExp N k0 (-a0) (fun h v => -f h v) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  refine ⟨-P, C, ?_, by simp [hc], hC, fun h v hr => ?_⟩
  · have := (WPoly.const (-1 : ℂ)).mul hP
    simpa using this
  · have e : -f h v - wev h v (-P) = -(f h v - wev h v P) := by rw [map_neg]; ring
    rw [e, norm_neg]; exact hb h v hr

lemma norm_pow_sub_pow_le (a b : ℂ) {K : ℝ} (hK : 1 ≤ K) (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ m * K ^ m * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ ^ m ≤ K ^ m := pow_le_pow_left₀ (norm_nonneg _) ha _
    have hK0 : 0 ≤ K := by linarith
    have h2 : ‖a ^ m - b ^ m‖ * ‖b‖ ≤ (m * K ^ m * ‖a - b‖) * K :=
      mul_le_mul ih hb (norm_nonneg _) (by positivity)
    have h3 : K ^ m ≤ K ^ (m + 1) := pow_le_pow_right₀ hK (Nat.le_succ m)
    have h4 : ‖a‖ ^ m * ‖a - b‖ ≤ K ^ m * ‖a - b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    push_cast
    have h5 : K ^ m * ‖a - b‖ ≤ K ^ (m + 1) * ‖a - b‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    have h6 : (m : ℝ) * K ^ m * ‖a - b‖ * K = m * K ^ (m + 1) * ‖a - b‖ := by ring
    nlinarith [h2, h4, h5, h6]

lemma exp (hk0 : k0 ≤ 1) (hN : 1 ≤ N) (hf : WExp N k0 0 f) :
    WExp N k0 1 (fun h v => Complex.exp (f h v)) := by
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  set K : ℝ := cnorm P + C with hK
  have hK0 : 0 ≤ K := by have := cnorm_nonneg P; positivity
  set K' : ℝ := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  set Q : P2 := ∑ m ∈ Finset.range N, MvPolynomial.C (1 / (m.factorial : ℂ)) * P ^ m with hQ
  have hQp : WPoly Q := WPoly.sum _ fun m _ => (hP.pow m).smul _
  have hQc : MvPolynomial.constantCoeff Q = 1 := by
    rw [hQ, map_sum]
    simp only [map_mul, MvPolynomial.constantCoeff_C, map_pow, hc]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm; simp [zero_pow hm]
    · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hwQ : ∀ h v, wev h v Q = ∑ m ∈ Finset.range N, (1 / (m.factorial : ℂ)) * (wev h v P) ^ m := by
    intro h v; rw [hQ, map_sum]; simp [wev_C]
  set S : ℝ := ∑ m ∈ Finset.range N, (m : ℝ) * K' ^ m / (m.factorial : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨Q, K ^ N * Real.exp K + S * C, hQp, hQc, by positivity, fun h v hr => ?_⟩
  have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
  have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
  have hxN : wx h v ^ N ≤ wx h v := pow_le_of_le_one hx0 hx1 (by omega)
  have hPx := norm_wev_le_x hP hc hr hk0
  have hPc := norm_wev_le_cnorm hP hr hk0
  have hdiff := hb h v hr
  have hfn : ‖f h v‖ ≤ K * wx h v := by
    have : ‖f h v‖ ≤ ‖wev h v P‖ + ‖f h v - wev h v P‖ := by
      calc ‖f h v‖ = ‖wev h v P + (f h v - wev h v P)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith [mul_le_mul_of_nonneg_left hxN hC]
  have hfK : ‖f h v‖ ≤ K' := by nlinarith [mul_le_mul_of_nonneg_left hx1 hK0]
  have hPK : ‖wev h v P‖ ≤ K' := by have := cnorm_nonneg P; linarith
  -- split
  have e : Complex.exp (f h v) - wev h v Q =
      (Complex.exp (f h v) - ∑ m ∈ Finset.range N, (f h v) ^ m / (m.factorial : ℂ)) +
        ∑ m ∈ Finset.range N, (1 / (m.factorial : ℂ)) * ((f h v) ^ m - (wev h v P) ^ m) := by
    have e1 : ∑ m ∈ Finset.range N, (1 / (m.factorial : ℂ)) * ((f h v) ^ m - (wev h v P) ^ m) =
        ∑ m ∈ Finset.range N, (f h v) ^ m / (m.factorial : ℂ) -
          ∑ m ∈ Finset.range N, (1 / (m.factorial : ℂ)) * (wev h v P) ^ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hwQ, e1]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 : ‖Complex.exp (f h v) - ∑ m ∈ Finset.range N, (f h v) ^ m / (m.factorial : ℂ)‖ ≤
      K ^ N * Real.exp K * wx h v ^ N := by
    refine (Complex.norm_exp_sub_sum_le_norm_mul_exp (f h v) N).trans ?_
    have h1 : ‖f h v‖ ^ N ≤ (K * wx h v) ^ N := pow_le_pow_left₀ (norm_nonneg _) hfn _
    have h2 : Real.exp ‖f h v‖ ≤ Real.exp K := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx1 hK0])
    calc ‖f h v‖ ^ N * Real.exp ‖f h v‖ ≤ (K * wx h v) ^ N * Real.exp K :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = K ^ N * Real.exp K * wx h v ^ N := by rw [mul_pow]; ring
  have b2 : ‖∑ m ∈ Finset.range N, (1 / (m.factorial : ℂ)) * ((f h v) ^ m - (wev h v P) ^ m)‖ ≤ S * C * wx h v ^ N := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ m ∈ Finset.range N, ‖(1 / (m.factorial : ℂ)) * ((f h v) ^ m - (wev h v P) ^ m)‖ ≤
        ((m : ℝ) * K' ^ m / (m.factorial : ℝ)) * (C * wx h v ^ N) := by
      intro m _
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      have := norm_pow_sub_pow_le (f h v) (wev h v P) hK'1 hfK hPK m
      have h3 : ‖(f h v) ^ m - (wev h v P) ^ m‖ ≤ m * K' ^ m * (C * wx h v ^ N) :=
        this.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
      calc 1 / (m.factorial : ℝ) * ‖(f h v) ^ m - (wev h v P) ^ m‖
          ≤ 1 / (m.factorial : ℝ) * (m * K' ^ m * (C * wx h v ^ N)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, hS]; ring
  nlinarith [b1, b2]

lemma abs_mul_le_wx {h v : ℝ} (hh : 0 < h) : h * |v| ≤ wx h v := by
  unfold wx
  have : |v| ≤ (1 + |v|) ^ 3 := by
    have h1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    calc |v| ≤ 1 + |v| := by linarith
      _ = (1 + |v|) ^ 1 := (pow_one _).symm
      _ ≤ (1 + |v|) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  exact mul_le_mul_of_nonneg_left this hh.le

lemma pow_abs_le_wx {h : ℝ} (v : ℝ) (hh : 0 < h) (m n : ℕ) (hmn : m ≤ 3 * n) :
    h ^ n * |v| ^ m ≤ wx h v ^ n := by
  have h1 : |v| ^ m ≤ (1 + |v|) ^ m := pow_le_pow_left₀ (abs_nonneg v) (by linarith) _
  have h2 : (1 + |v|) ^ m ≤ (1 + |v|) ^ (3 * n) := pow_le_pow_right₀ (by linarith [abs_nonneg v]) hmn
  have : wx h v ^ n = h ^ n * (1 + |v|) ^ (3 * n) := by
    unfold wx; rw [mul_pow, ← pow_mul, mul_comm 3 n]
  rw [this]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

lemma of_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hN : 1 ≤ N) (hk : 0 < k0) :
    WExp N k0 (g 0) (fun h v => g (h * v)) := by
  obtain ⟨C, hC, hT⟩ := taylor_poly_bound hg (N - 1) hk
  set gl : ℕ → ℂ := fun l => iteratedDeriv l g 0 / (l.factorial : ℂ) with hgl
  set P : P2 := ∑ l ∈ Finset.range N, wmono l l (gl l) with hP
  have hPp : WPoly P := WPoly.sum _ fun l _ => WPoly.wmono (by omega) (fun h => h) _
  refine ⟨P, C, hPp, ?_, hC, fun h v hr => ?_⟩
  · rw [hP, map_sum]
    rw [Finset.sum_eq_single 0]
    · simp [wmono, hgl]
    · intro l _ hl; simp [wmono, zero_pow hl]
    · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
  · have hwP : wev h v P = ∑ l ∈ Finset.range N, (gl l) * ((h * v : ℝ) : ℂ) ^ l := by
      rw [hP, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [wev_wmono]; push_cast; ring
    have hz : |h * v| ≤ k0 := by
      rw [abs_mul, abs_of_pos hr.1]; exact (abs_mul_le_wx hr.1).trans hr.2
    have := hT (h * v) hz
    have hNN : N - 1 + 1 = N := by omega
    rw [hNN] at this
    rw [hwP]
    refine this.trans ?_
    rw [abs_mul, abs_of_pos hr.1, mul_pow, mul_comm C, mul_assoc]
    have := pow_abs_le_wx v hr.1 N N (by omega)
    nlinarith [mul_le_mul_of_nonneg_left this hC]

lemma wmono_fun {n k : ℕ} (hk : k ≤ 3 * n) (hk1 : k = 0 → n = 0) (hn : 1 ≤ n) (a : ℂ) :
    WExp N k0 0 (fun h v => a * (h : ℂ) ^ n * (v : ℂ) ^ k) := by
  refine ⟨wmono n k a, 0, WPoly.wmono hk hk1 a, ?_, le_rfl, fun h v _ => ?_⟩
  · simp [wmono, zero_pow (by omega : n ≠ 0)]
  · simp [wev_wmono]

lemma of_smooth_inv_sq {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hN : 1 ≤ N) (hk : 0 < k0)
    (h0 : ∀ l < 3, iteratedDeriv l g 0 = 0) :
    WExp N k0 0 (fun h v => (((h ^ 2)⁻¹ : ℝ) : ℂ) * g (h * v)) := by
  obtain ⟨C, hC, hT⟩ := taylor_poly_bound hg (N + 1) hk
  set gl : ℕ → ℂ := fun l => iteratedDeriv l g 0 / (l.factorial : ℂ) with hgl
  have hgl0 : ∀ l < 3, gl l = 0 := fun l hl => by simp [hgl, h0 l hl]
  set P : P2 := ∑ l ∈ Finset.Icc 3 (N + 1), wmono (l - 2) l (gl l) with hP
  have hPp : WPoly P := WPoly.sum _ fun l hl => WPoly.wmono (by have := (Finset.mem_Icc.mp hl).1; omega) (fun h => by have := (Finset.mem_Icc.mp hl).1; omega) _
  refine ⟨P, C, hPp, ?_, hC, fun h v hr => ?_⟩
  · rw [hP, map_sum]
    refine Finset.sum_eq_zero fun l hl => ?_
    have := (Finset.mem_Icc.mp hl).1
    simp [wmono, zero_pow (by omega : l - 2 ≠ 0)]
  · have hh := hr.1
    have hwP : wev h v P = ∑ l ∈ Finset.Icc 3 (N + 1), (((h ^ 2)⁻¹ : ℝ) : ℂ) * ((gl l) * ((h * v : ℝ) : ℂ) ^ l) := by
      rw [hP, map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl3 := (Finset.mem_Icc.mp hl).1
      rw [wev_wmono]
      have hpow : (h : ℂ) ^ l = (h : ℂ) ^ (l - 2) * (h : ℂ) ^ 2 := by rw [← pow_add]; congr 1; omega
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      push_cast
      rw [mul_pow, hpow]
      field_simp
    have hz : |h * v| ≤ k0 := by
      rw [abs_mul, abs_of_pos hh]; exact (abs_mul_le_wx hh).trans hr.2
    have hT' := hT (h * v) hz
    have hsub : Finset.Icc 3 (N + 1) ⊆ Finset.range (N + 1 + 1) := fun l hl => by
      have := (Finset.mem_Icc.mp hl).2; exact Finset.mem_range.mpr (by omega)
    have hsum : ∑ l ∈ Finset.range (N + 1 + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l =
        ∑ l ∈ Finset.Icc 3 (N + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l := by
      symm
      refine Finset.sum_subset hsub fun l hl hnl => ?_
      have : l < 3 := by
        by_contra hcon
        exact hnl (Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hl; omega⟩)
      simp [hgl0 l this]
    have e : (((h ^ 2)⁻¹ : ℝ) : ℂ) * g (h * v) - wev h v P =
        (((h ^ 2)⁻¹ : ℝ) : ℂ) * (g (h * v) - ∑ l ∈ Finset.range (N + 1 + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l) := by
      rw [hwP, hsum, ← Finset.mul_sum]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hpow : (h ^ 2)⁻¹ * (C * |h * v| ^ (N + 1 + 1)) = C * (h ^ N * |v| ^ (N + 2)) := by
      rw [abs_mul, abs_of_pos hh, mul_pow]
      field_simp
      ring
    calc (h ^ 2)⁻¹ * ‖g (h * v) - ∑ l ∈ Finset.range (N + 1 + 1), (gl l) * ((h * v : ℝ) : ℂ) ^ l‖
        ≤ (h ^ 2)⁻¹ * (C * |h * v| ^ (N + 1 + 1)) := mul_le_mul_of_nonneg_left hT' (by positivity)
      _ = C * (h ^ N * |v| ^ (N + 2)) := hpow
      _ ≤ C * wx h v ^ N := mul_le_mul_of_nonneg_left (pow_abs_le_wx v hh (N + 2) N (by omega)) hC

/-- Truncation at weight `< N`: a finite list of monomials `a_d h^{d 0} v^{d 1}`, `1 ≤ d 0 < N`, `d 1 ≤ 3 d 0`. -/
theorem expansion (hk0 : k0 ≤ 1) (hf : WExp N k0 0 f) :
    ∃ (S : Finset (Fin 2 →₀ ℕ)) (a : (Fin 2 →₀ ℕ) → ℂ) (C : ℝ),
      (∀ d ∈ S, 1 ≤ d 0 ∧ d 0 < N ∧ d 1 ≤ 3 * d 0 ∧ 1 ≤ d 1) ∧ 0 ≤ C ∧
      ∀ h v : ℝ, WReg k0 h v →
        ‖f h v - ∑ d ∈ S, a d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖ ≤ C * wx h v ^ N := by
  classical
  obtain ⟨P, C, hP, hc, hC, hb⟩ := hf
  refine ⟨P.support.filter (fun d => d 0 < N), fun d => P.coeff d, C + cnorm P, ?_, by
    have := cnorm_nonneg P; positivity, fun h v hr => ?_⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hdc : P.coeff d ≠ 0 := by simpa using hd.1
    have hd1 := (hP d hdc).1
    have hd2 := (hP d hdc).2
    have hd0 : 1 ≤ d 0 := by
      by_contra hcon
      have h0' : d 0 = 0 := by omega
      have h1' : d 1 = 0 := by omega
      have : d = 0 := by ext i; fin_cases i <;> simp [h0', h1']
      subst this
      exact hdc (by simpa [MvPolynomial.constantCoeff_eq] using hc)
    refine ⟨hd0, hd.2, hd1, ?_⟩
    by_contra hcon
    have := hd2 (by omega)
    omega
  · have hx0 : 0 ≤ wx h v := wx_nonneg hr.1
    have hx1 : wx h v ≤ 1 := hr.wx_le.trans hk0
    have hsplit : wev h v P = ∑ d ∈ P.support.filter (fun d => d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) +
        ∑ d ∈ P.support.filter (fun d => ¬ d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) := by
      rw [wev_eq, Finset.sum_filter_add_sum_filter_not]
    have htail : ‖∑ d ∈ P.support.filter (fun d => ¬ d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖ ≤
        cnorm P * wx h v ^ N := by
      refine (norm_sum_le _ _).trans ?_
      rw [cnorm, Finset.sum_mul]
      calc ∑ d ∈ P.support.filter (fun d => ¬ d 0 < N), ‖P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖
          ≤ ∑ d ∈ P.support.filter (fun d => ¬ d 0 < N), ‖P.coeff d‖ * wx h v ^ N := by
            refine Finset.sum_le_sum fun d hd => ?_
            rw [Finset.mem_filter] at hd
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ((norm_mon_le hr (hP d (by simpa using hd.1)).1).trans ?_) (norm_nonneg _)
            exact pow_le_pow_of_le_one hx0 hx1 (by omega)
        _ ≤ ∑ d ∈ P.support, ‖P.coeff d‖ * wx h v ^ N :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    have e : f h v - ∑ d ∈ P.support.filter (fun d => d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) =
        (f h v - wev h v P) + ∑ d ∈ P.support.filter (fun d => ¬ d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1)) := by
      rw [hsplit]; ring
    show ‖f h v - ∑ d ∈ P.support.filter (fun d => d 0 < N), P.coeff d * ((h : ℂ) ^ (d 0) * (v : ℂ) ^ (d 1))‖ ≤ _
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith [hb h v hr, htail]

end WExp

/-- info: 'FormalResearch.SignUncertainty.WExp.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WExp.mul

/-- info: 'FormalResearch.SignUncertainty.WExp.exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WExp.exp

/-- info: 'FormalResearch.SignUncertainty.WExp.of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WExp.of_smooth

/-- info: 'FormalResearch.SignUncertainty.WExp.of_smooth_inv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WExp.of_smooth_inv_sq

/-- info: 'FormalResearch.SignUncertainty.WExp.expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WExp.expansion

end FormalResearch.SignUncertainty

module

public import FormalResearch.Special.DiscreteAiryKappaInvariant
public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# A priori bound for the Hahn chain on the left of the Airy window (plan K1, step M-c)

The closed-form Hahn recurrence (`hrAk 1 0 M σ h`, `hrCk 1 0 1 x M σ h`; for `M, σ ∈ ℤ` it is the rank recurrence of the
actual Wigner `3j` chain, `hahn_class_chain`) in the oscillatory band: with `e = ẽ(q_max)` and `x < e ≤ 1`,
`a_k = ½ r_k √(1-(kh)²) ≥ ½(1-β/k²) e`, `c_k = x - Mσ/(k(k+1))`, so `2a_k - |c_k| ≥ (e - x)/2` for `k ≥ K`.  The
adiabatic invariant of `DiscreteAiryKappaInvariant` then varies by the factor `e^{O(1)}` over the *whole* band
`K ≤ k ≤ k₁` (`|Δa| + |Δc| ≲ β/k² + 9h/(4x)`, whose sum is `≤ β + 2|Mσ| + 9/(4x)`), and the finitely many sites
`max(|M|,|σ|) ≤ k < K` are controlled by the backward recursion (`a_k ≥ x/(2K²)` there).

* `kl_hahn_left`: **for every solution `Y` of the rows `1 ≤ k ≤ k₁ - 1` with `Y_k = 0` for `k < max(|M|,|σ|)` and
  `(k₁ h)² ≤ 1 - e²`: `Y_k² ≤ C (Y_{k₁}² + Y_{k₁-1}²)` for every `k ≤ k₁`**, with `K, C` depending on `(M, σ, x, e)` only
  (not on `h`, `k₁`, `Y`).

**Claim class: proved**, explicit constants (`kl_const`).  This is the a priori bound for the part of the `3j` chain to the
left of the macroscopic Airy window (`DiscreteAiryOsc*`): it holds on the entire band including `k = O(1)` (the left
Hahn edge), with no WKB phase or amplitude input.  Mpmath check of the invariant on the actual chain: see
`DiscreteAiryKappaInvariant`.

**Not formalised.**  The sharp (`1 + o(1)`) amplitude on the left; the half-integer shifted chain; Racah.
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma kl_hrA (M σ h : ℝ) (k : ℤ) :
    hrAk 1 0 M σ h k = 1 / 2 * rr M σ (k : ℝ) * Real.sqrt (1 - ((k : ℝ) * h) ^ 2) := by
  unfold hrAk etilde
  congr 2
  ring_nf

lemma kl_hrC (x M σ h : ℝ) (k : ℤ) :
    hrCk 1 0 1 x M σ h k = x - M * σ / ((k : ℝ) * ((k : ℝ) + 1)) := by
  unfold hrCk hrB
  simp

/-- The Hahn left-end bound constants. -/
noncomputable def kl_beta (M σ : ℝ) : ℝ := M ^ 2 + σ ^ 2 + 1 / 3

/-- `|r_k - 1| ≤ β / k²` and `r_k ≤ 3/2` for `k ≥ 2β`, `k ≥ max(|M|, |σ|)`. -/
lemma kl_rr_close {M σ k : ℝ} (hk : 1 ≤ k) (hM : M ^ 2 ≤ k ^ 2) (hσ : σ ^ 2 ≤ k ^ 2) :
    |rr M σ k - 1| ≤ kl_beta M σ / k ^ 2 := rr_sub_one_le hk hM hσ

/-- `E_k = √(1 - (kh)²)` lies in `[e, 1]` on the band. -/
lemma kl_E_bounds {e t : ℝ} (htb : t ^ 2 ≤ 1 - e ^ 2) :
    e ≤ Real.sqrt (1 - t ^ 2) ∧ Real.sqrt (1 - t ^ 2) ≤ 1 := by
  constructor
  · apply Real.le_sqrt_of_sq_le; linarith
  · apply Real.sqrt_le_one.2; nlinarith [sq_nonneg t]

/-- Increment of `E`: `|E_{k+1} - E_k| ≤ 3h/e₀` where `E_k ≥ e₀ > 0`, `(k+1) h ≤ 1`, `k ≥ 1`. -/
lemma kl_E_diff {h k e0 : ℝ} (hh : 0 < h) (hk : 1 ≤ k) (he0 : 0 < e0)
    (hk1 : (k + 1) * h ≤ 1) (hE : e0 ≤ Real.sqrt (1 - (k * h) ^ 2)) :
    |Real.sqrt (1 - ((k + 1) * h) ^ 2) - Real.sqrt (1 - (k * h) ^ 2)| ≤ 3 * h / e0 := by
  set E := Real.sqrt (1 - (k * h) ^ 2) with hEdef
  set E' := Real.sqrt (1 - ((k + 1) * h) ^ 2) with hE'def
  have hk0 : 0 < k := by linarith
  have h1 : (k * h) ^ 2 ≤ 1 := by nlinarith [mul_pos hk0 hh]
  have h2 : ((k + 1) * h) ^ 2 ≤ 1 := by nlinarith [mul_pos (by linarith : (0 : ℝ) < k + 1) hh]
  have hE2 : E ^ 2 = 1 - (k * h) ^ 2 := Real.sq_sqrt (by linarith)
  have hE'2 : E' ^ 2 = 1 - ((k + 1) * h) ^ 2 := Real.sq_sqrt (by linarith)
  have hE'0 : 0 ≤ E' := Real.sqrt_nonneg _
  have hE0 : 0 < E := lt_of_lt_of_le he0 hE
  have hdiff : E ^ 2 - E' ^ 2 = (2 * k + 1) * h ^ 2 := by rw [hE2, hE'2]; ring
  have hfac : (E - E') * (E + E') = (2 * k + 1) * h ^ 2 := by nlinarith [hdiff]
  have hsum : e0 ≤ E + E' := by linarith
  have hkh : k * h ≤ 1 := by nlinarith
  have hnn : 0 ≤ E - E' := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hk0 hh, sq_nonneg h, mul_pos (mul_pos hk0 hh) hh]
  have hbound : (2 * k + 1) * h ^ 2 ≤ 3 * h := by nlinarith [mul_pos hk0 hh]
  rw [abs_sub_comm, abs_of_nonneg hnn]
  rw [le_div_iff₀ he0]
  nlinarith [mul_le_mul_of_nonneg_left hsum hnn]

/-- Margin from the bounds on `r`, `E` (plain real arithmetic). -/
lemma kl_margin {r E e x β μ k cabs : ℝ} (hk0 : 0 < k) (he0 : 0 ≤ e) (hβ0 : 0 ≤ β) (hrb : 1 - β / k ^ 2 ≤ r)
    (hE : e ≤ E) (hE1 : E ≤ 1) (hcabs : cabs ≤ x + μ / k ^ 2) (h4 : (β + μ) / k ^ 2 ≤ (e - x) / 2) :
    (e - x) / 2 ≤ r * E - cabs := by
  have hE0 : 0 ≤ E := le_trans he0 hE
  have hk2 : 0 < k ^ 2 := by positivity
  have h2 : (1 - β / k ^ 2) * E ≤ r * E := mul_le_mul_of_nonneg_right hrb hE0
  have h3 : β / k ^ 2 * E ≤ β / k ^ 2 := mul_le_of_le_one_right (by positivity) hE1
  have h5 : β / k ^ 2 + μ / k ^ 2 = (β + μ) / k ^ 2 := by ring
  nlinarith

/-- The diagonal bound `|c| ≤ x + μ/k²`. -/
lemma kl_cabs {M σ x k : ℝ} (hx : 0 < x) (hk0 : 0 < k) :
    |x - M * σ / (k * (k + 1))| ≤ x + |M * σ| / k ^ 2 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have h1 : |M * σ / (k * (k + 1))| ≤ |M * σ| / k ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < k * (k + 1))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk2 (by nlinarith)
  calc |x - M * σ / (k * (k + 1))| ≤ |x| + |M * σ / (k * (k + 1))| := abs_sub _ _
    _ ≤ x + |M * σ| / k ^ 2 := by rw [abs_of_pos hx]; linarith

/-- The `c`-increment `|c_{k+1} - c_k| ≤ 2|Mσ|/k²`. -/
lemma kl_cdiff {M σ x k : ℝ} (hk0 : 0 < k) :
    |(x - M * σ / ((k + 1) * (k + 1 + 1))) - (x - M * σ / (k * (k + 1)))| ≤ 2 * |M * σ| / k ^ 2 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have e1 : (x - M * σ / ((k + 1) * (k + 1 + 1))) - (x - M * σ / (k * (k + 1))) =
      M * σ * (2 / (k * (k + 1) * (k + 2))) := by field_simp; ring
  rw [e1, abs_mul, abs_of_pos (by positivity : 0 < 2 / (k * (k + 1) * (k + 2)))]
  have : 2 / (k * (k + 1) * (k + 2)) ≤ 2 / k ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hk2
    nlinarith [mul_pos hk0 hk0]
  calc |M * σ| * (2 / (k * (k + 1) * (k + 2))) ≤ |M * σ| * (2 / k ^ 2) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 2 * |M * σ| / k ^ 2 := by ring

/-- The `a`-increment from the `r`- and `E`-increments (plain arithmetic). -/
lemma kl_adiff {r r' E E' t d : ℝ} (hr : r ≤ 3 / 2) (hE'0 : 0 ≤ E') (hE'1 : E' ≤ 1) (hr0 : 0 < r)
    (hrr : |r' - r| ≤ 2 * t) (hEd : |E' - E| ≤ d) :
    |1 / 2 * r' * E' - 1 / 2 * r * E| ≤ t + 3 / 4 * d := by
  have e1 : 1 / 2 * r' * E' - 1 / 2 * r * E = 1 / 2 * ((r' - r) * E') + 1 / 2 * (r * (E' - E)) := by ring
  rw [e1]
  have t2 : |(r' - r) * E'| ≤ 2 * t := by
    rw [abs_mul, abs_of_nonneg hE'0]
    calc _ ≤ |r' - r| * 1 := mul_le_mul_of_nonneg_left hE'1 (abs_nonneg _)
      _ ≤ _ := by linarith
  have t3 : |r * (E' - E)| ≤ 3 / 2 * d := by
    rw [abs_mul, abs_of_pos hr0]
    exact mul_le_mul hr hEd (abs_nonneg _) (by norm_num)
  calc _ ≤ |1 / 2 * ((r' - r) * E')| + |1 / 2 * (r * (E' - E))| := abs_add_le _ _
    _ = 1 / 2 * |(r' - r) * E'| + 1 / 2 * |r * (E' - E)| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ t + 3 / 4 * d := by linarith

/-- The `B`-bound `c² + a² ≤ (45/x²) a'²` from `|c| ≤ 2a`, `a ≤ 3/4`, `a' ≥ x/4`. -/
lemma kl_Bbound {c a a' x : ℝ} (hx : 0 < x) (hc : |c| ≤ 2 * a) (ha : a ≤ 3 / 4) (ha0 : 0 ≤ a)
    (ha' : x / 4 ≤ a') : c ^ 2 + a ^ 2 ≤ 45 / x ^ 2 * a' ^ 2 := by
  have hsq : c ^ 2 ≤ (2 * a) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h1 : c ^ 2 + a ^ 2 ≤ 5 * a ^ 2 := by nlinarith
  have h2 : 5 * a ^ 2 ≤ 5 * (3 / 4) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 ha 2) (by norm_num)
  have h3 : (x / 4) ^ 2 ≤ a' ^ 2 := pow_le_pow_left₀ (by positivity) ha' 2
  have h4 : 45 / x ^ 2 * (x / 4) ^ 2 = 45 / 16 := by field_simp; ring
  calc _ ≤ 5 * (3 / 4) ^ 2 := h1.trans h2
    _ = 45 / x ^ 2 * (x / 4) ^ 2 := by rw [h4]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **Coefficient facts in the band** (real form, `k` the rank): for `k ≥ 1`, `k ≥ 2β`, `k ≥ 2(β + |Mσ|)/(e - x)`,
`M², σ² ≤ k²`, `x < e ≤ 1` and `((k+1)h)² ≤ 1 - e²`, with `a_j = ½ r_j E_j`, `c_j = x - Mσ/(j(j+1))`:
margin `2a_k - |c_k| ≥ (e-x)/2`, `0 < a_k ≤ 3/4`, `a_{k+1} ≥ x/4`, `c_k² + a_k² ≤ (45/x²) a_{k+1}²`,
`|a_{k+1} - a_k| + |c_{k+1} - c_k| ≤ (β + 2|Mσ|)/k² + 9h/(4x)`. -/
lemma kl_coef_facts {M σ x e h k : ℝ} (hx : 0 < x) (hxe : x < e) (he1 : e ≤ 1) (hh : 0 < h) (hk1 : 1 ≤ k)
    (hβ : 2 * kl_beta M σ ≤ k) (hγ : 2 * (kl_beta M σ + |M * σ|) / (e - x) ≤ k) (hM : M ^ 2 ≤ k ^ 2)
    (hσ : σ ^ 2 ≤ k ^ 2) (hband : ((k + 1) * h) ^ 2 ≤ 1 - e ^ 2) :
    (e - x) / 2 ≤ rr M σ k * Real.sqrt (1 - (k * h) ^ 2) - |x - M * σ / (k * (k + 1))| ∧
    0 < rr M σ k * Real.sqrt (1 - (k * h) ^ 2) ∧ 1 / 2 * rr M σ k * Real.sqrt (1 - (k * h) ^ 2) ≤ 3 / 4 ∧
    x / 4 ≤ 1 / 2 * rr M σ (k + 1) * Real.sqrt (1 - ((k + 1) * h) ^ 2) ∧
    (x - M * σ / (k * (k + 1))) ^ 2 + (1 / 2 * rr M σ k * Real.sqrt (1 - (k * h) ^ 2)) ^ 2 ≤
      45 / x ^ 2 * (1 / 2 * rr M σ (k + 1) * Real.sqrt (1 - ((k + 1) * h) ^ 2)) ^ 2 ∧
    |1 / 2 * rr M σ (k + 1) * Real.sqrt (1 - ((k + 1) * h) ^ 2) - 1 / 2 * rr M σ k * Real.sqrt (1 - (k * h) ^ 2)| +
      |(x - M * σ / ((k + 1) * (k + 1 + 1))) - (x - M * σ / (k * (k + 1)))| ≤
      (kl_beta M σ + 2 * |M * σ|) / k ^ 2 + 9 * h / (4 * x) := by
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k ^ 2 := by positivity
  have hβ0 : 0 < kl_beta M σ := by unfold kl_beta; positivity
  have hγ0 : 0 < e - x := by linarith
  have hμ0 : 0 ≤ |M * σ| := abs_nonneg _
  have hbandk : (k * h) ^ 2 ≤ 1 - e ^ 2 := by
    have : (k * h) ^ 2 ≤ ((k + 1) * h) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); nlinarith
    linarith
  obtain ⟨hEe, hE1⟩ := kl_E_bounds (e := e) hbandk
  obtain ⟨hE'e, hE'1⟩ := kl_E_bounds (e := e) hband
  have he0 : 0 < e := by linarith
  have hrc := kl_rr_close hk1 hM hσ
  have hrc' := kl_rr_close (M := M) (σ := σ) (k := k + 1) (by linarith) (by nlinarith) (by nlinarith)
  have hEd := kl_E_diff (h := h) (k := k) (e0 := x) hh hk1 hx (by nlinarith) (by linarith)
  have hβk : kl_beta M σ / k ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hk2]; nlinarith
  have hβk' : kl_beta M σ / (k + 1) ^ 2 ≤ kl_beta M σ / k ^ 2 := by
    apply div_le_div_of_nonneg_left hβ0.le hk2
    nlinarith
  have hcabs := kl_cabs (M := M) (σ := σ) hx hk0
  have hcd := kl_cdiff (M := M) (σ := σ) (x := x) hk0
  have h4 : (kl_beta M σ + |M * σ|) / k ^ 2 ≤ (e - x) / 2 := by
    have h5 : (kl_beta M σ + |M * σ|) / k ^ 2 ≤ (kl_beta M σ + |M * σ|) / k := by
      apply div_le_div_of_nonneg_left (by positivity) hk0
      nlinarith
    refine h5.trans ?_
    rw [div_le_iff₀ hk0]
    have := (div_le_iff₀ hγ0).1 hγ
    nlinarith
  generalize rr M σ k = r at *
  generalize rr M σ (k + 1) = r' at *
  generalize Real.sqrt (1 - (k * h) ^ 2) = E at *
  generalize Real.sqrt (1 - ((k + 1) * h) ^ 2) = E' at *
  generalize kl_beta M σ = β at *
  generalize |M * σ| = μ at *
  have hr1 := abs_le.1 hrc
  have hr1' := abs_le.1 hrc'
  have hrhi : r ≤ 3 / 2 := by linarith [hr1.2]
  have hr0 : 0 < r := by linarith [hr1.1]
  have hr'lo : 1 / 2 ≤ r' := by linarith [hr1'.1]
  have hmarg := kl_margin (r := r) (E := E) hk0 he0.le hβ0.le (by linarith [hr1.1]) hEe hE1 hcabs h4
  have hapos : 0 < r * E := by
    have : 0 ≤ |x - M * σ / (k * (k + 1))| := abs_nonneg _
    linarith
  have hE0 : 0 ≤ E := le_trans he0.le hEe
  have ha34 : 1 / 2 * r * E ≤ 3 / 4 := by
    have := mul_le_mul hrhi hE1 hE0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hE'0 : 0 ≤ E' := le_trans he0.le hE'e
  have ha'lo : x / 4 ≤ 1 / 2 * r' * E' := by
    have h1 := mul_le_mul_of_nonneg_right hr'lo hE'0
    have h2 : 1 / 4 * E' ≤ 1 / 2 * r' * E' := by linarith
    linarith
  have hcle : |x - M * σ / (k * (k + 1))| ≤ 2 * (1 / 2 * r * E) := by linarith
  refine ⟨hmarg, hapos, ha34, ha'lo, kl_Bbound hx hcle ha34 (by nlinarith) ha'lo, ?_⟩
  have t1 : |r' - r| ≤ 2 * (β / k ^ 2) := by
    have : r' - r = (r' - 1) - (r - 1) := by ring
    rw [this]
    calc _ ≤ |r' - 1| + |r - 1| := abs_sub _ _
      _ ≤ β / (k + 1) ^ 2 + β / k ^ 2 := add_le_add hrc' hrc
      _ ≤ 2 * (β / k ^ 2) := by linarith
  have hda := kl_adiff hrhi hE'0 hE'1 hr0 t1 hEd
  have e9 : β / k ^ 2 + 3 / 4 * (3 * h / x) = β / k ^ 2 + 9 * h / (4 * x) := by field_simp; ring
  calc _ ≤ (β / k ^ 2 + 3 / 4 * (3 * h / x)) + 2 * μ / k ^ 2 := add_le_add hda hcd
    _ = (β + 2 * μ) / k ^ 2 + 9 * h / (4 * x) := by rw [e9]; ring

end FormalResearch.Special

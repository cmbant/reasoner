module

public import FormalResearch.Special.RacahKappaConst
public import FormalResearch.Special.DiscreteAiryKappaLeftBand

/-!
# Coefficient facts of the closed-form chain at the left of the turn, at a real rank `t` (integer and half-integer lattices)

For `q ≤ q_m = q_*/2` the closed-form coefficients `a_t = hrAt P Q a b h t = ½ r_t ẽ((th)²)`, `c_t = hrCt P Q τ x a b h t = τ(x - hrB(t))` at a real rank `t` satisfy, for `t ≥ K₀`, `(t+1/2)h ≤ q_m`:
`2a_t - |c_t| ≥ m₀ > 0` (the margin `ẽ(1 - |u|) ≥ s(q_*² - q_m²)/2` of the oscillatory region, `u = τ(x - β₀q²)/ẽ`, `ẽ² - (x - β₀q²)² = s(q_*² - q²)`), `a_t ≤ 3/4`,
and the increments `|a_{t+1} - a_t| + |c_{t+1} - c_t| ≤ Λ₀(1/t² + h)` (`rl_c_boundT`, `rl_marginT`, `rl_incrT`).  The integer chain is `t = k` (`hrAk h k = hrAt h k`), the half-integer chain is `t = k + ½`
(`hrAkH P Q a b h k = hrAt P Q a b h (k + ½)`); the integer-rank lemmas are the case `t = k` and are not restated.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The key identity `ẽ² - (x - β₀σ)² = s(q_*² - σ)`. -/
lemma rl_key {P Q x qs σ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) :
    (1 - P * σ) * (1 - Q * σ) - (x - Real.sqrt (P * Q) * σ) ^ 2 = rkS P Q x * (qs ^ 2 - σ) := by
  have hb : Real.sqrt (P * Q) ^ 2 = P * Q := Real.sq_sqrt (mul_nonneg hP hQ)
  unfold rkS at hs ⊢
  have : (x - Real.sqrt (P * Q) * σ) ^ 2 = x ^ 2 - 2 * x * Real.sqrt (P * Q) * σ + Real.sqrt (P * Q) ^ 2 * σ ^ 2 := by ring
  rw [this, hb]
  linear_combination hs

/-- The margin `ẽ - |x - β₀q²| ≥ s(q_*² - q_m²)/2`. -/
lemma rl_margin_e {P Q x qs qm q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hspos : 0 < rkS P Q x)
    (hq : q ^ 2 ≤ qm ^ 2) (hqm : qm ^ 2 < qs ^ 2) (hP1 : 0 ≤ 1 - P * q ^ 2) (hQ1 : 0 ≤ 1 - Q * q ^ 2) :
    rkS P Q x * (qs ^ 2 - qm ^ 2) / 2 ≤ etilde P Q (q ^ 2) - |x - Real.sqrt (P * Q) * q ^ 2| := by
  have hk := rl_key (σ := q ^ 2) hP hQ hs
  set e : ℝ := etilde P Q (q ^ 2) with he
  have he2 : e ^ 2 = (1 - P * q ^ 2) * (1 - Q * q ^ 2) := by
    rw [he]; unfold etilde; exact Real.sq_sqrt (mul_nonneg hP1 hQ1)
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have he1 : e ≤ 1 := by
    rw [he]; unfold etilde
    apply Real.sqrt_le_one.2
    exact mul_le_one₀ (by nlinarith only [mul_nonneg hP (sq_nonneg q)]) hQ1 (by nlinarith only [mul_nonneg hQ (sq_nonneg q)])
  set y : ℝ := |x - Real.sqrt (P * Q) * q ^ 2| with hy
  have hy2 : y ^ 2 = (x - Real.sqrt (P * Q) * q ^ 2) ^ 2 := sq_abs _
  have hd : e ^ 2 - y ^ 2 = rkS P Q x * (qs ^ 2 - q ^ 2) := by rw [he2, hy2]; exact hk
  have hdlow : rkS P Q x * (qs ^ 2 - qm ^ 2) ≤ e ^ 2 - y ^ 2 := by
    rw [hd]; exact mul_le_mul_of_nonneg_left (by linarith) hspos.le
  have hy0 : 0 ≤ y := abs_nonneg _
  have hye : y ≤ e := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hspos (by linarith : 0 < qs ^ 2 - qm ^ 2)]
  have hpos : 0 < rkS P Q x * (qs ^ 2 - qm ^ 2) := mul_pos hspos (by linarith)
  nlinarith

/-- `ẽ ≤ 1`. -/
lemma rl_e_le_one {P Q σ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hσ : 0 ≤ σ) (hP1 : 0 ≤ 1 - P * σ) (hQ1 : 0 ≤ 1 - Q * σ) :
    etilde P Q σ ≤ 1 := by
  unfold etilde
  apply Real.sqrt_le_one.2
  exact mul_le_one₀ (by nlinarith only [mul_nonneg hP hσ]) hQ1 (by nlinarith only [mul_nonneg hQ hσ])

/-- `A_t = ½ r_t ẽ((th)²)` at a real rank `t`. -/
noncomputable def hrAt (P Q a b h t : ℝ) : ℝ := 1 / 2 * rr a b t * etilde P Q ((t * h) ^ 2)

/-- `c_t = τ(x - B_t)` at a real rank `t`. -/
noncomputable def hrCt (P Q τ x a b h t : ℝ) : ℝ := τ * (x - hrB (Real.sqrt (P * Q)) a b h t)

/-- The bound for the diagonal coefficient. -/
lemma rl_c_boundT {P Q a b τ x h qm : ℝ} {t : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hh : 0 < h) (hh1 : h ≤ 1) (hk1 : 1 ≤ t)
    (hkq : (t + 1 / 2) * h ≤ qm) :
    |hrCt P Q τ x a b h t| ≤ |x - Real.sqrt (P * Q) * (t * h) ^ 2| +
      (Real.sqrt (P * Q) * qm * h + Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2 * h + |a * b| / t ^ 2) := by
  have hk0 : (1 : ℝ) ≤ t := hk1
  unfold hrCt hrB
  have hτa : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith only [this, abs_nonneg τ]
  rw [abs_mul, hτa, one_mul]
  have e1 : x - (Real.sqrt (P * Q) * (((t + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 +
      a * b / (t * (t + 1))) = (x - Real.sqrt (P * Q) * (t * h) ^ 2) -
      (Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2)) - Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 + a * b / (t * (t + 1))) := by ring
  rw [e1]
  refine (abs_sub _ _).trans ?_
  have hb0 : 0 ≤ Real.sqrt (P * Q) := Real.sqrt_nonneg _
  have t1 : Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2)) ≤ Real.sqrt (P * Q) * qm * h := by
    have : h ^ 2 * (t + 1 / 2) ≤ qm * h := by
      calc h ^ 2 * (t + 1 / 2) = h * ((t + 1 / 2) * h) := by ring
        _ ≤ h * qm := mul_le_mul_of_nonneg_left hkq hh.le
        _ = qm * h := by ring
    calc _ ≤ Real.sqrt (P * Q) * (qm * h) := mul_le_mul_of_nonneg_left this hb0
      _ = _ := by ring
  have t2 : Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 ≤ Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2 * h := by
    have : h ^ 2 ≤ h := by
      calc h ^ 2 = h * h := by ring
        _ ≤ h * 1 := mul_le_mul_of_nonneg_left hh1 hh.le
        _ = h := mul_one _
    have h5 : 0 ≤ Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2 := by positivity
    calc Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 = (Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2) * h ^ 2 := by ring
      _ ≤ (Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2) * h := mul_le_mul_of_nonneg_left this h5
      _ = _ := by ring
  have t3 : |a * b / (t * (t + 1))| ≤ |a * b| / t ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < t * (t + 1))]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    nlinarith only [hk0]
  have u1 := abs_add_le (Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2)) - Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2)
    (a * b / (t * (t + 1)))
  have u2 := abs_sub (Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2))) (Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2)
  have u3 : |Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2))| = Real.sqrt (P * Q) * (h ^ 2 * (t + 1 / 2)) :=
    abs_of_nonneg (by positivity)
  have u4 : |Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2| = Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 :=
    abs_of_nonneg (by positivity)
  linarith only [u1, u2, u3, u4, t1, t2, t3]


/-- The margin at one site: `2a_k - |c_k| ≥ μ₀ - (β + |ab|)/k² - h β₀(q_m + (a²+b²)/2)`, and `a_k ≤ 3/4`. -/
lemma rl_marginT {P Q a b τ x qs h : ℝ} {t : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1)
    (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2) (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk1 : 1 ≤ t) (hka : a ^ 2 ≤ t ^ 2) (hkb : b ^ 2 ≤ t ^ 2)
    (hβk : (a ^ 2 + b ^ 2 + 1 / 3) / t ^ 2 ≤ 1 / 2) (hkq : (t + 1 / 2) * h ≤ qs / 2) :
    rkS P Q x * (qs ^ 2 - (qs / 2) ^ 2) / 2 - (a ^ 2 + b ^ 2 + 1 / 3) / t ^ 2 - |a * b| / t ^ 2 -
        h * (Real.sqrt (P * Q) * (qs / 2) + Real.sqrt (P * Q) * (a ^ 2 + b ^ 2) / 2) ≤
      2 * hrAt P Q a b h t - |hrCt P Q τ x a b h t| ∧ hrAt P Q a b h t ≤ 3 / 4 := by
  have hk0 : (1 : ℝ) ≤ t := hk1
  have hq0 : 0 < t * h := by positivity
  have hqm : t * h ≤ qs / 2 := by nlinarith only [hkq, hh, hk0]
  have hqs' : t * h ≤ qs := by linarith only [hqm, hqs]
  have hP1 : 0 < 1 - P * (t * h) ^ 2 := dlgh_fac hP hα hq0 hqs'
  have hQ1 : 0 < 1 - Q * (t * h) ^ 2 := dlgh_fac hQ hβ hq0 hqs'
  have hq2 : (t * h) ^ 2 ≤ (qs / 2) ^ 2 := pow_le_pow_left₀ hq0.le hqm 2
  have hmg := rl_margin_e (qm := qs / 2) hP hQ hs hspos hq2 (by nlinarith only [hqs]) hP1.le hQ1.le
  have hrr := rr_sub_one_le hk0 hka hkb
  set β : ℝ := a ^ 2 + b ^ 2 + 1 / 3 with hβdef
  set e : ℝ := etilde P Q ((t * h) ^ 2) with he
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have he1 : e ≤ 1 := rl_e_le_one hP hQ (sq_nonneg _) hP1.le hQ1.le
  have hrr0 : 0 ≤ rr a b t := Real.sqrt_nonneg _
  obtain ⟨hrr1, hrr2⟩ := abs_le.1 hrr
  have hA : hrAt P Q a b h t = 1 / 2 * rr a b t * e := rfl
  have h2a : 2 * hrAt P Q a b h t = rr a b t * e := by rw [hA]; ring
  have hlow : e - β / t ^ 2 ≤ rr a b t * e := by
    have h1 : (1 - β / t ^ 2) * e ≤ rr a b t * e := mul_le_mul_of_nonneg_right (by linarith only [hrr1]) he0
    have h3 : β / t ^ 2 * e ≤ β / t ^ 2 := mul_le_of_le_one_right (by positivity) he1
    have h4 : (1 - β / t ^ 2) * e = e - β / t ^ 2 * e := by ring
    linarith only [h1, h3, h4]
  have hc := rl_c_boundT (P := P) (Q := Q) (a := a) (b := b) (τ := τ) (x := x) (h := h) (qm := qs / 2) (t := t) hP hQ hτ hh hh1 hk1
    hkq
  constructor
  · rw [h2a]
    linarith only [hlow, hc, hmg]
  · rw [hA]
    have h1 : rr a b t ≤ 3 / 2 := by linarith only [hrr2, hβk]
    have h2 : rr a b t * e ≤ rr a b t := mul_le_of_le_one_right hrr0 he1
    linarith only [h1, h2]


/-- Lipschitz bound for `ẽ` on `[0, q_m²]`. -/
lemma rl_e_lip {P Q σ σ' qm : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hσ0 : 0 ≤ σ) (hσ : σ ≤ qm ^ 2) (hσ'0 : 0 ≤ σ') (hσ' : σ' ≤ qm ^ 2)
    (hP1 : 0 < 1 - P * qm ^ 2) (hQ1 : 0 < 1 - Q * qm ^ 2) :
    |etilde P Q σ' - etilde P Q σ| ≤
      (P + Q + 2 * P * Q * qm ^ 2) / (2 * Real.sqrt ((1 - P * qm ^ 2) * (1 - Q * qm ^ 2))) * |σ' - σ| := by
  set Xm : ℝ := (1 - P * qm ^ 2) * (1 - Q * qm ^ 2) with hXm
  have hXm0 : 0 < Xm := mul_pos hP1 hQ1
  have hP' : 1 - P * qm ^ 2 ≤ 1 - P * σ := by nlinarith only [mul_le_mul_of_nonneg_left hσ hP]
  have hQ' : 1 - Q * qm ^ 2 ≤ 1 - Q * σ := by nlinarith only [mul_le_mul_of_nonneg_left hσ hQ]
  have hP'' : 1 - P * qm ^ 2 ≤ 1 - P * σ' := by nlinarith only [mul_le_mul_of_nonneg_left hσ' hP]
  have hQ'' : 1 - Q * qm ^ 2 ≤ 1 - Q * σ' := by nlinarith only [mul_le_mul_of_nonneg_left hσ' hQ]
  set X : ℝ := (1 - P * σ) * (1 - Q * σ) with hX
  set X' : ℝ := (1 - P * σ') * (1 - Q * σ') with hX'
  have hXge : Xm ≤ X := mul_le_mul hP' hQ' hQ1.le (by linarith)
  have hX'ge : Xm ≤ X' := mul_le_mul hP'' hQ'' hQ1.le (by linarith)
  have hsX : Real.sqrt Xm ≤ Real.sqrt X := Real.sqrt_le_sqrt hXge
  have hsX' : Real.sqrt Xm ≤ Real.sqrt X' := Real.sqrt_le_sqrt hX'ge
  have hsm : 0 < Real.sqrt Xm := Real.sqrt_pos.2 hXm0
  have hX0 : 0 ≤ X := by linarith
  have hX'0 : 0 ≤ X' := by linarith
  have hdiff : X' - X = (σ' - σ) * (-(P + Q) + P * Q * (σ' + σ)) := by rw [hX, hX']; ring
  have hco : |-(P + Q) + P * Q * (σ' + σ)| ≤ P + Q + 2 * P * Q * qm ^ 2 := by
    have h1 : 0 ≤ P * Q := mul_nonneg hP hQ
    have h2 : P * Q * (σ' + σ) ≤ P * Q * (2 * qm ^ 2) := mul_le_mul_of_nonneg_left (by linarith) h1
    have h3 : 0 ≤ P * Q * (σ' + σ) := by positivity
    rw [abs_le]; constructor <;> nlinarith only [h1, h2, h3, hP, hQ]
  have hXdiff : |X' - X| ≤ (P + Q + 2 * P * Q * qm ^ 2) * |σ' - σ| := by
    rw [hdiff, abs_mul]
    calc |σ' - σ| * |-(P + Q) + P * Q * (σ' + σ)| ≤ |σ' - σ| * (P + Q + 2 * P * Q * qm ^ 2) :=
          mul_le_mul_of_nonneg_left hco (abs_nonneg _)
      _ = _ := by ring
  have hprod : (Real.sqrt X' - Real.sqrt X) * (Real.sqrt X' + Real.sqrt X) = X' - X := by
    have h1 := Real.sq_sqrt hX'0
    have h2 := Real.sq_sqrt hX0
    nlinarith only [h1, h2]
  unfold etilde
  rw [← hX, ← hX']
  have hden : 2 * Real.sqrt Xm ≤ Real.sqrt X' + Real.sqrt X := by linarith
  have hden0 : 0 < Real.sqrt X' + Real.sqrt X := by linarith
  have habs : |Real.sqrt X' - Real.sqrt X| * (Real.sqrt X' + Real.sqrt X) = |X' - X| := by
    have h1 : |Real.sqrt X' - Real.sqrt X| * (Real.sqrt X' + Real.sqrt X) = |(Real.sqrt X' - Real.sqrt X) * (Real.sqrt X' + Real.sqrt X)| := by
      rw [abs_mul, abs_of_pos hden0]
    rw [h1, hprod]
  have hfin : |Real.sqrt X' - Real.sqrt X| * (2 * Real.sqrt Xm) ≤ (P + Q + 2 * P * Q * qm ^ 2) * |σ' - σ| := by
    calc |Real.sqrt X' - Real.sqrt X| * (2 * Real.sqrt Xm) ≤ |Real.sqrt X' - Real.sqrt X| * (Real.sqrt X' + Real.sqrt X) :=
          mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ = |X' - X| := habs
      _ ≤ _ := hXdiff
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith only [hfin]

/-- The increments of the coefficients: `|a_{k+1} - a_k| + |c_{k+1} - c_k| ≤ (β + 2|ab|)/k² + Λ₁ h`. -/
lemma rl_incrT {P Q a b τ x qs h : ℝ} {t : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hqs : 0 < qs)
    (hP1 : 0 < 1 - P * (qs / 2) ^ 2) (hQ1 : 0 < 1 - Q * (qs / 2) ^ 2)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk1 : 1 ≤ t) (hka : a ^ 2 ≤ t ^ 2) (hkb : b ^ 2 ≤ t ^ 2)
    (hβk : (a ^ 2 + b ^ 2 + 1 / 3) / t ^ 2 ≤ 1 / 2) (hkq : (t + 1) * h ≤ qs / 2) :
    |hrAt P Q a b h (t + 1) - hrAt P Q a b h t| + |hrCt P Q τ x a b h (t + 1) - hrCt P Q τ x a b h t| ≤
      ((a ^ 2 + b ^ 2 + 1 / 3) + 2 * |a * b|) / t ^ 2 +
        ((3 / 2 * ((P + Q + 2 * P * Q * (qs / 2) ^ 2) / (2 * Real.sqrt ((1 - P * (qs / 2) ^ 2) * (1 - Q * (qs / 2) ^ 2)))) * (qs / 2) +
          2 * Real.sqrt (P * Q) * (qs / 2)) * h) := by
  have hk0 : (1 : ℝ) ≤ t := hk1
  have hk0' : (0 : ℝ) < t := by linarith
  set qm : ℝ := qs / 2 with hqm
  have hqm0 : 0 < qm := by rw [hqm]; positivity
  set β : ℝ := a ^ 2 + b ^ 2 + 1 / 3 with hβdef
  set L : ℝ := (P + Q + 2 * P * Q * qm ^ 2) / (2 * Real.sqrt ((1 - P * qm ^ 2) * (1 - Q * qm ^ 2))) with hL
  have hL0 : 0 ≤ L := by positivity
  have hkh : t * h ≤ qm := by nlinarith only [hkq, hh]
  have hk1h : (t + 1) * h ≤ qm := hkq
  have hrr := rr_sub_one_le hk0 hka hkb
  have hk1r : (1 : ℝ) ≤ t + 1 := by linarith
  have hrr' := rr_sub_one_le hk1r (by nlinarith only [hka, hk0]) (by nlinarith only [hkb, hk0])
  obtain ⟨hr1, hr2⟩ := abs_le.1 hrr
  obtain ⟨hr1', hr2'⟩ := abs_le.1 hrr'
  have hrr0 : 0 ≤ rr a b t := Real.sqrt_nonneg _
  have hrr0' : 0 ≤ rr a b (t + 1) := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hdr : |rr a b (t + 1) - rr a b t| ≤ 2 * β / t ^ 2 := by
    have h1 : β / (t + 1) ^ 2 ≤ β / t ^ 2 :=
      div_le_div_of_nonneg_left hβ0 (by positivity) (by nlinarith only [hk0'])
    have e : 2 * β / t ^ 2 = β / t ^ 2 + β / t ^ 2 := by ring
    rw [abs_le]; constructor <;> linarith only [hr1, hr2, hr1', hr2', h1, e]
  have hrr32 : rr a b t ≤ 3 / 2 := by linarith only [hr2, hβk]
  -- the `ẽ` increment
  have hq0 : 0 < t * h := by positivity
  have hq0' : 0 < (t + 1) * h := by positivity
  have hσ : (t * h) ^ 2 ≤ qm ^ 2 := pow_le_pow_left₀ hq0.le hkh 2
  have hσ' : ((t + 1) * h) ^ 2 ≤ qm ^ 2 := pow_le_pow_left₀ hq0'.le hk1h 2
  have hlip := rl_e_lip (P := P) (Q := Q) (σ := (t * h) ^ 2) (σ' := ((t + 1) * h) ^ 2) (qm := qm) hP hQ (sq_nonneg _) hσ
    (sq_nonneg _) hσ' hP1 hQ1
  have hσd : |((t + 1) * h) ^ 2 - (t * h) ^ 2| ≤ 2 * qm * h := by
    have e : ((t + 1) * h) ^ 2 - (t * h) ^ 2 = h * ((2 * t + 1) * h) := by ring
    rw [e, abs_of_nonneg (by positivity)]
    have : (2 * t + 1) * h ≤ 2 * qm := by nlinarith only [hk1h, hh]
    calc h * ((2 * t + 1) * h) ≤ h * (2 * qm) := mul_le_mul_of_nonneg_left this hh.le
      _ = 2 * qm * h := by ring
  have hde : |etilde P Q (((t + 1) * h) ^ 2) - etilde P Q ((t * h) ^ 2)| ≤ L * (2 * qm * h) :=
    hlip.trans (mul_le_mul_of_nonneg_left hσd hL0)
  have he1' : etilde P Q (((t + 1) * h) ^ 2) ≤ 1 := by
    apply rl_e_le_one hP hQ (sq_nonneg _)
    · nlinarith only [mul_le_mul_of_nonneg_left hσ' hP, hP1]
    · nlinarith only [mul_le_mul_of_nonneg_left hσ' hQ, hQ1]
  have he0 : 0 ≤ etilde P Q ((t * h) ^ 2) := Real.sqrt_nonneg _
  have he0' : 0 ≤ etilde P Q (((t + 1) * h) ^ 2) := Real.sqrt_nonneg _
  have hda : |hrAt P Q a b h (t + 1) - hrAt P Q a b h t| ≤ β / t ^ 2 + 3 / 2 * L * qm * h := by
    unfold hrAt
    set e0 := etilde P Q ((t * h) ^ 2)
    set e1 := etilde P Q (((t + 1) * h) ^ 2)
    set r0 := rr a b t
    set r1 := rr a b (t + 1)
    have e : 1 / 2 * r1 * e1 - 1 / 2 * r0 * e0 = 1 / 2 * ((r1 - r0) * e1 + r0 * (e1 - e0)) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have t1 : |(r1 - r0) * e1| ≤ 2 * β / t ^ 2 := by
      rw [abs_mul, abs_of_nonneg he0']
      calc |r1 - r0| * e1 ≤ |r1 - r0| * 1 := mul_le_mul_of_nonneg_left he1' (abs_nonneg _)
        _ ≤ _ := by linarith only [hdr]
    have t2 : |r0 * (e1 - e0)| ≤ 3 / 2 * (L * (2 * qm * h)) := by
      rw [abs_mul, abs_of_nonneg hrr0]
      exact mul_le_mul hrr32 hde (abs_nonneg _) (by norm_num)
    have hadd := abs_add_le ((r1 - r0) * e1) (r0 * (e1 - e0))
    have e2 : 2 * β / t ^ 2 = 2 * (β / t ^ 2) := by ring
    nlinarith only [hadd, t1, t2, e2]
  have hdc : |hrCt P Q τ x a b h (t + 1) - hrCt P Q τ x a b h t| ≤ 2 * Real.sqrt (P * Q) * qm * h + 2 * |a * b| / t ^ 2 := by
    unfold hrCt hrB
    have hτa : |τ| = 1 := by
      have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
      nlinarith only [this, abs_nonneg τ]
    have e : τ * (x - (Real.sqrt (P * Q) * (((t + 1 + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 +
          a * b / ((t + 1) * (t + 1 + 1)))) - τ * (x - (Real.sqrt (P * Q) * (((t + 1 / 2) * h) ^ 2 + h ^ 2 / 4) -
          Real.sqrt (P * Q) * h ^ 2 * (a ^ 2 + b ^ 2) / 2 + a * b / (t * (t + 1)))) =
        -τ * (Real.sqrt (P * Q) * (h ^ 2 * (2 * t + 2)) + (a * b / ((t + 1) * (t + 1 + 1)) - a * b / (t * (t + 1)))) := by ring
    rw [e, abs_mul, abs_neg, hτa, one_mul]
    have hb0 : 0 ≤ Real.sqrt (P * Q) := Real.sqrt_nonneg _
    have t1 : Real.sqrt (P * Q) * (h ^ 2 * (2 * t + 2)) ≤ 2 * Real.sqrt (P * Q) * qm * h := by
      have : h ^ 2 * (2 * t + 2) ≤ 2 * qm * h := by
        calc h ^ 2 * (2 * t + 2) = 2 * h * ((t + 1) * h) := by ring
          _ ≤ 2 * h * qm := mul_le_mul_of_nonneg_left hk1h (by positivity)
          _ = 2 * qm * h := by ring
      calc _ ≤ Real.sqrt (P * Q) * (2 * qm * h) := mul_le_mul_of_nonneg_left this hb0
        _ = _ := by ring
    have t2 : |a * b / ((t + 1) * (t + 1 + 1)) - a * b / (t * (t + 1))| ≤ 2 * |a * b| / t ^ 2 := by
      have e2 : a * b / ((t + 1) * (t + 1 + 1)) - a * b / (t * (t + 1)) =
          -(2 * (a * b)) / (t * (t + 1) * (t + 2)) := by
        field_simp; ring
      rw [e2, abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : 0 < t * (t + 1) * (t + 2))]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith only [hk0]
    have u1 := abs_add_le (Real.sqrt (P * Q) * (h ^ 2 * (2 * t + 2)))
      (a * b / ((t + 1) * (t + 1 + 1)) - a * b / (t * (t + 1)))
    have u3 : |Real.sqrt (P * Q) * (h ^ 2 * (2 * t + 2))| = Real.sqrt (P * Q) * (h ^ 2 * (2 * t + 2)) :=
      abs_of_nonneg (by positivity)
    linarith only [u1, u3, t1, t2]
  have hfin : |hrAt P Q a b h (t + 1) - hrAt P Q a b h t| + |hrCt P Q τ x a b h (t + 1) - hrCt P Q τ x a b h t| ≤
      (β + 2 * |a * b|) / t ^ 2 + (3 / 2 * L * qm + 2 * Real.sqrt (P * Q) * qm) * h := by
    have e1 : (β + 2 * |a * b|) / t ^ 2 = β / t ^ 2 + 2 * |a * b| / t ^ 2 := by ring
    rw [e1]
    nlinarith only [hda, hdc]
  exact hfin


end FormalResearch.Special

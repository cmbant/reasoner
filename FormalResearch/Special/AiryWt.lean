module

public import FormalResearch.Special.AiryEnvelopeReal

/-!
# The explicit Airy weight `airyWt` and its lattice sums

`airyWt X = (2+|X|)^{-1/4} exp(-(2/3) max(X,0)^{3/2})` (with `airyXi X = (2/3) max(X,0)^{3/2}`), a
single explicit stand-in for Olver's `M/E` on all of `ℝ`: it is the envelope of `Ai` on `[-1, ∞)` and
the (modulus) envelope `|X|^{-1/4}` of the oscillatory side.  The discrete-to-Airy arguments of the Weyl
papers (P3 appendices `A:1105-1135`, W1 `EC:74-113`) only use it through three facts, proved here.

* **Comparison with `Ai` on `X ≥ -1`** (from `airyAi_envelope_real`, `abs_airyAi'_le_mul_airyAi`):
  `airyWt/20 ≤ Ai ≤ 6 airyWt` (`airyWt_div_twenty_le_airyAi`, `airyAi_le_six_airyWt`) and
  `|Ai'| ≤ 720 √(2+|X|) airyWt` (`abs_airyAi'_le_airyWt`).  The constants are non-optimal.
* **Local constancy** (`airyWt_le_of_close`): if `|ξ - X| ≤ 1` and `|ξ - X| √(1+|X|) ≤ Λ` then
  `airyWt ξ ≤ (6/5) e^Λ airyWt X`.  The hypothesis `|ξ - X| √(1+|X|) ≤ Λ` cannot be dropped: `Ai(X-1)/Ai(X)`
  grows like `e^{√X}`, so no bound `airyWt ξ ≤ C airyWt X` is uniform in `|ξ-X| ≤ 1` and `X → ∞` (this
  is why the Taylor bounds of `AiryShiftTaylor` carry the same hypothesis; in the discrete application
  `|ξ - X| = O(h^{1/3})` and `X = O(h^{-2/3})`, so `Λ = O(1)`).
* **Lattice sums** (`airyWt_sq_lattice_sum`): for any finite lattice `X_0, …, X_n` in a window
  `[-A, B]` with spacings `X_{i+1} - X_i ≥ g > 0`,
  `Σ_i airyWt(X_i)² ≤ 2 + (2/g)(√(2+A) + √(2+B))`.  Only the lower spacing bound is used.  With
  `g = c δ` (`δ = h^{1/3}`) and `A, B ≤ C₀ δ^{-2}` this is `≤ (2 + 4√(2+C₀)/c) δ^{-2}`, i.e. `O(h^{-2/3})`
  (`airyWt_sq_lattice_sum_scaled`; P3 `A:1131-1133`).  `airyWt²` is **not** integrable at `-∞`
  (`(2+|X|)^{-1/2}`), which is why the sum bound depends on the window `[-A, B]` through `√A`, `√B`.

Not formalised: the Olver functions `M`, `E` themselves and `airyWt ≍ M/E` on `X ≤ -1` (needs the negative
axis asymptotics of `Ai² + Bi²`, optional item of the plan); the lower bound for lattice sums.
Numerics (`mpmath`, 30 digits): `Ai/airyWt ∈ [0.284, 0.705]` and `|Ai'|/(√(2+|X|) airyWt) ≤ 0.28` on `X ∈ [-1, 60]`
(the Lean constants `1/20`, `6`, `720` are far from sharp); `airyWt(X-1)/airyWt(X) = 2.3e2, 2.2e4, 3.3e7, 5.4e13`
at `X = 30, 100, 300, 1000`, i.e. `≈ e^{√X}` (so `Λ` cannot be dropped in `airyWt_le_of_close`); random lattices
(300 trials, spacings in `[cδ, 4cδ]`, windows up to `[-40, 40]`): `Σ airyWt² ≤ 0.41 ·` the bound of
`airyWt_sq_lattice_sum`.
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- The explicit Airy weight `(2+|X|)^{-1/4} exp(-(2/3) max(X,0)^{3/2})`. -/
noncomputable def airyWt (X : ℝ) : ℝ := (2 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)

lemma airyWt_pos (X : ℝ) : 0 < airyWt X := by
  unfold airyWt
  have : 0 < 2 + |X| := by positivity
  positivity

lemma airyWt_le_rpow (X : ℝ) : airyWt X ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by
  unfold airyWt
  have h1 : Real.exp (-airyXi X) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [airyXi_nonneg X]
  have : 0 < 2 + |X| := by positivity
  have h2 : 0 < (2 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos this _
  nlinarith

/-- `((2+t)^{-1/4})² = 1/√(2+t)`. -/
lemma rpow_neg_quarter_sq {t : ℝ} (ht : 0 < t) :
    (t ^ (-(1 / 4) : ℝ)) ^ 2 = (√t)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]
  norm_num

/-- `airyWt² ≤ 1/√(2+|X|)`. -/
lemma airyWt_sq_le (X : ℝ) : airyWt X ^ 2 ≤ (√(2 + |X|))⁻¹ := by
  have ht : 0 < 2 + |X| := by positivity
  rw [← rpow_neg_quarter_sq ht]
  exact pow_le_pow_left₀ (airyWt_pos X).le (airyWt_le_rpow X) 2

lemma airyWt_le_one (X : ℝ) : airyWt X ≤ 1 := by
  refine (airyWt_le_rpow X).trans ?_
  have ht : (2 : ℝ) ≤ 2 + |X| := by linarith [abs_nonneg X]
  calc (2 + |X|) ^ (-(1 / 4) : ℝ) ≤ 2 ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) ht (by norm_num)
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-! ### Comparison with `Ai` on `[-1, ∞)` -/

lemma three_rpow_quarter_le : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 / 2 := by
  have h : (3 : ℝ) ≤ (3 / 2) ^ 4 := by norm_num
  calc (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (((3 : ℝ) / 2) ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h (by norm_num)
    _ = 3 / 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `Ai ≥ airyWt / 20` on `[-1, ∞)`. -/
theorem airyWt_div_twenty_le_airyAi {X : ℝ} (hX : -1 ≤ X) : airyWt X / 20 ≤ airyAi X := by
  have h2 : 0 < 2 + X := by linarith
  have hle : 2 + X ≤ 2 + |X| := by linarith [le_abs_self X]
  have hr : (2 + |X|) ^ (-(1 / 4) : ℝ) ≤ (2 + X) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h2 hle (by norm_num)
  refine le_trans ?_ (airyAi_envelope_real hX).1
  unfold airyWt
  have := Real.exp_pos (-airyXi X)
  nlinarith

/-- `Ai ≤ 6 airyWt` on `[-1, ∞)`. -/
theorem airyAi_le_six_airyWt {X : ℝ} (hX : -1 ≤ X) : airyAi X ≤ 6 * airyWt X := by
  have h2 : 0 < 2 + X := by linarith
  have ht : 0 < 2 + |X| := by positivity
  have hle : 2 + |X| ≤ 3 * (2 + X) := by
    rcases le_or_gt 0 X with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  -- `3^{-1/4} (2+X)^{-1/4} ≤ (2+|X|)^{-1/4}`
  have hr : (3 * (2 + X)) ^ (-(1 / 4) : ℝ) ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ht hle (by norm_num)
  rw [Real.mul_rpow (by norm_num) h2.le] at hr
  have h3 : (3 : ℝ) ^ (-(1 / 4) : ℝ) * (3 : ℝ) ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h3p : 0 < (3 : ℝ) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hc := three_rpow_quarter_le
  have hp : 0 < (2 + X) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  -- `(2+X)^{-1/4} ≤ 3^{1/4} (2+|X|)^{-1/4} ≤ (3/2) (2+|X|)^{-1/4}`
  have hs : (2 + X) ^ (-(1 / 4) : ℝ) ≤ 3 / 2 * (2 + |X|) ^ (-(1 / 4) : ℝ) := by
    have h4 : (2 + X) ^ (-(1 / 4) : ℝ) = (3 : ℝ) ^ (1 / 4 : ℝ) *
        ((3 : ℝ) ^ (-(1 / 4) : ℝ) * (2 + X) ^ (-(1 / 4) : ℝ)) := by
      rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (1 / 4 : ℝ)), h3, one_mul]
    rw [h4]
    have hq : 0 ≤ (3 : ℝ) ^ (1 / 4 : ℝ) := by positivity
    have h5 : (2 + |X|) ^ (-(1 / 4) : ℝ) ≥ 0 := by positivity
    calc (3 : ℝ) ^ (1 / 4 : ℝ) * ((3 : ℝ) ^ (-(1 / 4) : ℝ) * (2 + X) ^ (-(1 / 4) : ℝ))
        ≤ (3 : ℝ) ^ (1 / 4 : ℝ) * (2 + |X|) ^ (-(1 / 4) : ℝ) := by gcongr
      _ ≤ 3 / 2 * (2 + |X|) ^ (-(1 / 4) : ℝ) := by gcongr
  have := (airyAi_envelope_real hX).2
  unfold airyWt
  have he := Real.exp_pos (-airyXi X)
  nlinarith

/-- `|Ai'| ≤ 720 √(2+|X|) airyWt` on `[-1, ∞)`. -/
theorem abs_airyAi'_le_airyWt {X : ℝ} (hX : -1 ≤ X) :
    |airyAi' X| ≤ 720 * √(2 + |X|) * airyWt X := by
  have h := abs_airyAi'_le_mul_airyAi hX
  have h2 : 0 < 2 + X := by linarith
  have hs : (2 + X) ^ (1 / 2 : ℝ) ≤ √(2 + |X|) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow h2.le (by linarith [le_abs_self X]) (by norm_num)
  have h6 := airyAi_le_six_airyWt hX
  have hw := airyWt_pos X
  calc |airyAi' X| ≤ 120 * (2 + X) ^ (1 / 2 : ℝ) * airyAi X := h
    _ ≤ 120 * √(2 + |X|) * (6 * airyWt X) := by
        have := airyAi_pos_of_neg_one_le hX
        gcongr
    _ = _ := by ring

/-! ### Local constancy -/

/-- For `a ≥ b ≥ 0`: `a^{3/2} - b^{3/2} ≤ (3/2) √a (a - b)`. -/
lemma rpow_three_halves_sub_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    a ^ (3 / 2 : ℝ) - b ^ (3 / 2 : ℝ) ≤ 3 / 2 * √a * (a - b) := by
  have e : ∀ x : ℝ, 0 ≤ x → x ^ (3 / 2 : ℝ) = (√x) ^ 3 := by
    intro x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rw [e a (hb.trans hab), e b hb]
  have ha := hb.trans hab
  have hu := Real.sqrt_nonneg a
  have hv := Real.sqrt_nonneg b
  have huv : √b ≤ √a := Real.sqrt_le_sqrt hab
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have hd : a - b = √a ^ 2 - √b ^ 2 := by rw [h1, h2]
  rw [hd]
  nlinarith [mul_nonneg (sub_nonneg.2 huv) (mul_nonneg hv (sub_nonneg.2 huv)),
    mul_nonneg (sub_nonneg.2 huv) (sq_nonneg (√a - √b)), mul_nonneg hu hv]

/-- **Local constancy of the weight.**  If `|ξ - X| ≤ 1` and `|ξ - X| √(1+|X|) ≤ Λ` then
`airyWt ξ ≤ (6/5) e^Λ airyWt X`. -/
theorem airyWt_le_of_close {X ξ Λ : ℝ} (h1 : |ξ - X| ≤ 1) (hΛ : |ξ - X| * √(1 + |X|) ≤ Λ) :
    airyWt ξ ≤ 6 / 5 * Real.exp Λ * airyWt X := by
  have hX2 : 0 < 2 + |X| := by positivity
  have hξ2 : 0 < 2 + |ξ| := by positivity
  -- polynomial factor: `2 + |ξ| ≥ (2 + |X|)/2`
  have hpoly : (2 + |ξ|) ^ (-(1 / 4) : ℝ) ≤ 6 / 5 * (2 + |X|) ^ (-(1 / 4) : ℝ) := by
    have hle : (2 + |X|) / 2 ≤ 2 + |ξ| := by
      have : |X| ≤ |ξ| + 1 := by
        have := abs_sub_abs_le_abs_sub X ξ
        rw [abs_sub_comm] at this
        linarith
      linarith [abs_nonneg ξ]
    have hle' : 2⁻¹ * (2 + |X|) ≤ 2 + |ξ| := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2⁻¹ * (2 + |X|)) hle'
      (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) hX2.le, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv] at h
    refine h.trans ?_
    have := two_rpow_quarter_le
    have hp : 0 ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by positivity
    nlinarith
  -- exponential factor: `airyXi X - airyXi ξ ≤ Λ`
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have hexp : airyXi X - airyXi ξ ≤ Λ := by
    unfold airyXi
    set a := max X 0 with ha
    set b := max ξ 0 with hb
    have hb0 : 0 ≤ b := le_max_right _ _
    have ha0 : 0 ≤ a := le_max_right _ _
    rcases le_total a b with hab | hab
    · have : a ^ (3 / 2 : ℝ) ≤ b ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ha0 hab (by norm_num)
      nlinarith
    · have h3 := rpow_three_halves_sub_le hb0 hab
      have hab' : a - b ≤ |ξ - X| := by
        have := abs_max_sub_max_le_abs X ξ 0
        rw [abs_sub_comm ξ X]
        exact (le_abs_self _).trans this
      have hsa : √a ≤ √(1 + |X|) := by
        apply Real.sqrt_le_sqrt
        have : a ≤ |X| := max_le (le_abs_self X) (abs_nonneg X)
        linarith
      have hs0 := Real.sqrt_nonneg a
      have h4 : √a * (a - b) ≤ √(1 + |X|) * |ξ - X| :=
        mul_le_mul hsa hab' (by linarith) (Real.sqrt_nonneg _)
      nlinarith
  have hexp' : Real.exp (-airyXi ξ) ≤ Real.exp Λ * Real.exp (-airyXi X) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; linarith
  unfold airyWt
  have hE1 := Real.exp_pos (-airyXi X)
  have hE2 := Real.exp_pos (-airyXi ξ)
  have hp1 : 0 < (2 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hX2 _
  have hp2 : 0 < (2 + |ξ|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hξ2 _
  calc (2 + |ξ|) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi ξ)
      ≤ (6 / 5 * (2 + |X|) ^ (-(1 / 4) : ℝ)) * (Real.exp Λ * Real.exp (-airyXi X)) := by gcongr
    _ = _ := by ring

/-! ### Lattice sums -/

private lemma inv_sqrt_two_add_le_one {x : ℝ} (hx : 0 ≤ x) : (√(2 + x))⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ √(2 + x) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  exact inv_le_one_of_one_le₀ h1

private lemma inv_sqrt_step {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (√(2 + b))⁻¹ * (b - a) ≤ 2 * (√(2 + b) - √(2 + a)) := by
  have hu : 0 < √(2 + b) := Real.sqrt_pos.2 (by linarith)
  have huv : √(2 + a) ≤ √(2 + b) := Real.sqrt_le_sqrt (by linarith)
  have h1 : (√(2 + b)) ^ 2 = 2 + b := Real.sq_sqrt (by linarith)
  have h2 : (√(2 + a)) ^ 2 = 2 + a := Real.sq_sqrt (by linarith)
  rw [inv_mul_le_iff₀ hu]
  nlinarith [sq_nonneg (√(2 + b) - √(2 + a))]

/-- Sum of `(2+x)^{-1/2}` over a `g`-separated finite subset of `[0, B]`. -/
private lemma sum_inv_sqrt_le {g : ℝ} (hg : 0 < g) (T : Finset ℝ) :
    (∀ x ∈ T, 0 ≤ x) → (∀ x ∈ T, ∀ y ∈ T, x < y → x + g ≤ y) →
    ∀ B : ℝ, 0 ≤ B → (∀ x ∈ T, x ≤ B) →
      ∑ x ∈ T, (√(2 + x))⁻¹ ≤ 1 + 2 / g * (√(2 + B) - √2) := by
  induction T using Finset.induction_on_max with
  | empty =>
    intro _ _ B hB0 _
    have : √2 ≤ √(2 + B) := Real.sqrt_le_sqrt (by linarith)
    simp only [Finset.sum_empty]
    have : 0 ≤ 2 / g * (√(2 + B) - √2) := mul_nonneg (by positivity) (by linarith)
    linarith
  | insert a S hS ih =>
    intro h0 hsep B hB0 hB
    have haS : a ∉ S := fun h => lt_irrefl _ (hS a h)
    rw [Finset.sum_insert haS]
    have ha0 : 0 ≤ a := h0 a (Finset.mem_insert_self _ _)
    have hfa : (√(2 + a))⁻¹ ≤ 1 := inv_sqrt_two_add_le_one ha0
    have haB : a ≤ B := hB a (Finset.mem_insert_self _ _)
    have hsq : √(2 + a) ≤ √(2 + B) := Real.sqrt_le_sqrt (by linarith)
    have hs2 : √2 ≤ √(2 + a) := Real.sqrt_le_sqrt (by linarith)
    rcases S.eq_empty_or_nonempty with hS0 | hne
    · subst hS0
      have : 0 ≤ 2 / g * (√(2 + B) - √2) := mul_nonneg (by positivity) (by linarith)
      simp only [Finset.sum_empty]
      linarith
    · set m := S.max' hne with hm
      have hmS : m ∈ S := Finset.max'_mem S hne
      have hma : m < a := hS m hmS
      have hm0 : 0 ≤ m := h0 m (Finset.mem_insert_of_mem hmS)
      have hIH := ih (fun x hx => h0 x (Finset.mem_insert_of_mem hx))
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
        m hm0 (fun x hx => Finset.le_max' S x hx)
      have hga : m + g ≤ a :=
        hsep m (Finset.mem_insert_of_mem hmS) a (Finset.mem_insert_self _ _) hma
      have hstep := inv_sqrt_step hm0 hma.le
      have hfpos : 0 ≤ (√(2 + a))⁻¹ := by positivity
      have h5 : (√(2 + a))⁻¹ * g ≤ 2 * (√(2 + a) - √(2 + m)) :=
        le_trans (mul_le_mul_of_nonneg_left (by linarith) hfpos) hstep
      have h6 : (√(2 + a))⁻¹ ≤ 2 / g * (√(2 + a) - √(2 + m)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hg]; linarith
      have h7 : 2 / g * (√(2 + a) - √2) ≤ 2 / g * (√(2 + B) - √2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith

/-- **Lattice sum bound.**  Let `X_0, …, X_n` be a finite lattice in `[-A, B]` (`A, B ≥ 0`) with
spacings `X_{i+1} - X_i ≥ g > 0`.  Then `Σ_i airyWt(X_i)² ≤ 2 + (2/g)(√(2+A) + √(2+B))`.
(P3 appendices `A:1131-1133`: with `g ≍ h^{1/3}` and a window of length `O(h^{-2/3})` this is
`O(h^{-2/3})`, see `airyWt_sq_lattice_sum_scaled`.) -/
theorem airyWt_sq_lattice_sum {g A B : ℝ} (hg : 0 < g) (hA : 0 ≤ A) (hB : 0 ≤ B) (n : ℕ)
    (X : ℕ → ℝ) (hgap : ∀ i < n, X i + g ≤ X (i + 1)) (hlo : ∀ i ≤ n, -A ≤ X i)
    (hhi : ∀ i ≤ n, X i ≤ B) :
    ∑ i ∈ Finset.range (n + 1), airyWt (X i) ^ 2 ≤ 2 + 2 / g * (√(2 + A) + √(2 + B)) := by
  have hsep : ∀ i k, i + k + 1 ≤ n → X i + g ≤ X (i + k + 1) := by
    intro i k
    induction k with
    | zero => intro h; exact hgap i (by omega)
    | succ k ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hgap (i + k + 1) (by omega)
      have : i + (k + 1) + 1 = i + k + 1 + 1 := by omega
      rw [this]; linarith
  have hsep' : ∀ i j, i < j → j ≤ n → X i + g ≤ X j := by
    intro i j hij hj
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
    exact hsep i k hj
  have hinj : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1), X i = X j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsep' i j h (by omega); linarith
    · have := hsep' j i h (by omega); linarith
  have hle : ∑ i ∈ Finset.range (n + 1), airyWt (X i) ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), (√(2 + |X i|))⁻¹ :=
    Finset.sum_le_sum fun i _ => airyWt_sq_le (X i)
  refine hle.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun i => 0 ≤ X i)]
  -- nonnegative part
  have hP : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 0 ≤ X i), (√(2 + |X i|))⁻¹ ≤
      1 + 2 / g * (√(2 + B) - √2) := by
    have e : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 0 ≤ X i), (√(2 + |X i|))⁻¹ =
        ∑ x ∈ ((Finset.range (n + 1)).filter (fun i => 0 ≤ X i)).image X, (√(2 + x))⁻¹ := by
      rw [Finset.sum_image (fun i hi j hj hij =>
        hinj i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [abs_of_nonneg (Finset.mem_filter.1 hi).2]
    rw [e]
    refine sum_inv_sqrt_le hg _ ?_ ?_ B hB ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hi).2
    · intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
      rcases lt_trichotomy i j with h | h | h
      · exact hsep' i j h (by omega)
      · subst h; exact absurd hxy (lt_irrefl _)
      · have := hsep' j i h (by omega); linarith
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact hhi i (by have := Finset.mem_range.1 (Finset.mem_filter.1 hi).1; omega)
  -- negative part
  have hN : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => ¬ 0 ≤ X i), (√(2 + |X i|))⁻¹ ≤
      1 + 2 / g * (√(2 + A) - √2) := by
    have e : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => ¬ 0 ≤ X i), (√(2 + |X i|))⁻¹ =
        ∑ x ∈ ((Finset.range (n + 1)).filter (fun i => ¬ 0 ≤ X i)).image (fun i => -X i),
          (√(2 + x))⁻¹ := by
      rw [Finset.sum_image (fun i hi j hj hij =>
        hinj i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 (neg_inj.1 hij))]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [abs_of_neg (not_le.1 (Finset.mem_filter.1 hi).2)]
    rw [e]
    refine sum_inv_sqrt_le hg _ ?_ ?_ A hA ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have := not_le.1 (Finset.mem_filter.1 hi).2
      linarith
    · intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      have hj' := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
      rcases lt_trichotomy i j with h | h | h
      · have := hsep' i j h (by omega); linarith
      · subst h; exact absurd hxy (lt_irrefl _)
      · have := hsep' j i h (by omega); linarith
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have := hlo i (by have := Finset.mem_range.1 (Finset.mem_filter.1 hi).1; omega)
      linarith
  have h2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have : 2 / g * (√(2 + B) - √2) + 2 / g * (√(2 + A) - √2) ≤
      2 / g * (√(2 + A) + √(2 + B)) := by
    have : 0 ≤ 2 / g * √2 := by positivity
    nlinarith
  linarith

/-- **Scaled form** (`δ = h^{1/3}`): if the spacings are `≥ c δ` (`0 < c`, `0 < δ ≤ 1`) and the lattice lies in
`[-C₀ δ^{-2}, C₀ δ^{-2}]` (`C₀ ≥ 0`; in the application `δ^{-2} = h^{-2/3}`), then
`Σ_i airyWt(X_i)² ≤ (2 + 4 √(2+C₀)/c) δ^{-2}`. -/
theorem airyWt_sq_lattice_sum_scaled {c δ C₀ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C₀) (n : ℕ) (X : ℕ → ℝ) (hgap : ∀ i < n, X i + c * δ ≤ X (i + 1))
    (hwin : ∀ i ≤ n, |X i| ≤ C₀ / δ ^ 2) :
    ∑ i ∈ Finset.range (n + 1), airyWt (X i) ^ 2 ≤ (2 + 4 * √(2 + C₀) / c) / δ ^ 2 := by
  have hcδ : 0 < c * δ := mul_pos hc hδ
  have hW : 0 ≤ C₀ / δ ^ 2 := by positivity
  have h := airyWt_sq_lattice_sum hcδ hW hW n X hgap
    (fun i hi => by have := (abs_le.1 (hwin i hi)).1; linarith)
    (fun i hi => (abs_le.1 (hwin i hi)).2)
  refine h.trans ?_
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ 1 / δ ^ 2 := by
    rw [le_div_iff₀ hδ2]; nlinarith
  have hs : √(2 + C₀ / δ ^ 2) ≤ √(2 + C₀) / δ := by
    rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt (by linarith)]
    rw [← mul_one_div, ← mul_one_div (2 + C₀)]
    nlinarith [mul_nonneg hC (sub_nonneg.2 h1)]
  have h2 : 2 / (c * δ) * (√(2 + C₀ / δ ^ 2) + √(2 + C₀ / δ ^ 2)) ≤
      4 * √(2 + C₀) / c / δ ^ 2 := by
    have : 2 / (c * δ) * (√(2 + C₀ / δ ^ 2) + √(2 + C₀ / δ ^ 2)) ≤
        2 / (c * δ) * (√(2 + C₀) / δ + √(2 + C₀) / δ) :=
      mul_le_mul_of_nonneg_left (add_le_add hs hs) (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  calc 2 + 2 / (c * δ) * (√(2 + C₀ / δ ^ 2) + √(2 + C₀ / δ ^ 2))
      ≤ 2 / δ ^ 2 + 4 * √(2 + C₀) / c / δ ^ 2 := by
        have : (2 : ℝ) ≤ 2 / δ ^ 2 := by
          calc (2 : ℝ) = 2 * 1 := by ring
            _ ≤ 2 * (1 / δ ^ 2) := by gcongr
            _ = 2 / δ ^ 2 := by ring
        linarith
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyWt_sq_lattice_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_sq_lattice_sum

/-- info: 'FormalResearch.Special.airyWt_sq_lattice_sum_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_sq_lattice_sum_scaled

/-- info: 'FormalResearch.Special.airyWt_le_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_le_of_close

/-- info: 'FormalResearch.Special.airyAi_le_six_airyWt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_le_six_airyWt

/-- info: 'FormalResearch.Special.airyWt_div_twenty_le_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWt_div_twenty_le_airyAi

/-- info: 'FormalResearch.Special.abs_airyAi'_le_airyWt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyAi'_le_airyWt

end FormalResearch.Special

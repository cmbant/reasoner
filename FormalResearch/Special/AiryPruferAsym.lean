module

public import FormalResearch.Special.AiryZeroSpacing

/-!
# The Prüfer angle of `Ai` on the negative axis: `θ(-y) = -(2/3) y^{3/2} + 3π/4 + O(1)`, with sharp amplitude `π/2`

Let `θ` be a Prüfer angle of `(Ai, Ai')` (`Ai = r sin θ`, `Ai' = r cos θ`, `θ' = cos²θ + y sin²θ` at `x = -y`) normalised by
`θ(0) ∈ (0, π)` (`airy_exists_prufer`: `θ(0) ∈ (π/2, π)`), and `ξ(y) = (2/3) y^{3/2}`.

**What is true.**  `tan θ = Ai/Ai' ≈ y^{-1/2} cot φ` with `φ = ξ - π/4`, so `θ` is *not* `π/2 - φ`: it is a **staircase** — a
plateau at the zeros of `Ai` (`θ ∈ πℤ`) and a fast jump by `-π` (width `~ y^{-1/2}` in `φ`) at each zero of `Ai'`
(`θ ∈ π/2 + πℤ`).  Hence `D(y) := θ(-y) + ξ(y) - 3π/4` is a sawtooth of amplitude `π/2` (numerically
`sup |D| = 0.88` for `y ≤ 60`, increasing slowly to `π/2`).

* `airy_prufer_airyZero`: **`θ(a_n) = -(n-1)π` exactly** (`n ≥ 1`);
* `airy_exists_airyAi'_zero`: for `n ≥ 1` there is exactly one zero `b_n` of `Ai'` in `(a_{n+1}, a_n)` and
  `θ(b_n) = -(n-1)π - π/2` (Clark node for `α = π/2`);
* `airyAi'_zero_location_r`: a zero `-r²` of `Ai'` with `r ≥ 2` has `|(2/3) r³ - (k + 1/4)π| ≤ 1.12/r³` for an integer `k`
  (from `airyAi'_neg_sq_asymptotic`); `k = n` for `b_n` (`n ≥ 2`);
* **`airy_prufer_deviation`**: for `y ≥ |a_2|`,
  `|θ(-y) + (2/3) y^{3/2} - 3π/4| ≤ π/2 + 0.14`  (`0.14 = 1.12/8`); the constant `π/2` is the sharp amplitude of the
  sawtooth.  Proof: on `[a_n, b_n]` and `[b_n, a_{n+1}]` the angle lies between its (exact) values at the end points and
  `ξ` between its (located) values; the four corner values give `±π/2` up to the location errors `0.05` (zeros of
  `Ai`) and `0.14` (zeros of `Ai'`);
* `airy_prufer_ratio`: `|-θ(-y)/ξ(y) - 1| ≤ 4.1/ξ(y)` for `y ≥ |a_2|`, i.e. **`θ(-y) ~ -ξ(y)`** with explicit rate `O(y^{-3/2})`.

Numerically checked (mpmath, unwrapped angle `arg(Ai' + i Ai)`, `θ(0) = 2.2…`): `θ(a_n) = -(n-1)π`, `D(a_n) ≈ 0`,
`|D| ≤ 0.8808` on `4.0879 ≤ y ≤ 60`; the proved `π/2 + 0.14` is therefore valid but the finite-`y` sup is smaller.
Everything here is proved; **not formalised**: the `O(y^{-1/2})` refinements at general Clark nodes
(`cos α Ai - sin α Ai'`, `α ≢ 0, π/2`; see the handoff).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

open SturmAiry

section Levels

variable {θ : ℝ → ℝ}

lemma airyPrufer_mono (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) : StrictMonoOn θ (Iic 0) :=
  hθ.strictMonoOn_of_neg (convex_Iic 0) (by rw [interior_Iic]; exact fun x hx => hx)

/-- **`θ(a_n) = -(n-1)π`.** -/
theorem airy_prufer_airyZero (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0)
    (h1 : θ 0 < π) {n : ℕ} (hn : 1 ≤ n) : θ (airyZero n) = -((n : ℝ) - 1) * π := by
  obtain ⟨k, hk⟩ := (airy_zero_iff_level hθ _).1 (airyAi_airyZero n)
  have hc := airy_zeros_ncard hθ h0 h1 (airyZero_nonpos n)
  have hcount : (({x | x ∈ Ioc (airyZero n) 0 ∧ airyAi x = 0}).ncard : ℤ) = (n : ℤ) - 1 := by
    have := airyZeroCount_airyZero n
    unfold airyZeroCount airyZeroSet at this
    rw [this]; omega
  have hfl : ⌊θ (airyZero n) / π⌋ = k := by
    rw [hk]
    have : (k : ℝ) * π / π = k := by field_simp
    rw [this, Int.floor_intCast]
  rw [hfl, hcount] at hc
  have hk' : k = -((n : ℤ) - 1) := by omega
  rw [hk, hk']; push_cast; ring

/-- **The zeros of `Ai'`**: for `n ≥ 1` there is `b_n ∈ (a_{n+1}, a_n)` with `Ai'(b_n) = 0` and
`θ(b_n) = -(n-1)π - π/2`. -/
theorem airy_exists_airyAi'_zero (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0)
    (h1 : θ 0 < π) (hlo : π / 2 < θ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ b : ℝ, airyZero (n + 1) < b ∧ b < airyZero n ∧ airyAi' b = 0 ∧
      θ b = -((n : ℝ) - 1) * π - π / 2 := by
  have hpi := Real.pi_pos
  have hm : π / 2 + ((-(n : ℤ) : ℤ) : ℝ) * π ≤ θ 0 := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨b, ⟨hb0, hbθ, hbc⟩, -⟩ := airy_node_exists_unique hθ (α := π / 2) (m := -(n : ℤ)) hm
  have hb' : airyAi' b = 0 := by simpa [combo] using hbc
  have hbθ' : θ b = -((n : ℝ) - 1) * π - π / 2 := by rw [hbθ]; push_cast; ring
  have hmono := airyPrufer_mono hθ
  have ha := airy_prufer_airyZero hθ h0 h1 hn
  have ha' := airy_prufer_airyZero hθ h0 h1 (by omega : 1 ≤ n + 1)
  have hn1 : (airyZero n) ∈ Iic (0 : ℝ) := airyZero_nonpos n
  have hn2 : (airyZero (n + 1)) ∈ Iic (0 : ℝ) := airyZero_nonpos _
  refine ⟨b, (hmono.lt_iff_lt hn2 hb0).1 ?_, (hmono.lt_iff_lt hb0 hn1).1 ?_, hb', hbθ'⟩
  · rw [ha', hbθ']; push_cast; nlinarith
  · rw [ha, hbθ']; nlinarith

/-- Location of the zeros of `Ai'` on the negative axis: if `r ≥ 2` and `Ai'(-r²) = 0`, then
`|(2/3) r³ - (k + 1/4)π| ≤ 1.12/r³` for an integer `k`. -/
theorem airyAi'_zero_location_r {r : ℝ} (hr : 2 ≤ r) (hz : airyAi' (-(r ^ 2)) = 0) :
    ∃ k : ℤ, |2 / 3 * r ^ 3 - (k + 1 / 4) * π| ≤ 1.12 / r ^ 3 := by
  have hr0 : 0 < r := by linarith
  have h := airyAi'_neg_sq_asymptotic hr0
  rw [hz, zero_sub, abs_neg] at h
  set φ := 2 / 3 * r ^ 3 - π / 4 with hφ
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsin : |Real.sin φ| ≤ 2 * √π / 5 / r ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos hs, abs_of_pos hT, div_le_iff₀ hT] at h
    have hr3 : 0 < r ^ 3 := by positivity
    have : √r * |Real.sin φ| ≤ 2 / (5 * (√r * r ^ 2)) * √π := h
    have e : 2 / (5 * (√r * r ^ 2)) * √π = √r * (2 * √π / 5 / r ^ 3) := by
      have hrr : √r * √r = r := Real.mul_self_sqrt hr0.le
      field_simp
      nlinarith [hrr]
    rw [e] at this
    exact le_of_mul_le_mul_left this hs
  set q := φ / π with hq
  set k : ℤ := round q with hk
  have hqk : |q - k| ≤ 1 / 2 := abs_sub_round q
  set x := φ - k * π with hx
  have hxq : x = π * (q - k) := by rw [hx, hq]; field_simp
  have hxabs : |x| ≤ π / 2 := by
    rw [hxq, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hφx : φ = x + k * π := by rw [hx]; ring
  have hsx : |Real.sin φ| = |Real.sin x| := by
    rw [hφx, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have hxs : |x| ≤ π / 2 * |Real.sin x| := by
    have key : ∀ y : ℝ, 0 ≤ y → y ≤ π / 2 → y ≤ π / 2 * Real.sin y := by
      intro y h0 h1
      have := Real.mul_le_sin h0 h1
      have hπ := Real.pi_pos
      calc y = π / 2 * (2 / π * y) := by field_simp
        _ ≤ π / 2 * Real.sin y := mul_le_mul_of_nonneg_left this (by positivity)
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (key x h0 (by linarith [(abs_le.mp hxabs).2])).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
    · rw [abs_of_nonpos h0]
      have := key (-x) (by linarith) (by linarith [(abs_le.mp hxabs).1])
      rw [Real.sin_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity))
  refine ⟨k, ?_⟩
  have e : 2 / 3 * r ^ 3 - (k + 1 / 4) * π = x := by rw [hx, hφ]; ring
  rw [e]
  have hr3 : 0 < r ^ 3 := by positivity
  have hπ1 : π < 3.1416 := Real.pi_lt_d4
  have hπ2 : √π < 1.7725 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith [Real.pi_lt_d4]
  calc |x| ≤ π / 2 * |Real.sin x| := hxs
    _ = π / 2 * |Real.sin φ| := by rw [hsx]
    _ ≤ π / 2 * (2 * √π / 5 / r ^ 3) := mul_le_mul_of_nonneg_left hsin (by positivity)
    _ = π * √π / 5 / r ^ 3 := by field_simp
    _ ≤ 1.12 / r ^ 3 := by
        apply div_le_div_of_nonneg_right _ hr3.le
        nlinarith [Real.sqrt_nonneg π, Real.pi_pos]

/-- **Any zero of `Ai'` in the gap `(a_{n+1}, a_n)`** (`n ≥ 2`) has radius `r = √(-b) ∈ (ρ_n, ρ_{n+1})` and phase
`|(2/3) r³ - (n + 1/4)π| ≤ 1.12/r³ ≤ 0.14`. -/
lemma airyAi'_zero_phase_of_gap {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb1 : airyZero (n + 1) < b)
    (hb2 : b < airyZero n) (hz : airyAi' b = 0) :
    airyZeroRoot n < √(-b) ∧ √(-b) < airyZeroRoot (n + 1) ∧
      |2 / 3 * (√(-b)) ^ 3 - ((n : ℝ) + 1 / 4) * π| ≤ 1.12 / (√(-b)) ^ 3 ∧
      |2 / 3 * (√(-b)) ^ 3 - ((n : ℝ) + 1 / 4) * π| ≤ 0.14 := by
  have hbneg : b < 0 := hb2.trans (airyZero_neg n)
  set r := √(-b) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hbneg)
  have hrsq : r ^ 2 = -b := Real.sq_sqrt (neg_nonneg.mpr hbneg.le)
  have hρ := two_lt_airyZeroRoot hn
  have hrρ : airyZeroRoot n < r := by
    rw [hr, airyZeroRoot]
    exact Real.sqrt_lt_sqrt (neg_nonneg.mpr (airyZero_nonpos n)) (by linarith)
  have hrσ : r < airyZeroRoot (n + 1) := by
    rw [hr, airyZeroRoot]
    exact Real.sqrt_lt_sqrt (neg_nonneg.mpr hbneg.le) (by linarith)
  have hz' : airyAi' (-(r ^ 2)) = 0 := by rw [hrsq, neg_neg]; exact hz
  obtain ⟨k, hk⟩ := airyAi'_zero_location_r (by linarith) hz'
  have hr3 : 8 < r ^ 3 := by
    nlinarith [pow_lt_pow_left₀ (hρ.trans hrρ) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  have hT : 1.12 / r ^ 3 ≤ 0.14 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hk' := abs_le.mp (hk.trans hT)
  have hρ3 := abs_le.mp (airyZero_phase_weak hn)
  have hσ3 := abs_le.mp (airyZero_phase_weak (by omega : 2 ≤ n + 1))
  have hlow : (2 / 3 : ℝ) * airyZeroRoot n ^ 3 < 2 / 3 * r ^ 3 := by
    have := pow_lt_pow_left₀ hrρ (airyZeroRoot_pos _).le (by norm_num : 3 ≠ 0); linarith
  have hhigh : (2 / 3 : ℝ) * r ^ 3 < 2 / 3 * airyZeroRoot (n + 1) ^ 3 := by
    have := pow_lt_pow_left₀ hrσ hr0.le (by norm_num : 3 ≠ 0); linarith
  push_cast at hσ3
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hkn : k = n := by
    have hk1 : (k : ℝ) < n + 1 := by
      by_contra hc; push Not at hc
      nlinarith [hk'.1, hk'.2, hσ3.2, hhigh]
    have hk2 : (n : ℝ) - 1 < k := by
      by_contra hc; push Not at hc
      nlinarith [hk'.1, hk'.2, hρ3.1, hlow]
    have h1' : k < (n : ℤ) + 1 := by exact_mod_cast hk1
    have h2' : (n : ℤ) - 1 < k := by exact_mod_cast hk2
    omega
  rw [hkn] at hk
  exact ⟨hrρ, hrσ, hk, hk.trans hT⟩

/-- The corner data for the zero `b_n` of `Ai'` (`n ≥ 2`). -/
lemma airyPrufer_corner (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0) (h1 : θ 0 < π)
    (hlo : π / 2 < θ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∃ b : ℝ, airyZero (n + 1) < b ∧ b < airyZero n ∧ θ b = -((n : ℝ) - 1) * π - π / 2 ∧
      |2 / 3 * (√(-b)) ^ 3 - ((n : ℝ) + 1 / 4) * π| ≤ 0.14 := by
  obtain ⟨b, hb1, hb2, hb3, hb4⟩ := airy_exists_airyAi'_zero hθ h0 h1 hlo (by omega : 1 ≤ n)
  exact ⟨b, hb1, hb2, hb4, (airyAi'_zero_phase_of_gap hn hb1 hb2 hb3).2.2.2⟩

/-- **Deviation of the Prüfer angle on a bracket `[a_{n+1}, a_n]`** (`n ≥ 2`): for `a_{n+1} ≤ x ≤ a_n`,
`|θ(x) + (2/3)√(-x)³ - 3π/4| ≤ π/2 + 0.14`. -/
theorem airy_prufer_deviation_bracket (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0)
    (h1 : θ 0 < π) (hlo : π / 2 < θ 0) {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx1 : airyZero (n + 1) ≤ x)
    (hx2 : x ≤ airyZero n) : |θ x + 2 / 3 * (√(-x)) ^ 3 - 3 * π / 4| ≤ π / 2 + 0.14 := by
  obtain ⟨b, hb1, hb2, hbθ, hbξ⟩ := airyPrufer_corner hθ h0 h1 hlo hn
  have hmono := airyPrufer_mono hθ
  have hθa := airy_prufer_airyZero hθ h0 h1 (by omega : 1 ≤ n)
  have hθa' := airy_prufer_airyZero hθ h0 h1 (by omega : 1 ≤ n + 1)
  have hρ3 := abs_le.mp (airyZero_phase_weak hn)
  have hσ3 := abs_le.mp (airyZero_phase_weak (by omega : 2 ≤ n + 1))
  push_cast at hσ3 hθa'
  have hbξ' := abs_le.mp hbξ
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hxneg : x ≤ 0 := hx2.trans (airyZero_nonpos n)
  have hbneg : b ≤ 0 := hb2.le.trans (airyZero_nonpos n)
  have hsx : (√(-x)) ^ 2 = -x := Real.sq_sqrt (neg_nonneg.mpr hxneg)
  -- ξ(x) comparisons via cubes of square roots
  have cube_mono : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → (√u) ^ 3 ≤ (√v) ^ 3 := fun hu huv =>
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt huv) 3
  have hρeq : airyZeroRoot n = √(-airyZero n) := rfl
  have hσeq : airyZeroRoot (n + 1) = √(-airyZero (n + 1)) := rfl
  have hxl : x ∈ Iic (0 : ℝ) := hxneg
  have hal : airyZero n ∈ Iic (0 : ℝ) := airyZero_nonpos n
  have hal' : airyZero (n + 1) ∈ Iic (0 : ℝ) := airyZero_nonpos _
  have hbl : b ∈ Iic (0 : ℝ) := hbneg
  rcases le_total x b with hxb | hxb
  · -- x ∈ [a_{n+1}, b]
    have t1 : θ (airyZero (n + 1)) ≤ θ x := hmono.monotoneOn hal' hxl hx1
    have t2 : θ x ≤ θ b := hmono.monotoneOn hxl hbl hxb
    have c1 : (√(-b)) ^ 3 ≤ (√(-x)) ^ 3 := cube_mono (by linarith) (by linarith)
    have c2 : (√(-x)) ^ 3 ≤ airyZeroRoot (n + 1) ^ 3 := by rw [hσeq]; exact cube_mono (by linarith) (by linarith)
    rw [abs_le]; constructor <;> linarith [hθa', hbθ, hbξ'.1, hbξ'.2, hσ3.1, hσ3.2]
  · have t1 : θ b ≤ θ x := hmono.monotoneOn hbl hxl hxb
    have t2 : θ x ≤ θ (airyZero n) := hmono.monotoneOn hxl hal hx2
    have c1 : airyZeroRoot n ^ 3 ≤ (√(-x)) ^ 3 := by rw [hρeq]; exact cube_mono (by linarith [airyZero_neg n]) (by linarith)
    have c2 : (√(-x)) ^ 3 ≤ (√(-b)) ^ 3 := cube_mono (by linarith [airyZero_neg n]) (by linarith)
    rw [abs_le]; constructor <;> linarith [hθa, hbθ, hbξ'.1, hbξ'.2, hρ3.1, hρ3.2]

/-- Every `x ≤ a_2` lies in some bracket `[a_{n+1}, a_n]`, `n ≥ 2`. -/
lemma exists_airyZero_bracket {x : ℝ} (hx : x ≤ airyZero 2) :
    ∃ n : ℕ, 2 ≤ n ∧ airyZero (n + 1) ≤ x ∧ x ≤ airyZero n := by
  have hex : ∃ m : ℕ, airyZero (m + 3) ≤ x := by
    have hY : 0 < -x := by linarith [airyZero_neg 2]
    refine ⟨⌈(-x) ^ 3⌉₊, ?_⟩
    set m := ⌈(-x) ^ 3⌉₊ + 3 with hm
    obtain ⟨h1, -⟩ := airyZero_abs_cube_bounds (n := m) (by omega)
    have hm1 : (-x) ^ 3 ≤ (m : ℝ) := by
      have := Nat.le_ceil ((-x) ^ 3)
      rw [hm]; push_cast; linarith
    have hm2 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg ⌈(-x) ^ 3⌉₊ : (0 : ℝ) ≤ _)]
    have : (-x) ^ 3 ≤ (-airyZero m) ^ 3 := by nlinarith
    have := le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (neg_nonneg.mpr (airyZero_nonpos m)) this
    linarith
  classical
  set m0 := Nat.find hex with hm0
  have hm0s : airyZero (m0 + 3) ≤ x := Nat.find_spec hex
  refine ⟨m0 + 2, by omega, hm0s, ?_⟩
  rcases Nat.eq_zero_or_pos m0 with h | h
  · rw [h]; exact hx
  · obtain ⟨m', hm'⟩ : ∃ m', m0 = m' + 1 := ⟨m0 - 1, by omega⟩
    have := Nat.find_min hex (show m' < m0 by omega)
    push Not at this
    rw [hm']
    have e : m' + 1 + 2 = m' + 3 := by ring
    rw [e]; exact this.le

/-- **Deviation of the Prüfer angle** (sharp amplitude `π/2`): for `y ≥ |a_2| = 4.0879…`,
`|θ(-y) + (2/3) y^{3/2} - 3π/4| ≤ π/2 + 0.14`. -/
theorem airy_prufer_deviation (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0)
    (h1 : θ 0 < π) (hlo : π / 2 < θ 0) {y : ℝ} (hy : -airyZero 2 ≤ y) :
    |θ (-y) + 2 / 3 * y ^ (3 / 2 : ℝ) - 3 * π / 4| ≤ π / 2 + 0.14 := by
  obtain ⟨n, hn, h1', h2'⟩ := exists_airyZero_bracket (x := -y) (by linarith)
  have := airy_prufer_deviation_bracket hθ h0 h1 hlo hn h1' h2'
  have hy0 : 0 < y := by linarith [airyZero_neg 2]
  rw [neg_neg] at this
  rwa [← sqrt_cube_eq_rpow hy0]

/-- **`θ(-y) ~ -ξ(y)`** with explicit rate: for `y ≥ |a_2|`, `ξ = (2/3) y^{3/2}`,
`|θ(-y) + ξ(y)| ≤ 4.1`, hence `|-θ(-y)/ξ(y) - 1| ≤ 4.1/ξ(y)`. -/
theorem airy_prufer_ratio (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (h0 : 0 < θ 0)
    (h1 : θ 0 < π) (hlo : π / 2 < θ 0) {y : ℝ} (hy : -airyZero 2 ≤ y) :
    |θ (-y) + 2 / 3 * y ^ (3 / 2 : ℝ)| ≤ 4.1 ∧
      |-θ (-y) / (2 / 3 * y ^ (3 / 2 : ℝ)) - 1| ≤ 4.1 / (2 / 3 * y ^ (3 / 2 : ℝ)) := by
  have h := airy_prufer_deviation hθ h0 h1 hlo hy
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hb : |θ (-y) + 2 / 3 * y ^ (3 / 2 : ℝ)| ≤ 4.1 := by
    have h' := abs_le.mp h
    rw [abs_le]; constructor <;> linarith [h'.1, h'.2]
  refine ⟨hb, ?_⟩
  have hy0 : 0 < y := by linarith [airyZero_neg 2]
  have hξ : 0 < 2 / 3 * y ^ (3 / 2 : ℝ) := by positivity
  have e : -θ (-y) / (2 / 3 * y ^ (3 / 2 : ℝ)) - 1 =
      -(θ (-y) + 2 / 3 * y ^ (3 / 2 : ℝ)) / (2 / 3 * y ^ (3 / 2 : ℝ)) := by
    field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hξ]
  exact div_le_div_of_nonneg_right hb hξ.le

/-- info: 'FormalResearch.Special.airy_prufer_airyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_prufer_airyZero

/-- info: 'FormalResearch.Special.airy_prufer_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_prufer_deviation

/-- info: 'FormalResearch.Special.airy_prufer_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_prufer_ratio

end Levels

end FormalResearch.Special

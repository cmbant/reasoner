module

public import FormalResearch.Special.DiscreteAiryKappaErmakov

/-!
# Sharp `κ`: the algebra of the single-site Ermakov match (plan K1, sharp constant, step 1)

For a profile `P` and `W = a² P_k P_{k-1} = 1 + s²` the Ermakov form `I_k(Y) = a² P_{k-1} Y_k² + a² P_k Y_{k-1}² - 2 a s Y_k Y_{k-1}` is a
positive quadratic form in `(Y_k, Y_{k-1})`.  If `Y_j = t √P_j c_j + e_j` with `c_k = cos θ`, `c_{k-1} = cos(θ + d)` and `cos d = u`, the
cosine part has `I = t² (1 + ε)` with `|ε| ≤ 4 W |s/√W - u|` (`ksh_match_alg`: the identity
`c² + c'² - 2u c c' = 1 - u²` and `W(1 - v²) = 1`, `v = s/√W`).  The error part has `I(e) ≤ 2 t² W (η₁² + η₀²)` and the square root of `I` is
subadditive (`ksh_tri`: the form is positive semidefinite).  Together (`ksh_I_close`):

`|√I_k(Y) - |t|| ≤ |t| (4 W ρ + √(2W) (η₁ + η₀))`

if `|s/√W - u| ≤ ρ` and `|e_j| ≤ η_j |t| √P_j`.

**Claim class: proved** (real algebra).  Used by `DiscreteAiryKappaSharpMatch`.
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- The binary quadratic form `α y² + β w² - 2γ y w`. -/
noncomputable def kshQ (α β γ y w : ℝ) : ℝ := α * y ^ 2 + β * w ^ 2 - 2 * γ * y * w

lemma kshQ_nonneg {α β γ y w : ℝ} (hα : 0 < α) (hγ : γ ^ 2 ≤ α * β) : 0 ≤ kshQ α β γ y w := by
  unfold kshQ
  have h : 0 ≤ α * (α * y ^ 2 + β * w ^ 2 - 2 * γ * y * w) := by
    nlinarith [sq_nonneg (α * y - γ * w), mul_nonneg (sub_nonneg.2 hγ) (sq_nonneg w)]
  exact nonneg_of_mul_nonneg_right h hα

/-- **Triangle inequality** for the square root of a positive semidefinite binary form. -/
lemma ksh_tri {α β γ y w y' w' : ℝ} (hα : 0 < α) (hγ : γ ^ 2 ≤ α * β) :
    √(kshQ α β γ (y + y') (w + w')) ≤ √(kshQ α β γ y w) + √(kshQ α β γ y' w') := by
  set q1 := kshQ α β γ y w with hq1
  set q2 := kshQ α β γ y' w' with hq2
  set B := α * y * y' + β * w * w' - γ * (y * w' + w * y') with hB
  have h1 : 0 ≤ q1 := kshQ_nonneg hα hγ
  have h2 : 0 ≤ q2 := kshQ_nonneg hα hγ
  have hsum : kshQ α β γ (y + y') (w + w') = q1 + q2 + 2 * B := by
    rw [hq1, hq2, hB]; unfold kshQ; ring
  have hdisc : discrim q2 (2 * B) q1 ≤ 0 := by
    apply discrim_le_zero
    intro t
    have := kshQ_nonneg (y := y + t * y') (w := w + t * w') hα hγ
    have e : kshQ α β γ (y + t * y') (w + t * w') = q2 * t * t + 2 * B * t + q1 := by
      rw [hq1, hq2, hB]; unfold kshQ; ring
    linarith
  have hB2 : B ^ 2 ≤ q1 * q2 := by
    unfold discrim at hdisc; nlinarith
  have hBle : B ≤ √q1 * √q2 := by
    have : B ≤ |B| := le_abs_self B
    have h3 : |B| ≤ √(q1 * q2) := Real.abs_le_sqrt hB2
    have h4 := Real.sqrt_mul h1 q2
    linarith
  rw [hsum]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have e1 : √q1 ^ 2 = q1 := Real.sq_sqrt h1
  have e2 : √q2 ^ 2 = q2 := Real.sq_sqrt h2
  nlinarith [hBle]

/-- The identity behind the phase: `cos²θ + cos²(θ + d) - 2 cos d cos θ cos(θ + d) = 1 - cos²d`. -/
lemma ksh_cos_id (θ d : ℝ) :
    Real.cos θ ^ 2 + Real.cos (θ + d) ^ 2 - 2 * Real.cos d * Real.cos θ * Real.cos (θ + d) = 1 - Real.cos d ^ 2 := by
  rw [Real.cos_add]
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq d
  nlinarith [h1, h2]

/-- **The cosine part**: `W (1 - v²) = 1`, `c² + c'² - 2 u c c' = 1 - u²`, `|c|, |c'| ≤ 1`, `|u|, |v| ≤ 1` give
`|W (c² + c'² - 2 v c c') - 1| ≤ 4 W |v - u|`. -/
lemma ksh_match_alg {W v u c c' : ℝ} (hW : 0 ≤ W) (hv : W * (1 - v ^ 2) = 1) (hc : c ^ 2 + c' ^ 2 - 2 * u * c * c' = 1 - u ^ 2)
    (hc1 : |c| ≤ 1) (hc2 : |c'| ≤ 1) (hu : |u| ≤ 1) (hv1 : |v| ≤ 1) :
    |W * (c ^ 2 + c' ^ 2 - 2 * v * c * c') - 1| ≤ 4 * W * |v - u| := by
  have e : W * (c ^ 2 + c' ^ 2 - 2 * v * c * c') - 1 = W * ((v - u) * (v + u - 2 * c * c')) := by
    linear_combination W * hc + hv
  rw [e, abs_mul, abs_mul, abs_of_nonneg hW]
  have h1 : |v + u - 2 * c * c'| ≤ 4 := by
    have a1 : |v + u| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have a2 : |2 * c * c'| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul hc1 hc2 (abs_nonneg _) (by norm_num)
      nlinarith
    have := abs_sub (v + u) (2 * c * c')
    linarith
  calc W * (|v - u| * |v + u - 2 * c * c'|) ≤ W * (|v - u| * 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) hW
    _ = 4 * W * |v - u| := by ring

/-- `|√(1 + x) - 1| ≤ |x|` for `x ≥ -1`. -/
lemma ksh_sqrt_one {x : ℝ} (hx : -1 ≤ x) : |√(1 + x) - 1| ≤ |x| := by
  have h0 : 0 ≤ 1 + x := by linarith
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (1 + x)
  have e : √(1 + x) - 1 = x / (√(1 + x) + 1) := by
    field_simp; nlinarith [hs]
  rw [e, abs_div, abs_of_pos (by linarith : 0 < √(1 + x) + 1)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg x]

/-- Pure ring identity for the cosine part. -/
lemma ksh_ring_id (a sp sq v t c1 c0 : ℝ) :
    kshQ (a ^ 2 * sq ^ 2) (a ^ 2 * sp ^ 2) (a * (v * (a * sp * sq))) (t * sp * c1) (t * sq * c0) =
      t ^ 2 * ((a ^ 2 * sp ^ 2 * sq ^ 2) * (c1 ^ 2 + c0 ^ 2 - 2 * v * c1 * c0)) := by
  unfold kshQ; ring

/-- **The error part**: `α p = W`, `β p' = W`, `|e₁| ≤ η₁|t|√p`, `|e₀| ≤ η₀|t|√p'` give `√Q(e) ≤ |t|√(2W)(η₁ + η₀)`. -/
lemma ksh_err {α β γ e1 e0 t W p p' η1 η0 : ℝ} (hα0 : 0 < α) (hγ2' : (-γ) ^ 2 ≤ α * β) (hW0 : 0 < W) (hp : 0 < p)
    (hp' : 0 < p') (hαp : α * p = W) (hβp : β * p' = W)
    (he1 : |e1| ≤ η1 * (|t| * √p)) (he0 : |e0| ≤ η0 * (|t| * √p')) (hη1 : 0 ≤ η1) (hη0 : 0 ≤ η0) :
    √(kshQ α β γ e1 e0) ≤ |t| * (√(2 * W) * (η1 + η0)) := by
  have hsp := Real.sq_sqrt hp.le
  have hsp' := Real.sq_sqrt hp'.le
  have hβ0 : 0 < β := by
    have : 0 < β * p' := by rw [hβp]; exact hW0
    exact (mul_pos_iff_of_pos_right hp').1 this
  have hpos := kshQ_nonneg (y := e1) (w := e0) hα0 hγ2'
  have hpos' : 0 ≤ α * e1 ^ 2 + β * e0 ^ 2 + 2 * γ * e1 * e0 := by
    unfold kshQ at hpos; nlinarith [hpos]
  have b1 : e1 ^ 2 ≤ η1 ^ 2 * (t ^ 2 * p) := by
    have := sq_le_sq' (abs_le.1 he1).1 (abs_le.1 he1).2
    have e : (η1 * (|t| * √p)) ^ 2 = η1 ^ 2 * (t ^ 2 * p) := by
      rw [mul_pow, mul_pow, sq_abs, hsp]
    rw [e] at this; exact this
  have b0 : e0 ^ 2 ≤ η0 ^ 2 * (t ^ 2 * p') := by
    have := sq_le_sq' (abs_le.1 he0).1 (abs_le.1 he0).2
    have e : (η0 * (|t| * √p')) ^ 2 = η0 ^ 2 * (t ^ 2 * p') := by
      rw [mul_pow, mul_pow, sq_abs, hsp']
    rw [e] at this; exact this
  have c1' : α * e1 ^ 2 ≤ t ^ 2 * W * η1 ^ 2 := by
    calc α * e1 ^ 2 ≤ α * (η1 ^ 2 * (t ^ 2 * p)) := mul_le_mul_of_nonneg_left b1 hα0.le
      _ = t ^ 2 * W * η1 ^ 2 := by rw [← hαp]; ring
  have c0' : β * e0 ^ 2 ≤ t ^ 2 * W * η0 ^ 2 := by
    calc β * e0 ^ 2 ≤ β * (η0 ^ 2 * (t ^ 2 * p')) := mul_le_mul_of_nonneg_left b0 hβ0.le
      _ = t ^ 2 * W * η0 ^ 2 := by rw [← hβp]; ring
  have hQe : kshQ α β γ e1 e0 ≤ 2 * (t ^ 2 * W * (η1 ^ 2 + η0 ^ 2)) := by
    unfold kshQ
    nlinarith [hpos', c1', c0']
  have hrhs : 2 * (t ^ 2 * W * (η1 ^ 2 + η0 ^ 2)) ≤ (|t| * (√(2 * W) * (η1 + η0))) ^ 2 := by
    have e : (|t| * (√(2 * W) * (η1 + η0))) ^ 2 = t ^ 2 * (2 * W) * (η1 + η0) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt (by positivity)]
      ring
    rw [e]
    have h1 : 0 ≤ t ^ 2 * W * (η1 * η0) := by positivity
    nlinarith [h1]
  exact (Real.sqrt_le_sqrt (hQe.trans hrhs)).trans (le_of_eq (Real.sqrt_sq (by positivity)))

/-- **The cosine part**: `√Q(ỹ, w̃) = |t| √Z`, `|Z - 1| ≤ 4Wρ`. -/
lemma ksh_cosine {α β γ yt wt t W v u c1 c0 ρ : ℝ} (hW0 : 0 < W)
    (hQt : kshQ α β γ yt wt = t ^ 2 * (W * (c1 ^ 2 + c0 ^ 2 - 2 * v * c1 * c0)))
    (hv2 : W * (1 - v ^ 2) = 1) (hv0 : 0 ≤ v) (hv1 : |v| ≤ 1)
    (hcos : c1 ^ 2 + c0 ^ 2 - 2 * u * c1 * c0 = 1 - u ^ 2) (hc1 : |c1| ≤ 1) (hc0 : |c0| ≤ 1) (hu : |u| ≤ 1)
    (hρ : |v - u| ≤ ρ) :
    abs (√(kshQ α β γ yt wt) - |t|) ≤ |t| * (4 * W * ρ) := by
  set Z := W * (c1 ^ 2 + c0 ^ 2 - 2 * v * c1 * c0) with hZ
  have hZ0 : 0 ≤ Z := by
    have h1 : 2 * v * c1 * c0 ≤ c1 ^ 2 + c0 ^ 2 := by
      nlinarith [mul_nonneg hv0 (sq_nonneg (c1 - c0)),
        mul_nonneg (sub_nonneg.2 (abs_le.1 hv1).2) (add_nonneg (sq_nonneg c1) (sq_nonneg c0))]
    exact mul_nonneg hW0.le (by linarith)
  have hZ1 : |Z - 1| ≤ 4 * W * ρ := by
    have := ksh_match_alg hW0.le hv2 hcos hc1 hc0 hu hv1
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left hρ (by positivity)
  have hQt' : √(kshQ α β γ yt wt) = |t| * √Z := by
    rw [hQt, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  rw [hQt']
  have e : |t| * √Z - |t| = |t| * (√(1 + (Z - 1)) - 1) := by
    rw [show 1 + (Z - 1) = Z by ring]; ring
  rw [e, abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_left ((ksh_sqrt_one (by linarith)).trans hZ1) (abs_nonneg _)

/-- **Real form of the single-site match** (`ksh_I_close`): `a, p, p' > 0`, `W = a² p p' ≥ 1`, `s ≥ 0`, `s² = W - 1`,
`y = t √p c₁ + e₁`, `w = t √p' c₀ + e₀`, the cosine data `c₁² + c₀² - 2u c₁c₀ = 1 - u²`, `|e₁| ≤ η₁ |t| √p`, `|e₀| ≤ η₀ |t| √p'`,
`|s/√W - u| ≤ ρ`: `|√(a²p' y² + a²p w² - 2 a s y w) - |t|| ≤ |t| (4 W ρ + √(2W)(η₁ + η₀))`. -/
lemma ksh_I_close_real {a p p' s y w t u c1 c0 e1 e0 η1 η0 ρ : ℝ} (ha : 0 < a) (hp : 0 < p) (hp' : 0 < p')
    (hW : 1 ≤ a ^ 2 * p * p') (hs0 : 0 ≤ s) (hs2 : s ^ 2 = a ^ 2 * p * p' - 1)
    (hy : y = t * √p * c1 + e1) (hw : w = t * √p' * c0 + e0)
    (hcos : c1 ^ 2 + c0 ^ 2 - 2 * u * c1 * c0 = 1 - u ^ 2) (hc1 : |c1| ≤ 1) (hc0 : |c0| ≤ 1) (hu : |u| ≤ 1)
    (he1 : |e1| ≤ η1 * (|t| * √p)) (he0 : |e0| ≤ η0 * (|t| * √p')) (hη1 : 0 ≤ η1) (hη0 : 0 ≤ η0)
    (hρ : |s / √(a ^ 2 * p * p') - u| ≤ ρ) :
    abs (√(a ^ 2 * p' * y ^ 2 + a ^ 2 * p * w ^ 2 - 2 * a * s * y * w) - |t|) ≤
      |t| * (4 * (a ^ 2 * p * p') * ρ + √(2 * (a ^ 2 * p * p')) * (η1 + η0)) := by
  obtain ⟨W, hWdef⟩ : ∃ W, W = a ^ 2 * p * p' := ⟨_, rfl⟩
  rw [← hWdef] at hW hs2 hρ ⊢
  have hW0 : 0 < W := by rw [hWdef]; positivity
  have hsp := Real.sq_sqrt hp.le
  have hsp' := Real.sq_sqrt hp'.le
  have hsW := Real.sq_sqrt hW0.le
  have hsW0 : 0 < √W := Real.sqrt_pos.2 hW0
  obtain ⟨α, hα⟩ : ∃ α, α = a ^ 2 * p' := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = a ^ 2 * p := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = a * s := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hαp : α * p = W := by rw [hα, hWdef]; ring
  have hβp : β * p' = W := by rw [hβ, hWdef]
  have hγ2 : γ ^ 2 ≤ α * β := by
    have e1 : γ ^ 2 = a ^ 2 * (W - 1) := by rw [hγ, mul_pow, hs2]
    have e2 : α * β = a ^ 2 * W := by rw [hα, hβ, hWdef]; ring
    rw [e1, e2]; nlinarith [sq_nonneg a]
  have hγ2' : (-γ) ^ 2 ≤ α * β := by rw [neg_sq]; exact hγ2
  have hI : a ^ 2 * p' * y ^ 2 + a ^ 2 * p * w ^ 2 - 2 * a * s * y * w = kshQ α β γ y w := by
    unfold kshQ; rw [hα, hβ, hγ]; ring
  rw [hI]
  obtain ⟨v, hvdef⟩ : ∃ v, v = s / √W := ⟨_, rfl⟩
  rw [← hvdef] at hρ
  have hv2 : W * (1 - v ^ 2) = 1 := by
    rw [hvdef, div_pow, hsW, hs2]; field_simp; ring
  have hv0 : 0 ≤ v := by rw [hvdef]; positivity
  have hv1 : |v| ≤ 1 := by
    rw [abs_of_nonneg hv0]
    have h1 : 0 < 1 - v ^ 2 := by
      by_contra hc
      have hc := not_lt.1 hc
      have := mul_nonpos_of_nonneg_of_nonpos hW0.le hc
      linarith
    exact ((sq_lt_one_iff₀ hv0).1 (by linarith)).le
  have hQt : kshQ α β γ (t * √p * c1) (t * √p' * c0) = t ^ 2 * (W * (c1 ^ 2 + c0 ^ 2 - 2 * v * c1 * c0)) := by
    have e1' : √W = a * √p * √p' := by
      rw [show W = (a * √p * √p') ^ 2 by rw [hWdef, mul_pow, mul_pow, hsp, hsp']]
      exact Real.sqrt_sq (by positivity)
    have hs' : s = v * (a * √p * √p') := by rw [hvdef, ← e1']; field_simp
    have key := ksh_ring_id a (√p) (√p') v t c1 c0
    rw [hsp, hsp'] at key
    rw [hα, hβ, hγ, hs', hWdef]
    exact key
  have hd1 := ksh_cosine hW0 hQt hv2 hv0 hv1 hcos hc1 hc0 hu hρ
  have hd2 := ksh_err hα0 hγ2' hW0 hp hp' hαp hβp he1 he0 hη1 hη0
  have hup : √(kshQ α β γ y w) ≤ √(kshQ α β γ (t * √p * c1) (t * √p' * c0)) + √(kshQ α β γ e1 e0) := by
    rw [hy, hw]; exact ksh_tri hα0 hγ2
  have hdn : √(kshQ α β γ (t * √p * c1) (t * √p' * c0)) ≤ √(kshQ α β γ y w) + √(kshQ α β γ e1 e0) := by
    have h := ksh_tri (α := α) (β := β) (γ := γ) (y := y) (w := w) (y' := -e1) (w' := -e0) hα0 hγ2
    have e1' : y + -e1 = t * √p * c1 := by rw [hy]; ring
    have e2' : w + -e0 = t * √p' * c0 := by rw [hw]; ring
    have e3 : kshQ α β γ (-e1) (-e0) = kshQ α β γ e1 e0 := by unfold kshQ; ring
    rw [e1', e2', e3] at h; exact h
  rw [abs_le] at hd1 ⊢
  constructor <;> linarith [hd1.1, hd1.2, hup, hdn, hd2]

/-- **The single-site Ermakov match** for `kermI`: with `W = a_k² P_k P_{k-1}`, `Y_k = t √P_k c₁ + e₁`, `Y_{k-1} = t √P_{k-1} c₀ + e₀`, the cosine data
`c₁² + c₀² - 2 u c₁ c₀ = 1 - u²`, `|e_j| ≤ η_j |t| √P_j` and `|s_k/√W - u| ≤ ρ`:
`|√I_k(Y) - |t|| ≤ |t| (4 W ρ + √(2W)(η₁ + η₀))`. -/
theorem ksh_I_close {a P Y : ℤ → ℝ} {k : ℤ} {t u c1 c0 e1 e0 η1 η0 ρ : ℝ} (ha : 0 < a k) (hp : 0 < P k)
    (hp' : 0 < P (k - 1)) (hW : 1 ≤ a k ^ 2 * P k * P (k - 1))
    (hy : Y k = t * √(P k) * c1 + e1) (hw : Y (k - 1) = t * √(P (k - 1)) * c0 + e0)
    (hcos : c1 ^ 2 + c0 ^ 2 - 2 * u * c1 * c0 = 1 - u ^ 2) (hc1 : |c1| ≤ 1) (hc0 : |c0| ≤ 1) (hu : |u| ≤ 1)
    (he1 : |e1| ≤ η1 * (|t| * √(P k))) (he0 : |e0| ≤ η0 * (|t| * √(P (k - 1)))) (hη1 : 0 ≤ η1) (hη0 : 0 ≤ η0)
    (hρ : |kermS a P k / √(a k ^ 2 * P k * P (k - 1)) - u| ≤ ρ) :
    abs (√(kermI a P Y k) - |t|) ≤
      |t| * (4 * (a k ^ 2 * P k * P (k - 1)) * ρ + √(2 * (a k ^ 2 * P k * P (k - 1))) * (η1 + η0)) := by
  have := ksh_I_close_real (a := a k) (p := P k) (p' := P (k - 1)) (s := kermS a P k) (y := Y k) (w := Y (k - 1))
    ha hp hp' hW (kermS_nonneg a P k) (kermS_sq hW) hy hw hcos hc1 hc0 hu he1 he0 hη1 hη0 hρ
  unfold kermI
  exact this

/-- `|s/√W - u| ≤ |1 - u² - 1/W|/u` (`s ≥ 0`, `s² = W - 1`, `W ≥ 1`, `u > 0`). -/
lemma ksh_v_close {s W u : ℝ} (hW : 1 ≤ W) (hs0 : 0 ≤ s) (hs2 : s ^ 2 = W - 1) (hu : 0 < u) :
    |s / √W - u| ≤ |1 - u ^ 2 - 1 / W| / u := by
  have hW0 : 0 < W := by linarith
  have hsW := Real.sq_sqrt hW0.le
  have hsW0 : 0 < √W := Real.sqrt_pos.2 hW0
  set v := s / √W with hv
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hv2 : v ^ 2 = 1 - 1 / W := by
    rw [hv, div_pow, hsW, hs2]; field_simp
  have e : v ^ 2 - u ^ 2 = (v - u) * (v + u) := by ring
  have h1 : |v - u| * (v + u) = |1 - u ^ 2 - 1 / W| := by
    have : v ^ 2 - u ^ 2 = 1 - u ^ 2 - 1 / W := by rw [hv2]; ring
    rw [← this, e, abs_mul, abs_of_pos (by linarith : 0 < v + u)]
  rw [le_div_iff₀ hu, ← h1]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- info: 'FormalResearch.Special.ksh_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_tri

/-- info: 'FormalResearch.Special.ksh_cos_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_cos_id

/-- info: 'FormalResearch.Special.ksh_match_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_match_alg

/-- info: 'FormalResearch.Special.ksh_I_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_I_close

/-- info: 'FormalResearch.Special.ksh_v_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_v_close

end FormalResearch.Special

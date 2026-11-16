module

public import FormalResearch.Special.DiscreteAiryLimitChains2Twist

/-!
# The actual `6j` chain: the turn from the triangle, both branches `τ = ±1`, and infinitely many realisations

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:racah-class` (`eq:D6linear`, `eq:racahTurnType`,
`rho_* = 2αβ sinθ/γ`), `thm:racahAiryConnection`.

## Part 1.  The turn is derived from the triangle (proved)

For shape data `α, β > 0` and `x = cos θ ∈ (-1, 1)`, `γ² = α² + β² - 2αβx` (the limiting triangle with sides `α, β, γ`),
`P = 1/(4α²)`, `Q = 1/(4β²)` and `q_* = 2αβ √(1-x²)/γ` (= `ρ_*`, twice the height of the triangle on the side `γ`):

* `1 - P q_*² = (α-βx)²/γ²`, `1 - Q q_*² = (β-αx)²/γ²` (positive unless the triangle is right-angled at the vertex opposite
  `α` resp. `β`: `α = βx` resp. `β = αx`; the paper's excluded `ε = 0` triangles);
* if `(α-βx)(β-αx) < 0` then `Φ_{+1}(q_*²) = 0` and `1 - x > 0` (`τ = +1`); if `(α-βx)(β-αx) > 0` then `Φ_{-1}(q_*²) = 0`
  and `1 + x > 0` (`τ = -1`).  (`cos A_α = (β-αx)/γ`, `cos A_β = (α-βx)/γ`: the sign is `τ = sgn ε`, `ε = -cos A_α cos A_β`.)

`racah_chain_airy_geom_pos`, `racah_chain_airy_geom_neg`: the Airy limit of the actual `6j` chain (resp. the twisted chain
`(-1)^k Ŷ_k` for `τ = -1`, from `racah_class_chain_neg`) with **no turn hypotheses**: only `α, β > 0`, `x ∈ (-1,1)` and the
sign of `(α-βx)(β-αx)`, for every finite Racah system, physical `c`, scale `h = δ³ ≤ δ₀³` with `A h = α`, `B h = β`,
`cosA A B C = x`.

## Part 2.  Realisations (proved; the congruence conditions)

`racah_realisation`: let `P, Q, R, m, n` be integers with a strict triangle `|P-Q| < R < P+Q` and the parities
`R` odd, `P ≡ n+1`, `Q ≡ m+1 (mod 2)`.  Then for every `ε > 0` and `α > 0` there are integers `a, b, c`, a finite Racah system
`RacahSystem a b m n D'`, a physical `c = c_i` and a scale `0 < h ≤ ε` with `A h = α`, `B h = α Q/P`,
`cosA A B C = (P²+Q²-R²)/(2PQ)`.  Explicitly `(2A, 2B, 2C) = t (P, Q, R)`, `t = 2u+1` odd and large:
`a = (tP-n-1)/2`, `b = (tQ-m-1)/2`, `c = (tR-1)/2`, `h = 2α/(tP)`.

**Exact obstruction (not formalised, elementary).**  For integer `a,b,c,m,n`, `(2A,2B,2C) = (2a+n+1, 2b+m+1, 2c+1)` has
`2C` odd and `2A ≡ n+1`, `2B ≡ m+1 (mod 2)`.  If `A : B : C = P : Q : R` with `gcd(P,Q,R) = 1` then `(2A,2B,2C) = t(P,Q,R)`
with `t = gcd`, and `2C` odd forces `t` and `R` odd and then `P ≡ n+1`, `Q ≡ m+1`.  So the parity conditions of
`racah_realisation` are necessary and sufficient for a direction `(P:Q:R)` (rational triangle) to occur with integer data;
directions with `R` even (e.g. the equilateral-type `(1,1,2)` excluded anyway by strictness, `(3,4,6)`, `(2,3,4)`) and
irrational directions never occur.  Quarter-turn irrational ratios `α/β ∉ ℚ` or `γ/β ∉ ℚ` (non-Pythagorean angle) have no exact
realisation, only approximate ones, which need the uniformity in `(α, β, x)` that is not formalised.

`racah_chain_airy_family_pos/_neg`: composition.  For every `ε > 0` the realisation of `racah_realisation` satisfies the
Airy conclusion `AiryOutAt` with constants independent of the realisation; `τ = +1` iff `R² < |P²-Q²|`, `τ = -1` iff
`R² > |P²-Q²|` (`R² = |P² - Q²|` is a right angle and excluded).  Example `(P,Q,R) = (6,2,5)`, `m = n = -1`: `τ = +1`,
`α/β = 3`, `x = 5/8`, `(a,b,c) = (t·3 + 0, ...)`: `(a,b,c) = (3u+3, u+1, 5u+2)` (checked with exact rationals for
`t = 1,…,11`: `cMin ≤ c ≤ cMax`).

Claim class: **proved**.

## Not formalised

`κ`, `κ ≠ 0`; uniformity in `(α, β, x)`; non-Pythagorean shapes; half-integer data (`DiscreteAiryLimitChains2Half*`).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `γ² = α² + β² - 2αβ x` (the third side of the limiting triangle). -/
noncomputable def racahGamma2 (α β x : ℝ) : ℝ := α ^ 2 + β ^ 2 - 2 * α * β * x

/-- The turning point `q_* = ρ_* = 2αβ sinθ/γ` of the centred Racah chain. -/
noncomputable def racahQs (α β x : ℝ) : ℝ := 2 * α * β * Real.sqrt (1 - x ^ 2) / Real.sqrt (racahGamma2 α β x)

lemma racahGamma2_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx : x < 1) : 0 < racahGamma2 α β x := by
  unfold racahGamma2
  nlinarith [sq_nonneg (α - β), mul_pos hα hβ]

lemma racahQs_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) : 0 < racahQs α β x := by
  unfold racahQs
  have := racahGamma2_pos hα hβ hx2
  have h1 : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  positivity

lemma racahQs_sq {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) :
    racahQs α β x ^ 2 = 4 * α ^ 2 * β ^ 2 * (1 - x ^ 2) / racahGamma2 α β x := by
  unfold racahQs
  have hg := racahGamma2_pos hα hβ hx2
  rw [div_pow, mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt hg.le]
  ring

lemma racah_one_sub_P {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) :
    1 - 1 / (4 * α ^ 2) * racahQs α β x ^ 2 = (α - β * x) ^ 2 / racahGamma2 α β x := by
  rw [racahQs_sq hα hβ hx1 hx2]
  have hg := (racahGamma2_pos hα hβ hx2).ne'
  have hdef : racahGamma2 α β x = α ^ 2 + β ^ 2 - 2 * α * β * x := rfl
  generalize racahGamma2 α β x = g at hg hdef ⊢
  field_simp
  rw [hdef]
  ring

lemma racah_one_sub_Q {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) :
    1 - 1 / (4 * β ^ 2) * racahQs α β x ^ 2 = (β - α * x) ^ 2 / racahGamma2 α β x := by
  rw [racahQs_sq hα hβ hx1 hx2]
  have hg := (racahGamma2_pos hα hβ hx2).ne'
  have hdef : racahGamma2 α β x = α ^ 2 + β ^ 2 - 2 * α * β * x := rfl
  generalize racahGamma2 α β x = g at hg hdef ⊢
  field_simp
  rw [hdef]
  ring

/-- The geometric value of `Φ_τ(q_*²)`: `τ(x - q_*²/(4αβ)) - ẽ(q_*²) = (-τ (α-βx)(β-αx) - |(α-βx)(β-αx)|)/γ²`. -/
lemma racah_Phi_geom {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1) (τ : ℝ) :
    Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (racahQs α β x ^ 2) =
      (-τ * ((α - β * x) * (β - α * x)) - |(α - β * x) * (β - α * x)|) / racahGamma2 α β x := by
  have hg := racahGamma2_pos hα hβ hx2
  have hsq : Real.sqrt (1 / (4 * α ^ 2) * (1 / (4 * β ^ 2))) = 1 / (4 * (α * β)) := by
    have e : 1 / (4 * α ^ 2) * (1 / (4 * β ^ 2)) = (1 / (4 * (α * β))) ^ 2 := by field_simp
    rw [e, Real.sqrt_sq (by positivity)]
  have hE : etilde (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (racahQs α β x ^ 2) =
      |(α - β * x) * (β - α * x)| / racahGamma2 α β x := by
    unfold etilde
    rw [racah_one_sub_P hα hβ hx1 hx2, racah_one_sub_Q hα hβ hx1 hx2]
    have e : (α - β * x) ^ 2 / racahGamma2 α β x * ((β - α * x) ^ 2 / racahGamma2 α β x) =
        (((α - β * x) * (β - α * x)) / racahGamma2 α β x) ^ 2 := by ring
    rw [e, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hg]
  unfold Phi
  rw [hsq, hE, racahQs_sq hα hβ hx1 hx2]
  have hg' := hg.ne'
  have hdef : racahGamma2 α β x = α ^ 2 + β ^ 2 - 2 * α * β * x := rfl
  generalize racahGamma2 α β x = g at hg' hdef ⊢
  field_simp
  rw [hdef]
  ring

/-- **The turn of the `6j` chain, `τ = +1` branch.** -/
theorem racah_turn_geom_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) :
    0 < racahQs α β x ∧ 0 < 1 - 1 * x ∧ 0 < 1 - 1 / (4 * α ^ 2) * racahQs α β x ^ 2 ∧
      0 < 1 - 1 / (4 * β ^ 2) * racahQs α β x ^ 2 ∧
      Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x ^ 2) = 0 := by
  have hg := racahGamma2_pos hα hβ hx2
  have ha : α - β * x ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  have hb : β - α * x ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  refine ⟨racahQs_pos hα hβ hx1 hx2, by linarith, ?_, ?_, ?_⟩
  · rw [racah_one_sub_P hα hβ hx1 hx2]; positivity
  · rw [racah_one_sub_Q hα hβ hx1 hx2]; positivity
  · rw [racah_Phi_geom hα hβ hx1 hx2, abs_of_neg hprod]; ring

/-- **The turn of the `6j` chain, `τ = -1` branch.** -/
theorem racah_turn_geom_neg {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) :
    0 < racahQs α β x ∧ 0 < 1 - (-1) * x ∧ 0 < 1 - 1 / (4 * α ^ 2) * racahQs α β x ^ 2 ∧
      0 < 1 - 1 / (4 * β ^ 2) * racahQs α β x ^ 2 ∧
      Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x ^ 2) = 0 := by
  have hg := racahGamma2_pos hα hβ hx2
  have ha : α - β * x ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  have hb : β - α * x ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  refine ⟨racahQs_pos hα hβ hx1 hx2, by linarith, ?_, ?_, ?_⟩
  · rw [racah_one_sub_P hα hβ hx1 hx2]; positivity
  · rw [racah_one_sub_Q hα hβ hx1 hx2]; positivity
  · rw [racah_Phi_geom hα hβ hx1 hx2, abs_of_pos hprod]; ring

/-- **Airy limit of the actual `6j` chain from the geometric data, `τ = +1`** (`thm:racahAiryConnection`, no turn
hypotheses). -/
theorem racah_chain_airy_geom_pos (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ (i : Fin (D' + 1))
        (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        AiryOutAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (racah6jY a b c m n)
          (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity) (m : ℝ) (n : ℝ) 1 x
      (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) (m : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h (racah6jY a b c m n) _ hh hhδ (fun k hk => ?_) (fun k => racah_chain_abs_le a b c m n hsys i hc k)
  have := racah_class_chain a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

/-- **Airy limit of the actual `6j` chain from the geometric data, `τ = -1`** (the twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_airy_geom_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ (i : Fin (D' + 1))
        (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        AiryOutAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x)
          (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j)
          (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity) (m : ℝ) (n : ℝ) (-1) x
      (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) (m : ℚ) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h _ _ hh hhδ (fun k hk => ?_) (fun k => ?_)
  · have := racah_class_chain_neg a b c m n h hh hA hB k hk
    rw [hAh, hBh, hx] at this
    exact this
  · have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
    rw [abs_mul, h1, one_mul]
    exact racah_chain_abs_le a b c m n hsys i hc k

/-- info: 'FormalResearch.Special.racah_turn_geom_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_turn_geom_pos

/-- info: 'FormalResearch.Special.racah_turn_geom_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_turn_geom_neg

/-- info: 'FormalResearch.Special.racah_chain_airy_geom_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_geom_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_geom_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_geom_neg

/-! ### Part 2: realisations -/

/-- The explicit family `(2A, 2B, 2C) = (2u+1)(P, Q, R)`: integers `a, b, c`, a finite Racah system and a physical `c`. -/
theorem racah_family_ints (P Q R m n : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1)) (u : ℕ)
    (hu : |m - n| + |m + n| + 1 ≤ (u : ℤ)) :
    ∃ (a b c : ℤ) (D' : ℕ), wA (a : ℚ) (n : ℚ) = (2 * (u : ℝ) + 1) * P / 2 ∧
      wB (b : ℚ) (m : ℚ) = (2 * (u : ℝ) + 1) * Q / 2 ∧ wC (c : ℚ) = (2 * (u : ℝ) + 1) * R / 2 ∧
      RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
      ∃ i : Fin (D' + 1), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i := by
  obtain ⟨wa, hwa⟩ := hpP
  obtain ⟨wb, hwb⟩ := hpQ
  obtain ⟨wc, hwc⟩ := hpR
  set a : ℤ := u * P + wa with ha
  set b : ℤ := u * Q + wb with hb
  set c : ℤ := u * R + wc with hc
  have hwaq : (P : ℚ) - n - 1 = wa + wa := by exact_mod_cast hwa
  have hwbq : (Q : ℚ) - m - 1 = wb + wb := by exact_mod_cast hwb
  have hwcq : (R : ℚ) = 2 * wc + 1 := by exact_mod_cast hwc
  have hAq : (a : ℚ) + ((n : ℚ) + 1) / 2 = (2 * (u : ℚ) + 1) * P / 2 := by
    rw [ha]; push_cast; linarith
  have hBq : (b : ℚ) + ((m : ℚ) + 1) / 2 = (2 * (u : ℚ) + 1) * Q / 2 := by
    rw [hb]; push_cast; linarith
  have hCq : (c : ℚ) = ((2 * (u : ℚ) + 1) * R - 1) / 2 := by
    rw [hc]; push_cast; linarith
  have hlab : RacahLabels (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) :=
    ⟨⟨2 * a, by push_cast; ring⟩, ⟨2 * b, by push_cast; ring⟩, ⟨2 * m, by push_cast; ring⟩, ⟨m - n, by push_cast; ring⟩⟩
  have ht : (0 : ℚ) < 2 * (u : ℚ) + 1 := by positivity
  have h1 : (P : ℚ) - Q ≤ R - 1 := by
    have : P - Q ≤ R - 1 := by have := abs_lt.1 hRlo; omega
    exact_mod_cast this
  have h2 : -((R : ℚ) - 1) ≤ P - Q := by
    have : -(R - 1) ≤ P - Q := by have := abs_lt.1 hRlo; omega
    exact_mod_cast this
  have h3 : (1 : ℚ) ≤ P + Q - R := by
    have : 1 ≤ P + Q - R := by omega
    exact_mod_cast this
  have hmn1 : (|(m : ℚ) - n|) + |(m : ℚ) + n| + 1 ≤ (u : ℚ) := by
    have : ((|m - n| + |m + n| + 1 : ℤ) : ℚ) ≤ ((u : ℤ) : ℚ) := by exact_mod_cast hu
    push_cast at this
    exact this
  have hlow : cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) ≤ (c : ℚ) := by
    rw [cMin_centered, hAq, hBq, hCq]
    have hab : |(2 * (u : ℚ) + 1) * P / 2 - (2 * (u : ℚ) + 1) * Q / 2| ≤ (2 * (u : ℚ) + 1) * (R - 1) / 2 := by
      rw [abs_le]; constructor <;> nlinarith
    have := abs_nonneg ((m : ℚ) + n)
    have := abs_nonneg ((m : ℚ) - n)
    nlinarith
  have hup : (c : ℚ) ≤ cMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) := by
    rw [cMax_centered, hAq, hBq, hCq]
    have := abs_nonneg ((m : ℚ) + n)
    have := abs_nonneg ((m : ℚ) - n)
    nlinarith
  obtain ⟨D', hsys⟩ := RacahSystem.exists hlab (hlow.trans hup)
  refine ⟨a, b, c, D', ?_, ?_, ?_, hsys, ?_⟩
  · unfold wA; push_cast
    have e : ((a : ℚ) : ℝ) + (((n : ℚ) : ℝ) + 1) / 2 = (((2 * (u : ℚ) + 1) * P / 2 : ℚ) : ℝ) := by
      rw [← hAq]; push_cast; ring
    push_cast at e
    exact e
  · unfold wB; push_cast
    have e : ((b : ℚ) : ℝ) + (((m : ℚ) : ℝ) + 1) / 2 = (((2 * (u : ℚ) + 1) * Q / 2 : ℚ) : ℝ) := by
      rw [← hBq]; push_cast; ring
    push_cast at e
    exact e
  · unfold wC
    have e : ((c : ℚ) : ℝ) = ((((2 * (u : ℚ) + 1) * R - 1) / 2 : ℚ) : ℝ) := by rw [hCq]
    push_cast at e ⊢
    linarith
  · obtain ⟨z, hz⟩ : ∃ z : ℤ, cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) = (z : ℚ) :=
      ⟨max |a - b| |b + m - a - n|, by unfold cMin; push_cast; rfl⟩
    have hcz : 0 ≤ c - z := by
      have : (z : ℚ) ≤ (c : ℚ) := hz ▸ hlow
      have : z ≤ c := by exact_mod_cast this
      omega
    have hD : (D' : ℚ) = cMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) - cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) := hsys.dim
    have hi : ((c - z).toNat : ℚ) = (c : ℚ) - z := by
      have : (((c - z).toNat : ℕ) : ℤ) = c - z := Int.toNat_of_nonneg hcz
      have h4 : ((((c - z).toNat : ℕ) : ℤ) : ℚ) = ((c - z : ℤ) : ℚ) := by rw [this]
      push_cast at h4
      exact h4
    have hlt : (c - z).toNat < D' + 1 := by
      have : ((c - z).toNat : ℚ) ≤ D' := by rw [hi, hD, hz]; linarith
      have : (c - z).toNat ≤ D' := by exact_mod_cast this
      omega
    refine ⟨⟨(c - z).toNat, hlt⟩, ?_⟩
    unfold cPt
    show (c : ℚ) = cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) + (((c - z).toNat : ℕ) : ℚ)
    rw [hi, hz]; ring

/-- **Realisations with `A h = α`, `B h = αQ/P`, `cosA A B C = (P²+Q²-R²)/(2PQ)` at arbitrarily small `h`.** -/
theorem racah_realisation (P Q R m n : ℤ) (hP : 0 < P) (hQ : 0 < Q) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1)) (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
      ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ 0 < h ∧ h ≤ ε ∧
        wA (a : ℚ) (n : ℚ) * h = α ∧ wB (b : ℚ) (m : ℚ) * h = α * Q / P ∧
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) =
          ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (α / (P * ε))
  obtain ⟨a, b, c, D', hA, hB, hC, hsys, i, hi⟩ :=
    racah_family_ints P Q R m n hRlo hRhi hpR hpP hpQ (|m - n| + |m + n| + 1 + T).toNat
      (by have h0 : 0 ≤ |m - n| + |m + n| + 1 + (T : ℤ) := by positivity
          rw [Int.toNat_of_nonneg h0]; have := abs_nonneg (m - n); have := abs_nonneg (m + n); omega)
  have hu : (((|m - n| + |m + n| + 1 + T).toNat : ℕ) : ℝ) ≥ T := by
    have h0 : 0 ≤ |m - n| + |m + n| + 1 + (T : ℤ) := by positivity
    have : (((|m - n| + |m + n| + 1 + T).toNat : ℕ) : ℤ) = |m - n| + |m + n| + 1 + T := Int.toNat_of_nonneg h0
    have h5 : (T : ℤ) ≤ (((|m - n| + |m + n| + 1 + T).toNat : ℕ) : ℤ) := by
      rw [this]; have := abs_nonneg (m - n); have := abs_nonneg (m + n); omega
    exact_mod_cast h5
  set u : ℕ := (|m - n| + |m + n| + 1 + T).toNat with hudef
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by
    have : 0 < R := by have := abs_nonneg (P - Q); omega
    exact_mod_cast this
  have htpos : (0 : ℝ) < 2 * (u : ℝ) + 1 := by positivity
  refine ⟨a, b, c, D', hsys, i, 2 * α / ((2 * (u : ℝ) + 1) * P), hi, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h1 : α / (P * ε) < T := hT
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  · rw [hA]; field_simp
  · rw [hB]; field_simp
  · rw [hA, hB, hC]
    unfold cosA
    field_simp

/-- info: 'FormalResearch.Special.racah_realisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_realisation

/-- The geometry of the integer triangle `(P, Q, R)`: `x = (P²+Q²-R²)/(2PQ) ∈ (-1, 1)` and, for `α > 0`, `β = αQ/P`,
`(α-βx)(β-αx) = α²(R⁴-(P²-Q²)²)/(4P³Q)`. -/
lemma racah_family_geom (P Q R : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q) (α : ℝ) :
    (0 < P ∧ 0 < Q ∧ 0 < R) ∧ -1 < ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
      ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) < 1 ∧
      (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
          (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) =
        α ^ 2 * ((R : ℝ) ^ 4 - ((P : ℝ) ^ 2 - Q ^ 2) ^ 2) / (4 * P ^ 3 * Q) := by
  have h0 := abs_nonneg (P - Q)
  have hl := abs_lt.1 hRlo
  have hP : 0 < P := by omega
  have hQ : 0 < Q := by omega
  have hR : 0 < R := by omega
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨⟨hP, hQ, hR⟩, ?_, ?_, ?_⟩
  · have h1 : ((P : ℤ) + Q) ^ 2 > R ^ 2 := by nlinarith
    have h2 : ((P : ℝ) + Q) ^ 2 > (R : ℝ) ^ 2 := by exact_mod_cast h1
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · have h1 : (P - Q) ^ 2 < R ^ 2 := sq_lt_sq' (by omega) (by omega)
    have h2 : ((P : ℝ) - Q) ^ 2 < (R : ℝ) ^ 2 := by exact_mod_cast h1
    rw [div_lt_one (by positivity)]
    nlinarith
  · field_simp
    ring

/-- **The Airy limit of the actual `6j` chain along infinitely many realisations, `τ = +1`** (`R² < |P²-Q²|`, e.g.
`(P,Q,R) = (6,2,5)`, `α/β = 3`, `x = 5/8`; `m = n = -1`). -/
theorem racah_chain_airy_family_pos (P Q R m n : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1))
    (hang : (R : ℝ) ^ 2 < |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2|) (α : ℝ) (hα : 0 < α) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ 0 < h ∧ h ≤ ε ∧
          wA (a : ℚ) (n : ℚ) * h = α ∧ wB (b : ℚ) (m : ℚ) * h = α * Q / P ∧
          cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryOutAt (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) 1 (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) (racah6jY a b c m n)
            (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨⟨hP, hQ, hR⟩, hx1, hx2, hprod⟩ := racah_family_geom P Q R hRlo hRhi α
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hβ : 0 < α * Q / P := by positivity
  have hneg : (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
      (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) < 0 := by
    rw [hprod]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have h1 : (R : ℝ) ^ 4 < ((P : ℝ) ^ 2 - Q ^ 2) ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg ((P : ℝ) ^ 2 - Q ^ 2), sq_nonneg (R : ℝ)] :
        -|(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) hang
      rw [sq_abs] at this
      nlinarith
    have : 0 < α ^ 2 := by positivity
    nlinarith
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    racah_chain_airy_geom_pos α (α * Q / P) _ hα hβ hx1 hx2 hneg m n A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation P Q R m n hP hQ hRlo hRhi hpR hpP hpQ α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- **The Airy limit of the actual `6j` chain along infinitely many realisations, `τ = -1`** (`R² > |P²-Q²|`; the
twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_airy_family_neg (P Q R m n : ℤ) (hRlo : |P - Q| < R) (hRhi : R < P + Q)
    (hpR : Odd R) (hpP : Even (P - n - 1)) (hpQ : Even (Q - m - 1))
    (hang : |(P : ℝ) ^ 2 - (Q : ℝ) ^ 2| < (R : ℝ) ^ 2) (α : ℝ) (hα : 0 < α) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∃ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' ∧
        ∃ (i : Fin (D' + 1)) (h : ℝ), (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i ∧ 0 < h ∧ h ≤ ε ∧
          wA (a : ℚ) (n : ℚ) * h = α ∧ wB (b : ℚ) (m : ℚ) * h = α * Q / P ∧
          cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) =
            ((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q) ∧
          AiryOutAt (1 / (4 * α ^ 2)) (1 / (4 * (α * Q / P) ^ 2)) (-1) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))
            (racahQs α (α * Q / P) (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q)))
            (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j)
            (Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)))) A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨⟨hP, hQ, hR⟩, hx1, hx2, hprod⟩ := racah_family_geom P Q R hRlo hRhi α
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hβ : 0 < α * Q / P := by positivity
  have hpos : 0 < (α - α * Q / P * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) *
      (α * Q / P - α * (((P : ℝ) ^ 2 + Q ^ 2 - R ^ 2) / (2 * P * Q))) := by
    rw [hprod]
    apply div_pos _ (by positivity)
    have h1 : ((P : ℝ) ^ 2 - Q ^ 2) ^ 2 < (R : ℝ) ^ 4 := by
      have h2 := abs_lt.1 hang
      have := sq_lt_sq' h2.1 h2.2
      nlinarith
    have : 0 < α ^ 2 := by positivity
    nlinarith
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    racah_chain_airy_geom_neg α (α * Q / P) _ hα hβ hx1 hx2 hpos m n A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro ε hε
  obtain ⟨a, b, c, D', hsys, i, h, hc, hh, hhε, hAh, hBh, hx⟩ :=
    racah_realisation P Q R m n hP hQ hRlo hRhi hpR hpP hpQ α (min ε (δ0 ^ 3)) hα (lt_min hε (by positivity))
  exact ⟨a, b, c, D', hsys, i, h, hc, hh, hhε.trans (min_le_left _ _), hAh, hBh, hx,
    H a b c D' hsys i h hc hh (hhε.trans (min_le_right _ _)) hAh hBh hx⟩

/-- info: 'FormalResearch.Special.racah_chain_airy_family_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_family_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_family_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_family_neg

end FormalResearch.Special

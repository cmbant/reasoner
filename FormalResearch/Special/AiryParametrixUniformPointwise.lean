module

public import FormalResearch.Special.AiryParametrixUniformODE
public import FormalResearch.Special.AiryParametrixPointwise

/-!
# Uniform parametrix defect, part 3: the pointwise estimate without the factor `(1+|X|)³`

`h = t³`, `X = ζ/t²`.  The window-form pointwise estimate `apx_pointwise` (`AiryParametrixPointwise`) expands
the exact shift functions at fixed `X`, whose Taylor error `(1+|X|)³ Δ⁶` is not small for `X ~ h^{-2/3}`.
Here the exact shift functions are expanded at *fixed `ζ`* (`AiryParametrixUniformODE`): the remainders are
`O(h²)` uniformly in `X`.  The parity skeleton (`sk_even_odd`, `sk_odd_even`) is applied to the closed forms
`E, O` and `A, B`, and the transport identity makes the `h¹` coefficient of `𝔅` vanish *exactly*
(`T = G₀ζ'' Ch(F) + 2G₁ A(ζ') + 2G₀ B(ζ') = 0`, `F = ζζ'²`, using `Ch(F) = 4F Ch''(F) + 2 Ch'(F)`).

* `apu_PA`: `|G₊C(X,Δ₊) + G₋C(X,Δ₋) - 2G₀ Ch(F)| ≤ K h²`;
* `apu_PB`: `|G₊S(X,Δ₊) + G₋S(X,Δ₋)| ≤ K t h²` (`S = t · S(s;ζ,h)`);
* `apu_pointwise`: `|G₊Ai(X+Δ₊) + G₋Ai(X+Δ₋) - 2G₀Ch(F) Ai(X)| ≤ K h² airyWt(X)`, using
  `|Ai| ≤ 25 airyWt`, `|Ai'| ≤ 132500 √(2+|X|) airyWt` and `t √(2+|X|) ≤ √(2+Z₀)`.

Proved; the constants are existential and depend only on the bounds.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **`𝔄` bound, uniform.** -/
theorem apu_PA (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      |(G0 + t ^ 3 * G1 + gp) * airyShiftC (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftC (z0 / t ^ 2) (t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2)| ≤ K * (t ^ 3) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := apu_bounds Z0 S hZ0 hS
  obtain ⟨KC, hKC0, hKC⟩ := apu_C_remainder Z0 S hZ0 hS
  refine ⟨(B * (2 * M * Ee + 2 * (Z0 * M) * (B / 2 + Ee) ^ 2) + B * M * (B + 2 * Ee) + 2 * Γ * M +
      B * M * (B + 2 * Ee) + 2 * B * M + 2 * Γ * M) + 2 * (2 * B + Γ) * KC, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm
  set h : ℝ := t ^ 3 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ ht0.le ht1
  have hskA := sk_even_odd (e := apuE z0) (e1 := apuE1 z0) (e2 := fun x => z0 * apuE z0 x)
    (o := apuO z0) (o1 := apuO1 z0) (S := S) (E0 := M) (M1 := M) (M2 := Z0 * M) (N0 := M) (N1 := M)
    (apu_hasDerivAt_E z0) (apu_hasDerivAt_E1 z0) (apu_hasDerivAt_O z0) (apuE_neg z0) (apuO_neg z0)
    (fun x hx => (hM z0 x hz0 hx).1) (fun x hx => (hM z0 x hz0 hx).2.1)
    (fun x hx => by
      rw [abs_mul]; exact mul_le_mul hz0 (hM z0 x hz0 hx).1 (abs_nonneg _) hZ0)
    (fun x hx => (hM z0 x hz0 hx).2.2.1) (fun x hx => (hM z0 x hz0 hx).2.2.2.1)
    hh0 hh1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
  have hGp : |G0 + h * G1 + gp| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgp.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inl rfl)
    simpa using this
  have hGm : |G0 - h * G1 + gm| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgm.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  have hρp := hKC z0 t (z1 + h * z2 / 2 + ep) hz0 hsp ht0 ht1
  have hρm := hKC z0 t (-z1 + h * z2 / 2 + em) hz0 hsm ht0 ht1
  set ρp : ℝ := apuCs z0 t (z1 + h * z2 / 2 + ep) -
    (apuE z0 (z1 + h * z2 / 2 + ep) + h * apuO z0 (z1 + h * z2 / 2 + ep)) with hρpdef
  set ρm : ℝ := apuCs z0 t (-z1 + h * z2 / 2 + em) -
    (apuE z0 (-z1 + h * z2 / 2 + em) + h * apuO z0 (-z1 + h * z2 / 2 + em)) with hρmdef
  have key : (G0 + h * G1 + gp) * airyShiftC (z0 / t ^ 2) (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftC (z0 / t ^ 2) (t * (-z1 + h * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) =
      ((G0 + h * G1 + gp) * (apuE z0 (z1 + h * z2 / 2 + ep) + h * apuO z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuE z0 (-z1 + h * z2 / 2 + em) +
          h * apuO z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apuE z0 z1) +
      (G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm := by
    have hc0 : apuE z0 z1 = langerCosh (z0 * z1 ^ 2) := rfl
    simp only [hρpdef, hρmdef, apuCs]
    rw [hc0]
    ring
  show |_ - 2 * G0 * langerCosh (z0 * z1 ^ 2)| ≤ _
  rw [key]
  have e2 : |(G0 + h * G1 + gp) * ρp| ≤ (2 * B + Γ) * (KC * h ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hGp hρp (abs_nonneg _) (by positivity)
  have e3 : |(G0 - h * G1 + gm) * ρm| ≤ (2 * B + Γ) * (KC * h ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hGm hρm (abs_nonneg _) (by positivity)
  have hfin := abs_add_three
    ((G0 + h * G1 + gp) * (apuE z0 (z1 + h * z2 / 2 + ep) + h * apuO z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuE z0 (-z1 + h * z2 / 2 + em) +
          h * apuO z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apuE z0 z1)
    ((G0 + h * G1 + gp) * ρp) ((G0 - h * G1 + gm) * ρm)
  have hp : ((G0 + h * G1 + gp) * (apuE z0 (z1 + h * z2 / 2 + ep) + h * apuO z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuE z0 (-z1 + h * z2 / 2 + em) +
          h * apuO z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apuE z0 z1) +
      (G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm =
      (((G0 + h * G1 + gp) * (apuE z0 (z1 + h * z2 / 2 + ep) + h * apuO z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuE z0 (-z1 + h * z2 / 2 + em) +
          h * apuO z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apuE z0 z1) +
      (G0 + h * G1 + gp) * ρp) + (G0 - h * G1 + gm) * ρm := rfl
  refine (abs_add_le _ _).trans ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  nlinarith [hskA, e2, e3]

/-- **`𝔅` bound, uniform**, using the transport identity `hTR`: the `h¹` coefficient vanishes exactly,
so `|G₊S(X,Δ₊) + G₋S(X,Δ₋)| ≤ K t h²` (`S(X,Δ) = t S(s;ζ,h)`). -/
theorem apu_PB (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |(G0 + t ^ 3 * G1 + gp) * airyShiftS (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftS (z0 / t ^ 2) (t * (-z1 + t ^ 3 * z2 / 2 + em))| ≤
        K * t * (t ^ 3) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := apu_bounds Z0 S hZ0 hS
  obtain ⟨KS, hKS0, hKS⟩ := apu_S_remainder Z0 S hZ0 hS
  refine ⟨(2 * B * (2 * M * Ee + 2 * M * (B / 2 + Ee) ^ 2) + 2 * Γ * M + 2 * B * M * (B / 2 + Ee) +
      2 * B * M + 2 * Γ * M) + 2 * (2 * B + Γ) * KS, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  set h : ℝ := t ^ 3 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ ht0.le ht1
  have ht : t ≠ 0 := ht0.ne'
  have hskB := sk_odd_even (a := apuA z0) (a1 := apuE z0) (a2 := apuE1 z0) (b := apuB z0)
    (b1 := apuB1 z0) (S := S) (A0 := M) (A1 := M) (A2 := M) (Bb := M) (Bb1 := M)
    (apu_hasDerivAt_A z0) (apu_hasDerivAt_E z0) (apu_hasDerivAt_B z0) (apuA_neg z0) (apuB_neg z0)
    (fun x hx => (hM z0 x hz0 hx).2.2.2.2.1) (fun x hx => (hM z0 x hz0 hx).1)
    (fun x hx => (hM z0 x hz0 hx).2.1) (fun x hx => (hM z0 x hz0 hx).2.2.2.2.2.1)
    (fun x hx => (hM z0 x hz0 hx).2.2.2.2.2.2)
    hh0 hh1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
  -- the transport identity kills the `h¹` coefficient
  have hTR' : 2 * G1 * z1 * (2 * apuc 1 (z0 * z1 ^ 2)) +
      G0 * z2 * (2 * apuc 1 (z0 * z1 ^ 2) + 2 * (z0 * z1 ^ 2) * (2 * apuc 2 (z0 * z1 ^ 2))) +
      G0 * z1 ^ 4 * (2 * apuc 2 (z0 * z1 ^ 2)) = 0 := hTR
  have hT : G0 * z2 * apuE z0 z1 + 2 * G1 * apuA z0 z1 + 2 * G0 * apuB z0 z1 = 0 := by
    have := apuc_ode0 (z0 * z1 ^ 2)
    unfold apuE apuA apuB
    linear_combination hTR' + G0 * z2 * this
  rw [hT, mul_zero, sub_zero] at hskB
  have hGp : |G0 + h * G1 + gp| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgp.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inl rfl)
    simpa using this
  have hGm : |G0 - h * G1 + gm| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgm.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  have hρp := hKS z0 t (z1 + h * z2 / 2 + ep) hz0 hsp ht0 ht1
  have hρm := hKS z0 t (-z1 + h * z2 / 2 + em) hz0 hsm ht0 ht1
  set ρp : ℝ := apuSs z0 t (z1 + h * z2 / 2 + ep) -
    (apuA z0 (z1 + h * z2 / 2 + ep) + h * apuB z0 (z1 + h * z2 / 2 + ep)) with hρpdef
  set ρm : ℝ := apuSs z0 t (-z1 + h * z2 / 2 + em) -
    (apuA z0 (-z1 + h * z2 / 2 + em) + h * apuB z0 (-z1 + h * z2 / 2 + em)) with hρmdef
  have hSs : ∀ s : ℝ, airyShiftS (z0 / t ^ 2) (t * s) = t * apuSs z0 t s := by
    intro s; unfold apuSs; field_simp
  have key : (G0 + h * G1 + gp) * airyShiftS (z0 / t ^ 2) (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftS (z0 / t ^ 2) (t * (-z1 + h * z2 / 2 + em)) =
      t * (((G0 + h * G1 + gp) * (apuA z0 (z1 + h * z2 / 2 + ep) + h * apuB z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuA z0 (-z1 + h * z2 / 2 + em) +
          h * apuB z0 (-z1 + h * z2 / 2 + em))) +
      (G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm) := by
    rw [hSs, hSs]
    simp only [hρpdef, hρmdef]
    ring
  show |(G0 + h * G1 + gp) * airyShiftS (z0 / t ^ 2) (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftS (z0 / t ^ 2) (t * (-z1 + h * z2 / 2 + em))| ≤ _
  rw [key, abs_mul, abs_of_pos ht0]
  have e2 : |(G0 + h * G1 + gp) * ρp| ≤ (2 * B + Γ) * (KS * h ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hGp hρp (abs_nonneg _) (by positivity)
  have e3 : |(G0 - h * G1 + gm) * ρm| ≤ (2 * B + Γ) * (KS * h ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hGm hρm (abs_nonneg _) (by positivity)
  have hsum := abs_add_three
    ((G0 + h * G1 + gp) * (apuA z0 (z1 + h * z2 / 2 + ep) + h * apuB z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuA z0 (-z1 + h * z2 / 2 + em) +
          h * apuB z0 (-z1 + h * z2 / 2 + em)))
    ((G0 + h * G1 + gp) * ρp) ((G0 - h * G1 + gm) * ρm)
  have hall : |((G0 + h * G1 + gp) * (apuA z0 (z1 + h * z2 / 2 + ep) + h * apuB z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apuA z0 (-z1 + h * z2 / 2 + em) +
          h * apuB z0 (-z1 + h * z2 / 2 + em))) +
      (G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm| ≤
      (2 * B * (2 * M * Ee + 2 * M * (B / 2 + Ee) ^ 2) + 2 * Γ * M + 2 * B * M * (B / 2 + Ee) +
      2 * B * M + 2 * Γ * M) * h ^ 2 + (2 * B + Γ) * (KS * h ^ 2) + (2 * B + Γ) * (KS * h ^ 2) := by
    linarith [hsum, hskB, e2, e3]
  calc t * |_| ≤ t * (((2 * B * (2 * M * Ee + 2 * M * (B / 2 + Ee) ^ 2) + 2 * Γ * M +
      2 * B * M * (B / 2 + Ee) + 2 * B * M + 2 * Γ * M) * h ^ 2 + (2 * B + Γ) * (KS * h ^ 2) +
      (2 * B + Γ) * (KS * h ^ 2))) := mul_le_mul_of_nonneg_left hall ht0.le
    _ = _ := by rw [hh]; ring

/-- `t √(2 + |z₀/t²|) ≤ √(2 + Z₀)` for `0 < t ≤ 1`, `|z₀| ≤ Z₀`. -/
lemma apu_t_sqrt {t z0 Z0 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hz0 : |z0| ≤ Z0) :
    t * √(2 + |z0 / t ^ 2|) ≤ √(2 + Z0) := by
  have hZ : 0 ≤ Z0 := (abs_nonneg _).trans hz0
  have e : t ^ 2 * (2 + |z0 / t ^ 2|) = 2 * t ^ 2 + |z0| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]; field_simp
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  calc t * √(2 + |z0 / t ^ 2|) = √(t ^ 2) * √(2 + |z0 / t ^ 2|) := by
        rw [Real.sqrt_sq ht0.le]
    _ = √(t ^ 2 * (2 + |z0 / t ^ 2|)) := (Real.sqrt_mul (sq_nonneg t) _).symm
    _ ≤ √(2 + Z0) := Real.sqrt_le_sqrt (by rw [e]; nlinarith)

/-- **Uniform pointwise defect estimate** (the Airy-level statement for real data at one lattice point):
`|G₊ Ai(X+Δ₊) + G₋ Ai(X+Δ₋) - 2 G₀ Ch(F) Ai(X)| ≤ K h² airyWt(X)` with *no* factor `(1+|X|)³`,
`h = t³`, `X = z0/t²`, `Δ± = t s±`, `s± = ±z1 + h z2/2 + e±`, `G± = G₀ ± h G₁ + γ±`, `F = z0 z1²`, given the
transport identity `hTR`.  Replaces `apx_pointwise`. -/
theorem apu_pointwise (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |(G0 + t ^ 3 * G1 + gp) * airyAi (z0 / t ^ 2 + t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyAi (z0 / t ^ 2 + t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) * airyAi (z0 / t ^ 2)| ≤
        K * (t ^ 3) ^ 2 * airyWt (z0 / t ^ 2) := by
  obtain ⟨KA, hKA0, hA⟩ := apu_PA Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  obtain ⟨KB, hKB0, hB'⟩ := apu_PB Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  refine ⟨25 * KA + 132500 * √(2 + Z0) * KB, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hAA := hA t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm
  have hBB := hB' t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hsplit := apx_split (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep))
    (t * (-z1 + t ^ 3 * z2 / 2 + em)) (G0 + t ^ 3 * G1 + gp) (G0 - t ^ 3 * G1 + gm)
    (2 * G0 * langerCosh (z0 * z1 ^ 2))
  rw [hsplit]
  set X : ℝ := z0 / t ^ 2 with hX
  obtain ⟨hAi, hAi'⟩ := apx_airy_global X
  have hw := airyWt_pos X
  have hts := apu_t_sqrt ht0 ht1 hz0
  rw [← hX] at hts
  have hh2 : 0 ≤ (t ^ 3) ^ 2 := by positivity
  set Ap : ℝ := (G0 + t ^ 3 * G1 + gp) * airyShiftC X (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftC X (t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) with hApdef
  set Bp : ℝ := (G0 + t ^ 3 * G1 + gp) * airyShiftS X (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftS X (t * (-z1 + t ^ 3 * z2 / 2 + em)) with hBpdef
  have e1 : |airyAi X * Ap| ≤ 25 * KA * (t ^ 3) ^ 2 * airyWt X := by
    rw [abs_mul]
    calc |airyAi X| * |Ap| ≤ (25 * airyWt X) * (KA * (t ^ 3) ^ 2) :=
          mul_le_mul hAi hAA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |airyAi' X * Bp| ≤ 132500 * √(2 + Z0) * KB * (t ^ 3) ^ 2 * airyWt X := by
    rw [abs_mul]
    have h1 : |airyAi' X| * t ≤ 132500 * √(2 + Z0) * airyWt X := by
      calc |airyAi' X| * t ≤ (132500 * √(2 + |X|) * airyWt X) * t :=
            mul_le_mul_of_nonneg_right hAi' ht0.le
        _ = 132500 * (t * √(2 + |X|)) * airyWt X := by ring
        _ ≤ 132500 * √(2 + Z0) * airyWt X := by gcongr
    calc |airyAi' X| * |Bp| ≤ |airyAi' X| * (KB * t * (t ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left hBB (abs_nonneg _)
      _ = (|airyAi' X| * t) * (KB * (t ^ 3) ^ 2) := by ring
      _ ≤ (132500 * √(2 + Z0) * airyWt X) * (KB * (t ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  calc |airyAi X * Ap + airyAi' X * Bp| ≤ |airyAi X * Ap| + |airyAi' X * Bp| := abs_add_le _ _
    _ ≤ _ := by nlinarith [e1, e2]

/-- info: 'FormalResearch.Special.apu_PA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_PA

/-- info: 'FormalResearch.Special.apu_PB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_PB

/-- info: 'FormalResearch.Special.apu_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_pointwise

end FormalResearch.Special

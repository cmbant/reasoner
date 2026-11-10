module

public import FormalResearch.PPTThreeQubit.WClassStates

/-!
# The mixed `W` class: the full-rank state `ρ̃` (`thm:ppt3-w-class`)

Source: `QI/hidden_entanglement/ppt_three_qubit/w_class_decompositions.tex` (last part of the proof
of `thm:ppt3-w-class`) and `appendix_noise.tex` (`eq:ppt3-tilde-rho`).

`rhoTilde` is the full-rank state `ρ̃` of `cor:ppt3-robust`, defined by `eq:ppt3-tilde-rho` with the
ten integer coefficients.  `isWClass_rhoTilde` is its membership in the mixed `W` class, by the
decomposition of the paper: complete the squares on the `(g, h)` and `(v, w)` blocks (`s`, `β`), and use
* `isWClass_A1`: `C([u_s + x e + y ē]) = [u_s] + x²[e] + y²[ē]` for `x + y = s`;
* `isWClass_A2`: `C(P([x' e + i(v - β w + o)])) = [v - β w] + [o] + x'²[e]` for
  `3 β x'² = β³ - 1`
(`eq:ppt3-w-atoms`, last line, with `γ = 1`), the remaining terms being nonnegative multiples of
`[h], [e], [ē], [w], [o], [ō]`, all with vanishing hyperdeterminant.
Covered: only the membership `ρ̃ ∈ 𝒲`.  Not covered here: that `ρ̃` is fully PPT and GME with the stated
noise radius (`cor:ppt3-robust`; needs the exact witness and trace-norm data).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

theorem ω_pow_reduce (k r : ℕ) : ω ^ (3 * k + r) = ω ^ r := by
  rw [pow_add, pow_mul, ω_cube, one_pow, one_mul]

theorem ωp7 : ω ^ 7 = ω ^ 1 := ω_pow_reduce 2 1

theorem ωp8 : ω ^ 8 = ω ^ 2 := ω_pow_reduce 2 2

theorem ωp9 : ω ^ 9 = ω ^ 0 := ω_pow_reduce 3 0

theorem ωp10 : ω ^ 10 = ω ^ 1 := ω_pow_reduce 3 1

theorem ωp11 : ω ^ 11 = ω ^ 2 := ω_pow_reduce 3 2

theorem ωp12 : ω ^ 12 = ω ^ 0 := ω_pow_reduce 4 0

theorem ωp14 : ω ^ 14 = ω ^ 2 := ω_pow_reduce 4 2

theorem ωp16 : ω ^ 16 = ω ^ 1 := ω_pow_reduce 5 1

/-- `[a + b + c] + [a + ω² b + ω c] + [a + ω b + ω² c] = 3([a] + [b] + [c])`. -/
theorem triple3_sum_id (a b c : Fin 8 → ℂ) :
    vecMulVec (a + b + c) (star (a + b + c)) +
        vecMulVec (a + ω ^ 2 • b + ω • c) (star (a + ω ^ 2 • b + ω • c)) +
        vecMulVec (a + ω • b + ω ^ 2 • c) (star (a + ω • b + ω ^ 2 • c)) =
      (3 : ℂ) • (vecMulVec a (star a) + vecMulVec b (star b) + vecMulVec c (star c)) := by
  have hω2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have hstar : star (ω ^ 2) = ω := by
    rw [star_pow, star_ω]; linear_combination ω * ω_cube
  ext i j
  simp only [vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul,
    star_ω, hstar, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, hω2]
  ring_nf

theorem det_A1_zero (x y : ℝ) :
    hyperdet (uVec (x + y) + (x : ℂ) • eVec + (y : ℂ) • star eVec) = 0 := by
  rw [hyperdet_even] <;> simp [uVec, eVec, star_ω]

theorem det_A1_one (x y : ℝ) :
    hyperdet (uVec (x + y) + ω ^ 2 • ((x : ℂ) • eVec) + ω • ((y : ℂ) • star eVec)) = 0 := by
  rw [hyperdet_even] <;> simp [uVec, eVec, star_ω]
  left; right
  linear_combination ((x : ℂ) + y) * ω_cube

theorem det_A1_two (x y : ℝ) :
    hyperdet (uVec (x + y) + ω • ((x : ℂ) • eVec) + ω ^ 2 • ((y : ℂ) • star eVec)) = 0 := by
  rw [hyperdet_even] <;> simp [uVec, eVec, star_ω]
  right
  linear_combination ((x : ℂ) + y * (ω ^ 3 + 1)) * ω_cube

theorem normSq_real_cast (x : ℝ) : Complex.normSq (x : ℂ) = x ^ 2 := by
  simp [Complex.normSq_apply]; ring

/-- `eq:ppt3-w-atoms`, first line: `C([u_s + x e + y ē]) = [u_s] + x²[e] + y²[ē]` for `x + y = s`
(here with `s = x + y`). -/
theorem isWClass_A1 (x y : ℝ) :
    IsWClass (vecMulVec (uVec (x + y)) (star (uVec (x + y))) +
      ((x ^ 2 : ℝ) : ℂ) • vecMulVec eVec (star eVec) +
      ((y ^ 2 : ℝ) : ℂ) • vecMulVec (star eVec) (star (star eVec))) := by
  have hsum := triple3_sum_id (uVec (x + y)) ((x : ℂ) • eVec) ((y : ℂ) • star eVec)
  have e : vecMulVec (uVec (x + y)) (star (uVec (x + y))) +
      ((x ^ 2 : ℝ) : ℂ) • vecMulVec eVec (star eVec) +
      ((y ^ 2 : ℝ) : ℂ) • vecMulVec (star eVec) (star (star eVec)) =
      ((1 / 3 : ℝ) : ℂ) • (vecMulVec (uVec (x + y) + (x : ℂ) • eVec + (y : ℂ) • star eVec)
          (star (uVec (x + y) + (x : ℂ) • eVec + (y : ℂ) • star eVec)) +
        vecMulVec (uVec (x + y) + ω ^ 2 • ((x : ℂ) • eVec) + ω • ((y : ℂ) • star eVec))
          (star (uVec (x + y) + ω ^ 2 • ((x : ℂ) • eVec) + ω • ((y : ℂ) • star eVec))) +
        vecMulVec (uVec (x + y) + ω • ((x : ℂ) • eVec) + ω ^ 2 • ((y : ℂ) • star eVec))
          (star (uVec (x + y) + ω • ((x : ℂ) • eVec) + ω ^ 2 • ((y : ℂ) • star eVec)))) := by
    rw [hsum, vecMulVec_smul_star, vecMulVec_smul_star, normSq_real_cast, normSq_real_cast,
      smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e]
  rw [smul_add, smul_add]
  exact ((isWClass_rankOne_smul (det_A1_zero x y) (by norm_num)).add
    (isWClass_rankOne_smul (det_A1_one x y) (by norm_num))).add
    (isWClass_rankOne_smul (det_A1_two x y) (by norm_num))

/-- `Det(ε x e + σ(v - β w + ε o)) = 0` for `ε ∈ {1, ω, ω²}`, `σ² = -1` and `3 β x² = β³ - 1`
(`Det(x e + i(v - β w + γ o)) = 4(γ³ - β³ + 3 β γ x²)` at `γ = 1`, and its cyclic images). -/
theorem det_A2 (ε : ℂ) (hε : ε = 1 ∨ ε = ω ∨ ε = ω ^ 2) (sg : ℂ) (hsg : sg ^ 2 = -1)
    (x β : ℝ) (hx : 3 * β * x ^ 2 = β ^ 3 - 1) :
    hyperdet ((x : ℂ) • (ε • eVec) + sg • (vVec - (β : ℂ) • wVec + ε • oVec)) = 0 := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have hsg4 : sg ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsg]; norm_num
  have hx' : (3 * β * x ^ 2 : ℂ) = β ^ 3 - 1 := by exact_mod_cast hx
  rcases hε with rfl | rfl | rfl <;>
  · simp [hyperdet, eVec, vVec, wVec, oVec]
    ring_nf
    simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, ωp7, ωp8, ωp9, ωp10, ωp11, ωp12, ωp14,
      ωp16, pow_zero, pow_one, h2, hsg4, hsg]
    ring_nf
    linear_combination 4 * hx'

theorem normSq_phase {ε : ℂ} (hε : ε = 1 ∨ ε = ω ∨ ε = ω ^ 2) : Complex.normSq ε = 1 := by
  rcases hε with rfl | rfl | rfl
  · simp
  · exact normSq_ω
  · exact normSq_ω_sq

/-- `eq:ppt3-w-atoms`, last line, with `γ = 1`: `C(P([x' e + i(v - β w + o)])) =
[v - β w] + [o] + x'² [e]` for `3 β x'² = β³ - 1` (here `q = x'² ≥ 0`). -/
theorem isWClass_A2 {β q : ℝ} (hq : 0 ≤ q) (hq' : 3 * β * q = β ^ 3 - 1) :
    IsWClass (vecMulVec (vVec - (β : ℂ) • wVec) (star (vVec - (β : ℂ) • wVec)) +
      vecMulVec oVec (star oVec) + (q : ℂ) • vecMulVec eVec (star eVec)) := by
  set a : Fin 8 → ℂ := vVec - (β : ℂ) • wVec with ha
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x ^ 2 = q := ⟨Real.sqrt q, Real.sq_sqrt hq⟩
  have hx3 : 3 * β * x ^ 2 = β ^ 3 - 1 := by rw [hx]; exact hq'
  have F : ∀ ε : ℂ, (ε = 1 ∨ ε = ω ∨ ε = ω ^ 2) →
      IsWClass ((q : ℂ) • vecMulVec eVec (star eVec) + vecMulVec (a + ε • oVec) (star (a + ε • oVec))) := by
    intro ε hε
    have h := isWClass_pair (x := (x : ℂ) • (ε • eVec)) (y := Complex.I • (a + ε • oVec))
      (det_A2 ε hε Complex.I Complex.I_sq x β hx3) (by
        rw [sub_eq_add_neg, ← neg_smul]
        exact det_A2 ε hε (-Complex.I) (by rw [neg_sq, Complex.I_sq]) x β hx3)
    rwa [vecMulVec_smul_star, vecMulVec_smul_star, vecMulVec_smul_star, normSq_phase hε,
      normSq_real_cast, hx, Complex.normSq_I, Complex.ofReal_one, one_smul, one_smul] at h
  have hsum := triple_sum_id a oVec
  have e : vecMulVec a (star a) + vecMulVec oVec (star oVec) + (q : ℂ) • vecMulVec eVec (star eVec) =
      ((1 / 3 : ℝ) : ℂ) • (((q : ℂ) • vecMulVec eVec (star eVec) +
          vecMulVec (a + oVec) (star (a + oVec))) +
        ((q : ℂ) • vecMulVec eVec (star eVec) + vecMulVec (a + ω • oVec) (star (a + ω • oVec))) +
        ((q : ℂ) • vecMulVec eVec (star eVec) +
          vecMulVec (a + ω ^ 2 • oVec) (star (a + ω ^ 2 • oVec)))) := by
    have h3 : (q : ℂ) • vecMulVec eVec (star eVec) + vecMulVec (a + oVec) (star (a + oVec)) +
        ((q : ℂ) • vecMulVec eVec (star eVec) + vecMulVec (a + ω • oVec) (star (a + ω • oVec))) +
        ((q : ℂ) • vecMulVec eVec (star eVec) +
          vecMulVec (a + ω ^ 2 • oVec) (star (a + ω ^ 2 • oVec))) =
        (3 : ℂ) • ((q : ℂ) • vecMulVec eVec (star eVec)) + (3 : ℂ) • (vecMulVec a (star a) +
          vecMulVec oVec (star oVec)) := by
      rw [← hsum]; module
    rw [h3]
    push_cast
    module
  rw [e]
  have h1 := F 1 (Or.inl rfl)
  rw [one_smul] at h1
  exact ((h1.add (F ω (Or.inr (Or.inl rfl)))).add (F (ω ^ 2) (Or.inr (Or.inr rfl)))).smul
    (r := 1 / 3) (by norm_num)

/-! ### The full-rank state `ρ̃` -/

/-- `|g⟩ = |000⟩`. -/
def gVec : Fin 8 → ℂ := ![1, 0, 0, 0, 0, 0, 0, 0]

/-- `|h⟩ = |011⟩ + |101⟩ + |110⟩`. -/
def hVec : Fin 8 → ℂ := ![0, 0, 0, 1, 0, 1, 1, 0]

/-- The full-rank state `ρ̃` of `cor:ppt3-robust` (`eq:ppt3-tilde-rho`), with `ē = star e`,
`ō = star o`:
`10⁷ ρ̃ = 955592 [g] - 930700 (|g⟩⟨h| + |h⟩⟨g|) + 906857 [h] + 519407 [e] + 208476 [ē]
  + 390647 [v] - 520181 (|v⟩⟨w| + |w⟩⟨v|) + 693325 [w] + 556418 [o] + 104 [ō]`. -/
def rhoTilde : Matrix (Fin 8) (Fin 8) ℂ :=
  ((1 / 10000000 : ℝ) : ℂ) •
    ((955592 : ℂ) • vecMulVec gVec (star gVec) -
      (930700 : ℂ) • (vecMulVec gVec (star hVec) + vecMulVec hVec (star gVec)) +
      (906857 : ℂ) • vecMulVec hVec (star hVec) + (519407 : ℂ) • vecMulVec eVec (star eVec) +
      (208476 : ℂ) • vecMulVec (star eVec) (star (star eVec)) +
      (390647 : ℂ) • vecMulVec vVec (star vVec) -
      (520181 : ℂ) • (vecMulVec vVec (star wVec) + vecMulVec wVec (star vVec)) +
      (693325 : ℂ) • vecMulVec wVec (star wVec) + (556418 : ℂ) • vecMulVec oVec (star oVec) +
      (104 : ℂ) • vecMulVec (star oVec) (star (star oVec)))

/-- `s = -c₁/c₀` for the `(g, h)` block. -/
def tS : ℝ := 232675 / 238898

/-- `β = -c_{vw}/c_v` for the `(v, w)` block. -/
def tB : ℝ := 520181 / 390647

/-- `x'² = (β³ - 1)/(3β)`. -/
def tQ : ℝ := (tB ^ 3 - 1) / (3 * tB)

theorem uVec_eq_sub (s : ℝ) : uVec s = gVec - (s : ℂ) • hVec := by
  funext i
  fin_cases i <;> simp [uVec, gVec, hVec]

theorem vecMulVec_sub_smul (a b : Fin 8 → ℂ) (s : ℝ) :
    vecMulVec (a - (s : ℂ) • b) (star (a - (s : ℂ) • b)) =
      vecMulVec a (star a) + ((s ^ 2 : ℝ) : ℂ) • vecMulVec b (star b) -
        (s : ℂ) • (vecMulVec a (star b) + vecMulVec b (star a)) := by
  ext i j
  simp only [vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, Pi.star_apply, star_sub, star_smul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  ring

theorem hyperdet_hVec : hyperdet hVec = 0 := by
  rw [hyperdet_even] <;> simp [hVec]

theorem hyperdet_star_eVec : hyperdet (star eVec) = 0 := by
  rw [hyperdet_even] <;> simp [eVec]

theorem hyperdet_star_oVec : hyperdet (star oVec) = 0 := by
  rw [hyperdet_odd] <;> simp [oVec]

/-- **`thm:ppt3-w-class`, the full-rank state `ρ̃`.**  By the decomposition of the paper:
`10⁷ ρ̃ = c₀ C([u_s + x e + y ē]) + c_v C(P([x' e + i(v - β w + o)])) + (c₂ - c₀ s²)[h]
  + r_e [e] + r_ē [ē] + (c_w - c_v β²)[w] + (c_o - c_v)[o] + c_ō [ō]`
with `(x, y) = (5s/9, 4s/9)`. -/
theorem isWClass_rhoTilde : IsWClass rhoTilde := by
  have hB0 : tB ≠ 0 := by unfold tB; norm_num
  have hQ0 : 0 ≤ tQ := by unfold tQ tB; norm_num
  have hQ3 : 3 * tB * tQ = tB ^ 3 - 1 := by
    unfold tQ; field_simp
  have hA1 := isWClass_A1 (5 * tS / 9) (4 * tS / 9)
  have hA2 := isWClass_A2 (β := tB) (q := tQ) hQ0 hQ3
  have key : rhoTilde =
      ((1 / 10000000 : ℝ) : ℂ) •
        (((955592 : ℝ) : ℂ) • (vecMulVec (uVec (5 * tS / 9 + 4 * tS / 9))
            (star (uVec (5 * tS / 9 + 4 * tS / 9))) +
          (((5 * tS / 9) ^ 2 : ℝ) : ℂ) • vecMulVec eVec (star eVec) +
          (((4 * tS / 9) ^ 2 : ℝ) : ℂ) • vecMulVec (star eVec) (star (star eVec))) +
        ((390647 : ℝ) : ℂ) • (vecMulVec (vVec - (tB : ℂ) • wVec) (star (vVec - (tB : ℂ) • wVec)) +
          vecMulVec oVec (star oVec) + (tQ : ℂ) • vecMulVec eVec (star eVec)) +
        ((906857 - 955592 * tS ^ 2 : ℝ) : ℂ) • vecMulVec hVec (star hVec) +
        ((519407 - 955592 * (5 * tS / 9) ^ 2 - 390647 * tQ : ℝ) : ℂ) • vecMulVec eVec (star eVec) +
        ((208476 - 955592 * (4 * tS / 9) ^ 2 : ℝ) : ℂ) • vecMulVec (star eVec) (star (star eVec)) +
        ((693325 - 390647 * tB ^ 2 : ℝ) : ℂ) • vecMulVec wVec (star wVec) +
        ((556418 - 390647 : ℝ) : ℂ) • vecMulVec oVec (star oVec) +
        ((104 : ℝ) : ℂ) • vecMulVec (star oVec) (star (star oVec))) := by
    have e1 : (5 * tS / 9 + 4 * tS / 9 : ℝ) = tS := by ring
    rw [e1, uVec_eq_sub, vecMulVec_sub_smul, vecMulVec_sub_smul, rhoTilde]
    congr 1
    simp only [tS, tB, tQ]
    push_cast
    module
  rw [key]
  have c1 : (0 : ℝ) ≤ 906857 - 955592 * tS ^ 2 := by unfold tS; norm_num
  have c2 : (0 : ℝ) ≤ 519407 - 955592 * (5 * tS / 9) ^ 2 - 390647 * tQ := by
    unfold tS tQ tB; norm_num
  have c3 : (0 : ℝ) ≤ 208476 - 955592 * (4 * tS / 9) ^ 2 := by unfold tS; norm_num
  have c4 : (0 : ℝ) ≤ 693325 - 390647 * tB ^ 2 := by unfold tB; norm_num
  refine IsWClass.smul ?_ (by norm_num)
  exact (((((((hA1.smul (by norm_num)).add (hA2.smul (by norm_num))).add
    ((isWClass_rankOne hyperdet_hVec).smul c1)).add (isWClass_e.smul c2)).add
    ((isWClass_rankOne hyperdet_star_eVec).smul c3)).add (isWClass_w.smul c4)).add
    (isWClass_o.smul (by norm_num))).add ((isWClass_rankOne hyperdet_star_oVec).smul (by norm_num))

end

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_A1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_A1

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_A2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_A2

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_rhoTilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_rhoTilde

end FormalResearch.PPTThreeQubit

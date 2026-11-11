module

public import FormalResearch.PPTThreeQubit.FamilyGME
public import FormalResearch.PPTThreeQubit.SurfaceWitness

/-!
# The rank-five surface `ρ(α, β, γ)`: definitions, local filter, GME

Source: `QI/hidden_entanglement/ppt_three_qubit/rank_five_surface.tex`
(`eq:ppt3-weights`, `eq:ppt3-rho-surface`, `thm:ppt3-orbit`(b) and the GME part, in the file
`Surface.lean`; `cor:ppt3-extreme5` GME part is in `SurfaceExtreme.lean`).

The weights `O, E, G, V` of `eq:ppt3-weights` are `wO, wE, wG, wV`; the operator is
`rhoSurface α β γ = B_s X B_s†` with `s = α/γ` and `X` the `5 × 5` coefficient matrix `surfX`
(`rhoSurface_eq` is `eq:ppt3-rho-surface`).  `ρ_{τ,a} = rhoSurface 1 τ a`.

Covered here: the filter identity `ρ(α, β, aα) = a F_λ ρ(α, β, α) F_λ†` for `λ² = 1/a`
(`rhoSurface_filter`, `thm:ppt3-orbit`(b)), and the GME part of `thm:ppt3-orbit`: for
`1/√3 < τ < 1` and every `a > 0`, `ρ_{τ,a}` is GME (`ppt3_orbit_gme`; the operators are
unnormalised, which does not affect biseparability).  The proof splits at `τ = 3/4` (`Q = 2`):
`H_5` on `[3/4, 1)` and `H_0` on `(1/√3, 3/4]`, with the traces of the paper in the coordinate
`Q = τ + √(1+τ²)`, then the local filter for general `a`.
Not covered: positivity, rank profile and PPT of the family, and the rest of (a), (c).
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-! ### The surface weights and the operator `ρ(α, β, γ)` -/

/-- `h = √(α² + β²)`. -/
def surfH (α β : ℝ) : ℝ := Real.sqrt (α ^ 2 + β ^ 2)

/-- `O = κ / β`, `κ = α² - β²` (`eq:ppt3-weights`). -/
def wO (α β : ℝ) : ℝ := (α ^ 2 - β ^ 2) / β

/-- `E = κ (h + β)² / (α² γ)`. -/
def wE (α β γ : ℝ) : ℝ := (α ^ 2 - β ^ 2) * (surfH α β + β) ^ 2 / (α ^ 2 * γ)

/-- `G = α (E - α s) / β`, `s = α / γ`. -/
def wG (α β γ : ℝ) : ℝ := α * (wE α β γ - α * (α / γ)) / β

/-- `V = (α² E² - 2 α s κ E + (α s)² κ) / (β κ)`, `s = α / γ`. -/
def wV (α β γ : ℝ) : ℝ :=
  (α ^ 2 * wE α β γ ^ 2 - 2 * α * (α / γ) * (α ^ 2 - β ^ 2) * wE α β γ +
    (α * (α / γ)) ^ 2 * (α ^ 2 - β ^ 2)) / (β * (α ^ 2 - β ^ 2))

/-- The `5 × 5` coefficient matrix in the basis `(u_s, v, w, e, o)`: diagonal `(γ, V, β, E, O)`
and `vw` entry `G`. -/
def surfXw (γ V G β E O : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun i j => ((![![γ, 0, 0, 0, 0], ![0, V, G, 0, 0], ![0, G, β, 0, 0],
    ![0, 0, 0, E, 0], ![0, 0, 0, 0, O]] i j : ℝ) : ℂ)

/-- The coefficient matrix of `ρ(α, β, γ)`. -/
def surfX (α β γ : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  surfXw γ (wV α β γ) (wG α β γ) β (wE α β γ) (wO α β)

/-- `ρ(α, β, γ) = B_s X B_s†`, `s = α/γ` (`eq:ppt3-rho-surface`); unnormalised. -/
def rhoSurface (α β γ : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Bs (α / γ) * surfX α β γ * (Bs (α / γ))ᴴ

theorem Bs_surfXw_Bs (s γ V G β E O : ℝ) :
    Bs s * surfXw γ V G β E O * (Bs s)ᴴ =
      (γ : ℂ) • vecMulVec (uVec s) (star (uVec s)) + (β : ℂ) • vecMulVec wVec (star wVec) +
      (V : ℂ) • vecMulVec vVec (star vVec) +
      (G : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
      (E : ℂ) • vecMulVec eVec (star eVec) + (O : ℂ) • vecMulVec oVec (star oVec) := by
  ext i j
  simp only [surfXw, Bs, bCols, mul_apply, Fin.sum_univ_five, conjTranspose_apply, of_apply,
    Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  simp
  ring

/-- **`eq:ppt3-rho-surface`**:
`ρ(α,β,γ) = γ u_s u_s† + β ww† + V vv† + G (wv† + vw†) + E ee† + O oo†`, `s = α/γ`. -/
theorem rhoSurface_eq (α β γ : ℝ) :
    rhoSurface α β γ =
      (γ : ℂ) • vecMulVec (uVec (α / γ)) (star (uVec (α / γ))) +
      (β : ℂ) • vecMulVec wVec (star wVec) +
      (wV α β γ : ℂ) • vecMulVec vVec (star vVec) +
      (wG α β γ : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
      (wE α β γ : ℂ) • vecMulVec eVec (star eVec) + (wO α β : ℂ) • vecMulVec oVec (star oVec) :=
  Bs_surfXw_Bs _ _ _ _ _ _ _

/-! ### The local filter `F_λ = diag(1, λ)^{⊗3}` (`thm:ppt3-orbit`(b)) -/

/-- The diagonal of `F_λ = diag(1, λ)^{⊗3}`: `|abc⟩ ↦ λ^{a+b+c}|abc⟩`. -/
def filterDiag (lam : ℝ) : Fin 8 → ℂ := fun i => (lam : ℂ) ^ (i.val / 4 + i.val / 2 % 2 + i.val % 2)

theorem isLocalDiag_filterDiag (lam : ℝ) : IsLocalDiag (filterDiag lam) :=
  ⟨fun a => (lam : ℂ) ^ a.val, fun a => (lam : ℂ) ^ a.val, fun a => (lam : ℂ) ^ a.val,
    fun i => by simp [filterDiag, pow_add, mul_assoc]⟩

theorem filterDiag_ne_zero {lam : ℝ} (h : lam ≠ 0) (i : Fin 8) : filterDiag lam i ≠ 0 := by
  simp [filterDiag, h]

/-- `F_λ B_1 = B_{λ²} diag(1, λ³, λ, λ², λ)`: excitation counting. -/
theorem filter_mul_Bs (lam : ℝ) :
    diagonal (filterDiag lam) * Bs 1 =
      Bs (lam ^ 2) * diagonal (fun a => ((![1, lam ^ 3, lam, lam ^ 2, lam] a : ℝ) : ℂ)) := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Bs, bCols, filterDiag, uVec, vVec, wVec, eVec, oVec] <;> ring

/-- Positive real scalars are diagonal filters: `diag(k) M diag(k)† = |k|² M`. -/
theorem conj_const (k : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    diagonal (fun _ => k) * M * (diagonal (fun _ => k))ᴴ = (k * star k) • M := by
  have : (diagonal (fun _ : Fin 8 => k)) = k • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
    rw [← smul_one_eq_diagonal]
  rw [this]
  simp [smul_smul, mul_comm]

theorem isBiseparable_smul_pos {c : ℝ} (hc : 0 < c) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    IsBiseparable ((c : ℂ) • M) ↔ IsBiseparable M := by
  have hd : IsLocalDiag (fun _ : Fin 8 => ((Real.sqrt c : ℝ) : ℂ)) :=
    ⟨fun _ => ((Real.sqrt c : ℝ) : ℂ), fun _ => 1, fun _ => 1, fun i => by simp⟩
  have hne : ∀ i : Fin 8, ((Real.sqrt c : ℝ) : ℂ) ≠ 0 := fun _ => by
    have := Real.sqrt_pos.mpr hc
    exact_mod_cast this.ne'
  have := isBiseparable_conj_localDiag_iff hd (fun i => hne i) M
  rw [conj_const] at this
  have e : ((Real.sqrt c : ℝ) : ℂ) * star ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rwa [e] at this

/-! ### Relations between the weights at `γ = aα` and `γ = α` -/

section filterWeights

variable {α β a : ℝ}

theorem wE_filter (hα : 0 < α) (ha : 0 < a) : wE α β (a * α) = wE α β α / a := by
  unfold wE; field_simp

theorem wG_filter (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) :
    wG α β (a * α) = wG α β α / a := by
  unfold wG
  rw [wE_filter hα ha]
  have : α / (a * α) = a⁻¹ := by field_simp
  rw [this, div_self hα.ne']
  field_simp

theorem wV_filter (hα : 0 < α) (hβ : 0 < β) (hβα : β < α) (ha : 0 < a) :
    wV α β (a * α) = wV α β α / a ^ 2 := by
  have hκ : α ^ 2 - β ^ 2 ≠ 0 := by nlinarith
  unfold wV
  rw [wE_filter hα ha]
  have : α / (a * α) = a⁻¹ := by field_simp
  rw [this, div_self hα.ne']
  field_simp

end filterWeights

/-- **`thm:ppt3-orbit`(b)** (filter identity): for `0 < β < α`, `a > 0` and `λ² = 1/a`,
`ρ(α, β, aα) = a F_λ ρ(α, β, α) F_λ†`, `F_λ = diag(1, λ)^{⊗3}`. -/
theorem rhoSurface_filter {α β a lam : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβα : β < α) (ha : 0 < a)
    (hl : lam ^ 2 = a⁻¹) :
    rhoSurface α β (a * α) =
      (a : ℂ) • (diagonal (filterDiag lam) * rhoSurface α β α * (diagonal (filterDiag lam))ᴴ) := by
  have hs : α / (a * α) = lam ^ 2 := by rw [hl]; field_simp
  have hs1 : α / α = 1 := div_self hα.ne'
  have hl0 : lam ≠ 0 := by
    intro h; rw [h] at hl; simp at hl; linarith
  have ha' : a * lam ^ 2 = 1 := by rw [hl]; field_simp
  -- the coefficient matrix transforms by the diagonal scaling
  have hlc : (lam : ℂ) ≠ 0 := by exact_mod_cast hl0
  have ha2 : (a : ℂ) = ((lam : ℂ) ^ 2)⁻¹ := by
    have : a = (lam ^ 2)⁻¹ := by rw [hl]; simp
    rw [this]; push_cast; rfl
  set D : Matrix (Fin 5) (Fin 5) ℂ :=
    diagonal (fun b => ((![1, lam ^ 3, lam, lam ^ 2, lam] b : ℝ) : ℂ)) with hD
  have hX : (a : ℂ) • (D * surfX α β α * Dᴴ) = surfX α β (a * α) := by
    have hE := wE_filter (β := β) hα ha
    have hG := wG_filter hα hβ ha
    have hV := wV_filter hα hβ hβα ha
    unfold surfX
    rw [hE, hG, hV]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hD, surfXw, diagonal_mul, mul_diagonal, Matrix.smul_apply]
    all_goals
      (rw [ha2]; field_simp)
  have hF : diagonal (filterDiag lam) * Bs 1 = Bs (lam ^ 2) * D := filter_mul_Bs lam
  unfold rhoSurface
  rw [hs, hs1]
  calc Bs (lam ^ 2) * surfX α β (a * α) * (Bs (lam ^ 2))ᴴ
      = Bs (lam ^ 2) * ((a : ℂ) • (D * surfX α β α * Dᴴ)) * (Bs (lam ^ 2))ᴴ := by rw [hX]
    _ = (a : ℂ) • ((Bs (lam ^ 2) * D) * surfX α β α * (Bs (lam ^ 2) * D)ᴴ) := by
        simp [Matrix.mul_assoc, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = (a : ℂ) • ((diagonal (filterDiag lam) * Bs 1) * surfX α β α *
          (diagonal (filterDiag lam) * Bs 1)ᴴ) := by rw [hF]
    _ = _ := by simp [Matrix.mul_assoc, conjTranspose_mul]

/-! ### Traces of the witnesses on `X(1, t, 1)` in the coordinate `Q = t + √(1+t²)` -/

theorem trace_Hs_surfXw (s γ V G β E O : ℝ) :
    (Hs s * surfXw γ V G β E O).trace =
      ((hDiag s 0 * γ + hDiag s 1 * V + hDiag s 2 * β + hDiag s 3 * E + hDiag s 4 * O : ℝ) : ℂ) := by
  simp [Hs, surfXw, trace, diag, mul_apply, Fin.sum_univ_five, diagonal_apply]

theorem trace_H0_surfXw (γ V G β E O : ℝ) :
    (H0 * surfXw γ V G β E O).trace =
      ((h0Diag 0 * γ + h0Diag 1 * V + h0Diag 2 * β + h0Diag 3 * E + h0Diag 4 * O -
        2 * nuH * G : ℝ) : ℂ) := by
  simp [H0, surfXw, trace, diag, mul_apply, Fin.sum_univ_five, h0Diag]
  ring

theorem surfH_sq (t : ℝ) : surfH 1 t ^ 2 = 1 + t ^ 2 := by
  unfold surfH; rw [Real.sq_sqrt (by positivity)]; ring

theorem surfH_pos (t : ℝ) : 0 < surfH 1 t := by
  unfold surfH; exact Real.sqrt_pos.mpr (by positivity)

theorem wO_one (t : ℝ) : wO 1 t = (1 - t ^ 2) / t := by simp [wO]

theorem wE_one (t : ℝ) : wE 1 t 1 = (1 - t ^ 2) * (surfH 1 t + t) ^ 2 := by simp [wE]

theorem wG_one (t : ℝ) : wG 1 t 1 = ((1 - t ^ 2) * (surfH 1 t + t) ^ 2 - 1) / t := by
  simp [wG, wE_one]

theorem wV_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    wV 1 t 1 = ((1 - t ^ 2) * (surfH 1 t + t) ^ 4 - 2 * (1 - t ^ 2) * (surfH 1 t + t) ^ 2 + 1) / t := by
  have hκ : (1 - t ^ 2) ≠ 0 := by nlinarith
  unfold wV
  rw [wE_one]
  simp
  field_simp

/-- `S_6(Q) = Q⁶ - Q⁵ - 9Q⁴ + 2Q³ + 11Q² + 27Q - 3` of the paper. -/
def S6 (Q : ℝ) : ℝ := Q ^ 6 - Q ^ 5 - 9 * Q ^ 4 + 2 * Q ^ 3 + 11 * Q ^ 2 + 27 * Q - 3

/-- `P(Q) = Q⁴ + (8+2√3)Q³ - (2+4√3)Q² - (20+14√3)Q + 1 + 4√3` of the paper. -/
def Pq (Q : ℝ) : ℝ :=
  Q ^ 4 + (8 + 2 * Real.sqrt 3) * Q ^ 3 - (2 + 4 * Real.sqrt 3) * Q ^ 2 -
    (20 + 14 * Real.sqrt 3) * Q + 1 + 4 * Real.sqrt 3

/-- Rational-function algebra in `Q = h + t`, using `t = (Q²-1)/(2Q)`, `h = (Q²+1)/(2Q)`. -/
theorem Q_coords {t h : ℝ} (ht : 0 < t) (hh : h ^ 2 = 1 + t ^ 2) (h0 : 0 < h) :
    ∃ Q : ℝ, Q = h + t ∧ 1 < Q ∧ t = (Q ^ 2 - 1) / (2 * Q) ∧ h = (Q ^ 2 + 1) / (2 * Q) := by
  have h1 : 1 < h := by nlinarith
  refine ⟨h + t, rfl, by linarith, ?_, ?_⟩ <;> field_simp <;> nlinarith

theorem core5 {t h : ℝ} (ht : 0 < t) (hh : h ^ 2 = 1 + t ^ 2) (h0 : 0 < h) :
    -12 * 1 + ((1 - t ^ 2) * (h + t) ^ 4 - 2 * (1 - t ^ 2) * (h + t) ^ 2 + 1) / t + 11 * t -
        6 * ((1 - t ^ 2) * (h + t) ^ 2) + 14 * ((1 - t ^ 2) / t) =
      -((h + t) ^ 2 - 2 * (h + t) - 1) * S6 (h + t) / (2 * (h + t) * ((h + t) ^ 2 - 1)) := by
  obtain ⟨Q, hQ, hQ1, ht', hh'⟩ := Q_coords ht hh h0
  rw [← hQ]
  have hQ0 : Q ≠ 0 := by positivity
  have hQ2 : Q ^ 2 - 1 ≠ 0 := by nlinarith
  subst ht'
  unfold S6
  field_simp
  ring

theorem core0 {t h : ℝ} (s : ℝ) (ht : 0 < t) (hh : h ^ 2 = 1 + t ^ 2) (h0 : 0 < h) :
    (-24 - 8 * s) * 1 + ((1 - t ^ 2) * (h + t) ^ 4 - 2 * (1 - t ^ 2) * (h + t) ^ 2 + 1) / t + 9 * t +
        (12 + 4 * s) * ((1 - t ^ 2) * (h + t) ^ 2) + (12 + 12 * s) * ((1 - t ^ 2) / t) -
        2 * (7 + 4 * s) * (((1 - t ^ 2) * (h + t) ^ 2 - 1) / t) =
      -(((h + t) ^ 2 - 3) * ((h + t) ^ 2 - 2 * (h + t) - 1) *
        ((h + t) ^ 4 + (8 + 2 * s) * (h + t) ^ 3 - (2 + 4 * s) * (h + t) ^ 2 -
          (20 + 14 * s) * (h + t) + 1 + 4 * s)) / (2 * (h + t) * ((h + t) ^ 2 - 1)) := by
  obtain ⟨Q, hQ, hQ1, ht', hh'⟩ := Q_coords ht hh h0
  rw [← hQ]
  have hQ0 : Q ≠ 0 := by positivity
  have hQ2 : Q ^ 2 - 1 ≠ 0 := by nlinarith
  subst ht'
  field_simp
  ring

/-- `tr(H_5 X_t) = -(Q²-2Q-1) S_6(Q) / (2Q(Q²-1))`, `Q = t + √(1+t²)`, for `0 < t < 1`. -/
theorem trace_H5_surf {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (Hs 1 * surfX 1 t 1).trace.re =
      -((surfH 1 t + t) ^ 2 - 2 * (surfH 1 t + t) - 1) * S6 (surfH 1 t + t) /
        (2 * (surfH 1 t + t) * ((surfH 1 t + t) ^ 2 - 1)) := by
  unfold surfX
  rw [trace_Hs_surfXw, Complex.ofReal_re, wV_one ht ht1, wE_one, wO_one]
  rw [← core5 ht (surfH_sq t) (surfH_pos t)]
  simp [hDiag]
  ring

/-- `tr(H_0 X_t) = -(Q²-3)(Q²-2Q-1) P(Q) / (2Q(Q²-1))`, `Q = t + √(1+t²)`, for `0 < t < 1`. -/
theorem trace_H0_surf {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (H0 * surfX 1 t 1).trace.re =
      -(((surfH 1 t + t) ^ 2 - 3) * ((surfH 1 t + t) ^ 2 - 2 * (surfH 1 t + t) - 1) *
        Pq (surfH 1 t + t)) / (2 * (surfH 1 t + t) * ((surfH 1 t + t) ^ 2 - 1)) := by
  unfold surfX
  rw [trace_H0_surfXw, Complex.ofReal_re, wV_one ht ht1, wG_one, wE_one, wO_one]
  rw [Pq, ← core0 (Real.sqrt 3) ht (surfH_sq t) (surfH_pos t)]
  simp [h0Diag, nuH]

/-! ### The sign of the traces and GME at `a = 1` -/

/-- `S_6(2 + x) = -1 - 81x - 33x² + 50x³ + 41x⁴ + 11x⁵ + x⁶`. -/
theorem S6_shift (x : ℝ) :
    S6 (2 + x) = -1 - 81 * x - 33 * x ^ 2 + 50 * x ^ 3 + 41 * x ^ 4 + 11 * x ^ 5 + x ^ 6 := by
  unfold S6; ring

/-- `S_6(Q) < 0` for `2 ≤ Q ≤ 5/2` (the paper uses `Q < 1 + √2 < 5/2`). -/
theorem S6_neg {Q : ℝ} (h2 : 2 ≤ Q) (h3 : Q ≤ 5 / 2) : S6 Q < 0 := by
  obtain ⟨x, rfl⟩ : ∃ x, Q = 2 + x := ⟨Q - 2, by ring⟩
  have hx : 0 ≤ x := by linarith
  have hx' : x ≤ 1 / 2 := by linarith
  rw [S6_shift]
  have e2 : x ^ 2 ≤ x / 2 := by nlinarith
  have e3 : x ^ 3 ≤ x ^ 2 / 2 := by nlinarith [sq_nonneg x]
  have e4 : x ^ 4 ≤ x / 8 := by nlinarith [pow_nonneg hx 3]
  have e5 : x ^ 5 ≤ x / 16 := by nlinarith [pow_nonneg hx 4]
  have e6 : x ^ 6 ≤ x / 32 := by nlinarith [pow_nonneg hx 5]
  nlinarith [sq_nonneg x]

/-- `P(Q) < 0` for `√3 ≤ Q ≤ 2` (`P(Q) = P(2) + (Q-2) R(Q)` with `R ≥ 0` and `P(2) = 33-24√3`). -/
theorem Pq_neg {Q : ℝ} (h0 : 0 < Q) (h1 : 3 < Q ^ 2) (h2 : Q ≤ 2) : Pq Q < 0 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  set s := Real.sqrt 3
  have hs1 : 7 / 4 > s := by nlinarith
  have hs2 : 3 / 2 < s := by nlinarith
  have hQ : 17 / 10 < Q := by nlinarith
  have hR : 0 ≤ Q ^ 3 + (10 + 2 * s) * Q ^ 2 + 18 * Q + 16 - 14 * s := by
    nlinarith [pow_pos (by linarith : (0 : ℝ) < Q) 3, sq_nonneg Q]
  have e : Pq Q = (33 - 24 * s) + (Q - 2) * (Q ^ 3 + (10 + 2 * s) * Q ^ 2 + 18 * Q + 16 - 14 * s) := by
    unfold Pq; ring
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) hR]

theorem trace_H5_surf_neg {t : ℝ} (h34 : 3 / 4 ≤ t) (ht1 : t < 1) :
    (Hs 1 * surfX 1 t 1).trace.re < 0 := by
  have ht : 0 < t := by linarith
  rw [trace_H5_surf ht ht1]
  have hh := surfH_sq t
  have h0 := surfH_pos t
  set h := surfH 1 t
  have hh54 : 5 / 4 ≤ h := by nlinarith
  have hQ2 : 2 ≤ h + t := by linarith
  have hQ1 : (h + t) ^ 2 - 2 * (h + t) - 1 < 0 := by nlinarith
  have hQ52 : h + t ≤ 5 / 2 := by nlinarith
  have hS := S6_neg hQ2 hQ52
  have hden : 0 < 2 * (h + t) * ((h + t) ^ 2 - 1) := by
    have : 0 < (h + t) ^ 2 - 1 := by nlinarith
    positivity
  apply div_neg_of_neg_of_pos _ hden
  nlinarith [mul_pos_of_neg_of_neg hQ1 hS]

theorem trace_H0_surf_neg {t : ℝ} (hlow : 1 / Real.sqrt 3 < t) (h34 : t ≤ 3 / 4) :
    (H0 * surfX 1 t 1).trace.re < 0 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < t := lt_trans (by positivity) hlow
  have ht1 : t < 1 := by linarith
  have hst : 1 < Real.sqrt 3 * t := by
    rwa [div_lt_iff₀ hs0, mul_comm] at hlow
  have h3t : 1 < 3 * t ^ 2 := by nlinarith
  rw [trace_H0_surf ht ht1]
  have hh := surfH_sq t
  have h0 := surfH_pos t
  set h := surfH 1 t
  have hh54 : h ≤ 5 / 4 := by nlinarith
  have hQ2 : h + t ≤ 2 := by linarith
  have hQ1 : (h + t) ^ 2 - 2 * (h + t) - 1 < 0 := by nlinarith
  have hQ3 : 3 < (h + t) ^ 2 := by
    -- `Q² = 1 + 2 Q t` and `Q t > 1`
    have hqt : 1 < (h + t) * t := by
      by_contra hcon
      have hcon := not_lt.mp hcon
      nlinarith [mul_pos h0 ht]
    nlinarith
  have hP := Pq_neg (by linarith) hQ3 hQ2
  have hden : 0 < 2 * (h + t) * ((h + t) ^ 2 - 1) := by
    have : 0 < (h + t) ^ 2 - 1 := by nlinarith
    positivity
  apply div_neg_of_neg_of_pos _ hden
  have h1 : 0 < (h + t) ^ 2 - 3 := by linarith
  have := mul_pos_of_neg_of_neg hQ1 hP
  nlinarith [mul_pos h1 this]

/-- **`thm:ppt3-orbit`, GME at `a = 1`**: `ρ_τ = ρ(1, τ, 1)` is GME for `1/√3 < τ < 1`. -/
theorem ppt3_orbit_gme_one {t : ℝ} (h1 : 1 / Real.sqrt 3 < t) (h2 : t < 1) :
    IsGME (rhoSurface 1 t 1) := by
  intro hb
  have ht : 0 < t := lt_trans (by positivity) h1
  have e : rhoSurface 1 t 1 = Bs 1 * surfX 1 t 1 * (Bs 1)ᴴ := by simp [rhoSurface]
  rw [e] at hb
  by_cases h34 : t ≤ 3 / 4
  · have := trace_H0_nonneg_of_biseparable _ hb
    have := trace_H0_surf_neg h1 h34
    linarith
  · have := trace_Hs_nonneg_of_biseparable one_pos _ hb
    have := trace_H5_surf_neg (by linarith [not_le.mp h34]) h2
    linarith

/-- **`thm:ppt3-orbit`, GME part.**  For `1/√3 < τ < 1` and every `a > 0`, the family member
`ρ_{τ,a} = ρ(1, τ, a)` is genuinely multipartite entangled (not biseparable).  The operators are
unnormalised, which does not affect biseparability.  The proof uses `H_5` on `3/4 ≤ τ < 1` and
`H_0` on `1/√3 < τ ≤ 3/4`, transported to `a ≠ 1` by the invertible local filter
`F_λ`, `λ² = 1/a` (`rhoSurface_filter`, `isBiseparable_conj_localDiag_iff`). -/
theorem ppt3_orbit_gme {τ : ℝ} (a : ℝ) (hτ : 1 / Real.sqrt 3 < τ) (hτ1 : τ < 1) (ha : 0 < a) :
    IsGME (rhoSurface 1 τ a) := by
  intro hb
  have hτ0 : 0 < τ := lt_trans (by positivity) hτ
  have hl : (Real.sqrt a⁻¹) ^ 2 = a⁻¹ := Real.sq_sqrt (inv_nonneg.mpr ha.le)
  have hl0 : Real.sqrt a⁻¹ ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr ha)).ne'
  have hf := rhoSurface_filter one_pos hτ0 hτ1 ha hl
  rw [mul_one] at hf
  rw [hf] at hb
  have h1 := (isBiseparable_smul_pos ha _).mp hb
  have h2 := (isBiseparable_conj_localDiag_iff (isLocalDiag_filterDiag _)
    (filterDiag_ne_zero hl0) _).mp h1
  exact ppt3_orbit_gme_one hτ hτ1 h2

end

/-- info: 'FormalResearch.PPTThreeQubit.rhoSurface_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoSurface_filter

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_orbit_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_orbit_gme

end FormalResearch.PPTThreeQubit

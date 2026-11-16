module

public import Mathlib
public import FormalResearch.Racah.P2AnalyticAllOrder6jSeries
public import FormalResearch.Racah.P2AnalyticAllOrder3j

/-!
# All-order local calculus for the one-small `6j` kernel: the operators `𝒢_r` (Weyl P2, `thm:6jallorderlocal`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jallorderlocal`, `app:6j-allorder`
(the `6j` instance of `prop:localcalculus`: `(a,b) = (n,m)`, `k = f`, `η(k) = η_k` of `eq:etak`,
`q(λ) = (2λ+1-Σ)/(8AB)`, `Σ = m²+n²`, `τ = mn`), `eq:6jrec`, `eq:3jpsi2r` and the paragraph "Link to the
physical kernels".  This is the `6j` mirror of `P2AnalyticAllOrder3j` (`allorder_operators`).

Fix the canonical sector (`m - n = p`, `m + n = q` natural, so `m ≥ |n|`) and the normalised lengths
`α, β > 0` (the paper's `A/Λ`, `B/Λ` at the bookkeeping scale `t = Λ⁻²`).  For `x ∈ (-1,1)` let
`γ(x) = √(α²+β²-2αβx)` (`gam6`), so that `(α,β,γ(x))` is a strict-triangle shape with `cosA α β γ(x) = x`
(`cosA_gam6`, `strictTri_gam6`).  `a_{f,r}(α,β,γ(x))` (`a6`) is the `t^r` Taylor coefficient of the exact germ
`G6` (`thm:6jeven`, `G_{f,2r} = Λ^{-2r} a_{f,r}`).

* `phys6 m n hα hβ d r : Fn`: the function `x ↦ a_{m+d,r}(α,β,γ(x))` on `(-1,1)` (smooth by the analyticity of
  `a6` on `StrictTri`); `phys6_rankDefect`: its formal series solve the deformed rank recurrence;
* `allorder_operators6_pos` (**`thm:6jallorderlocal`, identification step, `m > 0`**): there are left-normal
  differential operators `𝒢_r` (`𝒢_0 = I`, coefficients smooth on `(-1,1)`, independent of the rank `d`),
  `[x, 𝒢_{r+1}] = 𝖡_{r+1}` for `𝖡` of `eq:3jB2r` with `H = 𝖧₀` the Wigner operator (`Σ = m²+n²`, `τ = mn`),
  `q = qPoly6 = (2λ+1-Σ)/(8αβ)` and `e_s = eta6c` the coefficients of `√((1-z/4α²)(1-z/4β²))`, such that
  `(𝒢_r d^{m+d}_{nm})(x) = a_{m+d,r}(α,β,γ(x))` for every rank `d`, order `r` and `x ∈ (-1,1)`
  (so `Φ_f = ∑_r t^r 𝒢_r d^f_{nm}` as formal series, `G_{f,2r} = (𝒢_r d)(x)` at the physical scale);
* `allorder_operators6_zero` (the scalar sector `m = n = 0`, two exact starts, `𝒢_r d_0 = 0` for `r ≥ 1`).

Claim class: proved.  Canonical sector (`m ≥ |n|`) only; the other sectors of `G6` are `±` the canonical germ
of a reduced pair, so the operators for them are the same up to the chamber sign (not formalised).
*Not formalised:* rationality of the coefficients and the pole statement at `x = ±1` (the multipliers
`ψ_r = κ_r - 𝒥(𝖡_r)d_m/d_m` are smooth on `(-1,1)`; `lem:6jseedrational`), the homogeneous rewriting
`G_{f,2r}(A,B,C) = (𝒢_r(A,B) d)(x)` in the physical scale `(A,B,C)`, the explicit `𝒢_2`, `𝒢_4`
(`eq:6jG2operator`, `eq:6jG4operator`), and the seed formula for `κ_r^{[2r]}` (`eq:6jpsi4`).
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus.Fun

open Set Module FormalResearch.Wigner FormalResearch.Racah FormalResearch.Racah.SixJ
open scoped ContDiff

/-! ### The point `γ(x)` -/

section Geometry

variable {α β : ℝ}

/-- `γ(x) = √(α²+β²-2αβx)`: the third side of the triangle with sides `α, β` and `cosA = x`. -/
noncomputable def gam6 (α β x : ℝ) : ℝ := Real.sqrt (α ^ 2 + β ^ 2 - 2 * α * β * x)

lemma gam6_rad_pos (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) :
    0 < α ^ 2 + β ^ 2 - 2 * α * β * x := by
  have h := mul_pos (mul_pos hα hβ) (sub_pos.2 hx.2)
  nlinarith [sq_nonneg (α - β)]

lemma gam6_sq (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) :
    gam6 α β x ^ 2 = α ^ 2 + β ^ 2 - 2 * α * β * x :=
  Real.sq_sqrt (gam6_rad_pos hα hβ hx).le

lemma gam6_pos (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) : 0 < gam6 α β x :=
  Real.sqrt_pos.mpr (gam6_rad_pos hα hβ hx)

/-- `cosA α β γ(x) = x`. -/
lemma cosA_gam6 (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) : cosA α β (gam6 α β x) = x := by
  unfold cosA
  rw [gam6_sq hα hβ hx]
  field_simp
  ring

/-- `(α, β, γ(x))` is a strict-triangle shape for `x ∈ (-1,1)`. -/
lemma strictTri_gam6 (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) :
    (α, β, gam6 α β x) ∈ StrictTri := by
  have hγ := gam6_pos hα hβ hx
  have hsq := gam6_sq hα hβ hx
  have hab := mul_pos hα hβ
  refine ⟨hα, hβ, hγ, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    nlinarith [hx.1]
  · by_contra h
    push Not at h
    nlinarith [hx.2, mul_pos hab (sub_pos.2 hx.2)]
  · by_contra h
    push Not at h
    nlinarith [hx.2, mul_pos hab (sub_pos.2 hx.2)]

lemma analyticAt_gam6 (hα : 0 < α) (hβ : 0 < β) {x : ℝ} (hx : x ∈ Sx) :
    AnalyticAt ℝ (gam6 α β) x :=
  analyticAt_sqrt_comp_3j (g := fun x : ℝ => α ^ 2 + β ^ 2 - 2 * α * β * x)
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (gam6_rad_pos hα hβ hx)

end Geometry

/-! ### The physical coefficient functions as elements of `Fn` -/

section Phys

variable (m n : ℚ) {α β : ℝ}

/-- `x ↦ a_{m+d,r}(α, β, γ(x))` on `(-1,1)` (zero elsewhere): the Taylor coefficient `G_{f,2r}` of the exact
`6j` germ at the shape `(α,β,γ(x))`, `f = m + d`. -/
noncomputable def phys6 (hα : 0 < α) (hβ : 0 < β) (d r : ℕ) : Fn :=
  ⟨fun y => if y ∈ Sx then a6 (m + d) m n r (α, β, gam6 α β y) else 0,
    fun y hy => by simp only [hy, ↓reduceIte],
    by
      have hmap : Set.MapsTo (fun y : ℝ => (α, β, gam6 α β y)) Sx StrictTri :=
        fun y hy => strictTri_gam6 hα hβ hy
      have han : AnalyticOnNhd ℝ (fun y : ℝ => (α, β, gam6 α β y)) Sx := fun y hy =>
        AnalyticAt.prod analyticAt_const
          (AnalyticAt.prod analyticAt_const (analyticAt_gam6 hα hβ hy))
      have := (analyticOnNhd_a6 (m + d) m n r).comp han hmap
      exact (this.contDiffOn isOpen_Sx.uniqueDiffOn).congr fun y hy => by simp only [hy, ↓reduceIte, Function.comp]⟩

lemma phys6_apply (hα : 0 < α) (hβ : 0 < β) (d r : ℕ) {y : ℝ} (hy : y ∈ Sx) :
    (phys6 m n hα hβ d r).1 y = a6 (m + d) m n r (α, β, gam6 α β y) := by
  show (if y ∈ Sx then _ else _) = _
  simp only [hy, ↓reduceIte]

variable {m n}

lemma max_abs_canon {p q : ℕ} (hp : m - n = p) (hq : m + n = q) : max |n| |m| = m := by
  have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hm : 0 ≤ m := by linarith
  have hn : |n| ≤ m := abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_of_nonneg hm]
  exact max_eq_right hn

lemma kz_canon {p q : ℕ} (hp : m - n = p) (hq : m + n = q) : kz n m = (m : ℝ) := by
  unfold kz; rw [max_abs_canon hp hq]

lemma Rn_canon {p q : ℕ} (hp : m - n = p) (hq : m + n = q) :
    Rn n m = fun j : ℕ => rootR m n ((m : ℝ) + j) := by
  funext j
  unfold Rn Rk rootR
  rw [max_abs_canon hp hq]
  push_cast
  rw [mul_comm]

lemma dv_canon_apply {p q : ℕ} (hp : m - n = p) (hq : m + n = q) (d : ℕ) {y : ℝ} (hy : y ∈ Sx) :
    (dv n m d).1 y = wignerSmallDx (m + (d : ℚ)) n m y := by
  unfold dv
  rw [wigF_apply _ n m hy, max_abs_canon hp hq]

end Phys

/-! ### The rank recurrence for the physical coefficient functions -/

section Rank6

variable {m n : ℚ} {p q : ℕ} {α β : ℝ}

lemma abs_le_canon (hp : m - n = p) (hq : m + n = q) : |n| ≤ m := by
  have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The evaluation of the rank defect of the functions `phys6` at a point `y ∈ (-1,1)` is the rank defect of the
formal Taylor series of the germ at the shape `(α,β,γ(y))`. -/
lemma evAt_rankDefect_phys6 (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) {y : ℝ}
    (hy : y ∈ Sx) (n' r : ℕ) :
    evAt y (LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (m : ℝ)
      (fun j : ℕ => rootR m n ((m : ℝ) + j)) (phys6 m n hα hβ) n' r) =
    LocalCalculus.rankDefect (M := ℝ) (LinearMap.lsmul ℝ ℝ y) (qPoly6 m n α β) (eta6c α β) ((n : ℝ) * m) (m : ℝ)
      (fun j : ℕ => rootR m n ((m : ℝ) + j))
      (fun d s => PowerSeries.coeff s (PsiSer6 m n α β (gam6 α β y) d)) n' r := by
  have hmap := LocalCalculus.rankDefect_map (evAt y) xOp (LinearMap.lsmul ℝ ℝ y) (fun v => rfl)
    (qPoly6 m n α β) (eta6c α β) (TauM n m) (m : ℝ) (fun j : ℕ => rootR m n ((m : ℝ) + j))
    (phys6 m n hα hβ) n' r
  have hΦ : (fun d s => evAt y (phys6 m n hα hβ d s)) =
      fun d s => PowerSeries.coeff s (PsiSer6 m n α β (gam6 α β y) d) := by
    funext d s
    show (phys6 m n hα hβ d s).1 y = _
    rw [phys6_apply m n hα hβ d s hy, a6_eq_coeff_Psi6 (abs_le_canon hp hq) d s]
  rw [hmap, hΦ]
  rfl

theorem phys6_rankDefect_succ (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) (n' : ℕ) :
    LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (kz n m) (Rn n m)
      (phys6 m n hα hβ) (n' + 1) = 0 := by
  rw [kz_canon hp hq, Rn_canon hp hq]
  funext r
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · have key : evAt y (LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (m : ℝ)
        (fun j : ℕ => rootR m n ((m : ℝ) + j)) (phys6 m n hα hβ) (n' + 1) r) = 0 := by
      rw [evAt_rankDefect_phys6 hp hq hα hβ hy]
      have := congrFun (G6c_rankDefect_succ hp hq (strictTri_gam6 hα hβ hy) n') r
      rw [cosA_gam6 hα hβ hy] at this
      exact this
    exact key
  · rw [Fn.zero_off _ hy]; rfl

theorem phys6_rankDefect_zero (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) (hm : m ≠ 0) :
    LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (kz n m) (Rn n m)
      (phys6 m n hα hβ) 0 = 0 := by
  rw [kz_canon hp hq, Rn_canon hp hq]
  funext r
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · have key : evAt y (LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (m : ℝ)
        (fun j : ℕ => rootR m n ((m : ℝ) + j)) (phys6 m n hα hβ) 0 r) = 0 := by
      rw [evAt_rankDefect_phys6 hp hq hα hβ hy]
      have := congrFun (G6c_rankDefect_zero hp hq (strictTri_gam6 hα hβ hy) hm) r
      rw [cosA_gam6 hα hβ hy] at this
      exact this
    exact key
  · rw [Fn.zero_off _ hy]; rfl

/-- At `t = 0` the physical coefficient is the Wigner function: `a_{m+d,0}(α,β,γ(y)) = d^{m+d}_{nm}(y)`. -/
lemma phys6_zero_eq_dv (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) (d : ℕ) {y : ℝ}
    (hy : y ∈ Sx) : (phys6 m n hα hβ d 0).1 y = (dv n m d).1 y := by
  have hst := strictTri_gam6 hα hβ hy
  have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  rw [phys6_apply m n hα hβ d 0 hy, a6_zero, dv_canon_apply hp hq d hy]
  have hx : cosA α β (gam6 α β y) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [cosA_gam6 hα hβ hy]; exact ⟨hy.1.le, hy.2.le⟩
  have h := G6_zero_eq_wignerD (m + (d : ℚ)) m n ⟨p + q + d, by push_cast; linarith⟩
    ⟨d, by ring⟩ ⟨q + d, by push_cast; linarith⟩ ⟨p + d, by push_cast; linarith⟩ α β (gam6 α β y)
    hα.ne' hβ.ne' hx
  exact (h.trans (by rw [cosA_gam6 hα hβ hy]))

end Rank6

/-! ### The identification theorem (`m > 0`) -/

section Main6

variable {m n : ℚ} {p q : ℕ} {α β : ℝ}

lemma abs_sub_canon (hp : m - n = p) : |n - m| = (p : ℚ) := by
  rw [abs_sub_comm, abs_of_nonneg (by rw [hp]; exact Nat.cast_nonneg p), hp]

lemma abs_add_canon (hq : m + n = q) : |n + m| = (q : ℚ) := by
  rw [add_comm, abs_of_nonneg (by rw [hq]; exact Nat.cast_nonneg q), hq]

/-- The multipliers `κ_r = a_{m,r}(α,β,γ(x))/d^m_{nm}(x)` (smooth on `(-1,1)` since `d^m_{nm} ≠ 0` there). -/
noncomputable def kap6 (hα' : |n - m| = (p : ℚ)) (hβ' : |n + m| = (q : ℚ)) (hα : 0 < α) (hβ : 0 < β)
    (r : ℕ) : End ℝ Fn :=
  mulOp (fun y => (phys6 m n hα hβ 0 r).1 y / (dv n m 0).1 y)
    (contDiffOn_div_dv0 hα' hβ' (phys6 m n hα hβ 0 r).2.2)

lemma kap6_zero (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) :
    kap6 (abs_sub_canon hp) (abs_add_canon hq) hα hβ 0 = 1 := by
  refine LinearMap.ext fun f => Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · show (phys6 m n hα hβ 0 0).1 y / (dv n m 0).1 y * f.1 y = f.1 y
    rw [phys6_zero_eq_dv hp hq hα hβ 0 hy, div_self (dv_zero_ne_zero (abs_sub_canon hp) (abs_add_canon hq) hy),
      one_mul]
  · show (phys6 m n hα hβ 0 0).1 y / (dv n m 0).1 y * f.1 y = f.1 y
    rw [Fn.zero_off f hy, mul_zero]

lemma phys6_zero_eq_kap (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) :
    phys6 m n hα hβ 0 = fun r => kap6 (abs_sub_canon hp) (abs_add_canon hq) hα hβ r (dv n m 0) := by
  funext r
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · show _ = (phys6 m n hα hβ 0 r).1 y / (dv n m 0).1 y * (dv n m 0).1 y
    rw [div_mul_cancel₀ _ (dv_zero_ne_zero (abs_sub_canon hp) (abs_add_canon hq) hy)]
  · show _ = (phys6 m n hα hβ 0 r).1 y / (dv n m 0).1 y * (dv n m 0).1 y
    rw [Fn.zero_off _ hy, Fn.zero_off _ hy, mul_zero]

/-- **`thm:6jallorderlocal`, the identification step (canonical sector, `m > 0`).**

Let `m - n = p`, `m + n = q` be natural numbers with `m > 0` and `α, β > 0` (the normalised large lengths).
There are differential operators `𝒢_0 = I, 𝒢_1, 𝒢_2, …` on functions on `(-1,1)`, independent of the rank, such that

* each `𝒢_r = ∑_j b_j(x) ∂_x^j` is a finite-order left-normal operator with coefficients smooth on `(-1,1)`
  (`LN DOp Csm`), obtained by the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` with `[x, 𝒢_{r+1}] = 𝖡_{r+1}`
  (`eq:3jB2r`, `Bop`) for `H = 𝖧₀ = Hop (n²+m²) (nm)` (the Wigner operator of `d_{nm}`), `q = qPoly6`
  (`q(λ) = (2λ+1-m²-n²)/(8αβ)`), `e_s = eta6c` (the coefficients of `√((1-z/4α²)(1-z/4β²))`, `eq:6jetaallorders`),
  `τ = nm`;
* for every rank `d`, order `r` and `x ∈ (-1,1)`: `(𝒢_r d^{m+d}_{nm})(x) = a_{m+d,r}(α, β, γ(x))`,
  where `γ(x) = √(α²+β²-2αβx)` (so `cosA α β γ(x) = x`) and `a_{f,r}` (`a6`) is the `t^r` Taylor coefficient
  of the exact germ `G6` at that shape, `t = Λ⁻²` (`G_{f,2r} = Λ^{-2r} a_{f,r}`): that is,
  `Φ_f = ∑_r t^r 𝒢_r d^f_{nm}` as formal series (`thm:6jallorderlocal`; the operators depend on the rank only
  through `d^f_{nm}`).

The multipliers `ψ_r` are the ones fixed by the exact seed at `f = m` (`eq:3jpsi2r`).  *Not formalised:*
rationality of the coefficients with poles at `x = ±1` only (`lem:6jseedrational`) and the explicit `𝒢_2`, `𝒢_4`. -/
theorem allorder_operators6_pos (hp : m - n = p) (hq : m + n = q) (hα : 0 < α) (hβ : 0 < β) (hm : 0 < m) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM n m) (TauM n m)) (qPoly6 m n α β) (eta6c α β) (TauM n m) G r) ∧
      ∀ d r, ∀ y ∈ Sx, (G r (dv n m d)).1 y = a6 (m + d) m n r (α, β, gam6 α β y) := by
  have hα' := abs_sub_canon hp
  have hβ' := abs_add_canon hq
  have hk : 0 < kz n m := by rw [kz_canon hp hq]; exact_mod_cast hm
  have hfwd : ∀ n' : ℕ, (kz n m + n') * Rn n m (n' + 1) ≠ 0 := by
    intro n'
    have hR : 0 < Rn n m (n' + 1) := by
      unfold Rn
      refine Rk_pos n m _ ?_
      have : (0 : ℚ) < ((n' + 1 : ℕ) : ℚ) := by positivity
      linarith
    have : 0 < kz n m + n' := by positivity
    exact (mul_pos this hR).ne'
  obtain ⟨G, hG0, hGm, hGB, hGκ, -, huniq⟩ := LocalCalculus.prop_localcalculus (D := DOp) (C := Csm)
    (x := xOp) DOp_xOp (fun c hc => comm_x_Csm hc) (fun c hc => comm_Csm hc) xOp_mem_Csm
    (Hop_mem_LN_sm (SigM n m) (TauM n m)) (qPoly6 m n α β) (eta6c α β) (e6_zero α β) (TauM n m) (kz n m)
    (Rn n m) (Rn_zero n m) hfwd (dv n m) (Hop_dv n m) (dv_rec n m)
    (mulOp_mem_Csm _ (contDiffOn_div_dv0 hα' hβ' (dv n m 0).contDiffOn_deriv)) (DOp_dv_zero hα' hβ')
    (kap6 hα' hβ' hα hβ) (fun r => mulOp_mem_Csm _ _) (kap6_zero hp hq hα hβ)
  have hall : ∀ n' : ℕ, LocalCalculus.rankDefect (M := Fn) xOp (qPoly6 m n α β) (eta6c α β) (TauM n m) (kz n m)
      (Rn n m) (phys6 m n hα hβ) n' = 0 := by
    intro n'
    cases n' with
    | zero => exact phys6_rankDefect_zero hp hq hα hβ hm.ne'
    | succ k => exact phys6_rankDefect_succ hp hq hα hβ k
  have hu := huniq (phys6 m n hα hβ) hall (phys6_zero_eq_kap hp hq hα hβ)
  refine ⟨G, hG0, hGm, hGB, fun d r y hy => ?_⟩
  have := congrFun (congrFun hu d) r
  rw [← phys6_apply m n hα hβ d r hy, this]
  rfl

/-! ### The scalar sector `m = n = 0` -/

/-- The exact coefficient functions of the scalar sector: `Φ_0 = 1`, i.e. `a_{0,r} = 0` for `r ≥ 1`. -/
lemma phys6_zero_zero_pos (hα : 0 < α) (hβ : 0 < β) (r : ℕ) (hr : 1 ≤ r) {y : ℝ} (hy : y ∈ Sx) :
    (phys6 0 0 hα hβ 0 r).1 y = 0 := by
  rw [phys6_apply 0 0 hα hβ 0 r hy,
    a6_eq_coeff_Psi6 (m := 0) (n := 0) (by simp) 0 r α β (gam6 α β y)]
  simp only [Psi6_zero_zero_zero, PowerSeries.coeff_one]
  simp [show r ≠ 0 by omega]

/-- **`thm:6jallorderlocal`, scalar sector `m = n = 0`** (two exact starts, `prop:localcalculus` (c)):
the same identification as `allorder_operators6_pos` for `f = d ∈ ℕ`, with `𝒢_r d_0 = 0` for `r ≥ 1`
(`Φ_0 = 1`) and `q(0) = 1/(8αβ)` in the second start `η(1)Φ_1 = x - t q(0)` (`eq:6jexceptionalseed`). -/
theorem allorder_operators6_zero (hα : 0 < α) (hβ : 0 < β) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (qPoly6 0 0 α β) (eta6c α β) (TauM 0 0) G r) ∧
      (∀ r, G (r + 1) (dv 0 0 0) = 0) ∧
      ∀ d r, ∀ y ∈ Sx, (G r (dv 0 0 d)).1 y = a6 (0 + (d : ℚ)) 0 0 r (α, β, gam6 α β y) := by
  have hp0 : (0 : ℚ) - 0 = ((0 : ℕ) : ℚ) := by simp
  have hq0 : (0 : ℚ) + 0 = ((0 : ℕ) : ℚ) := by simp
  have hα' := abs_sub_canon (m := (0 : ℚ)) (n := 0) (p := 0) hp0
  have hβ' := abs_add_canon (m := (0 : ℚ)) (n := 0) (q := 0) hq0
  let κ : ℕ → End ℝ Fn := fun r => if r = 0 then 1 else 0
  have hκ : ∀ r, κ r ∈ Csm := by
    intro r; simp only [κ]; split_ifs
    · exact Csm.one_mem
    · exact Csm.zero_mem
  have hκ0 : κ 0 = 1 := by simp [κ]
  obtain ⟨G, hG0, hGm, hGB, hGκ, -⟩ := LocalCalculus.local_calculus_start (D := DOp) (C := Csm)
    (x := xOp) DOp_xOp (fun c hc => comm_x_Csm hc) (fun c hc => comm_Csm hc) xOp_mem_Csm
    (Hop_mem_LN_sm (SigM 0 0) (TauM 0 0)) (qPoly6 0 0 α β) (eta6c α β) (TauM 0 0) (d0 := dv 0 0 0)
    (mulOp_mem_Csm _ (contDiffOn_div_dv0 hα' hβ' (dv 0 0 0).contDiffOn_deriv)) (DOp_dv_zero hα' hβ')
    κ hκ hκ0
  have hGz : ∀ r, G (r + 1) (dv 0 0 0) = 0 := by
    intro r; rw [hGκ (r + 1)]; simp [κ]
  have hk : kz 0 0 = 0 := by simp [kz]
  have hτ : TauM 0 0 = 0 := by simp [TauM]
  have hd0 : Hop (SigM 0 0) (TauM 0 0) (dv 0 0 0) = 0 := by
    rw [Hop_dv]; simp [hk, LocalCalculus.lam]
  have hd1 : Hop (SigM 0 0) (TauM 0 0) (xOp (dv 0 0 0)) = (2 : ℝ) • xOp (dv 0 0 0) := by
    rw [← dv_one_scalar, Hop_dv]; simp [hk, LocalCalculus.lam]; norm_num
  have hGB' : ∀ r, comm xOp (G (r + 1)) =
      Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (qPoly6 0 0 α β) (eta6c α β) 0 G r := by
    intro r; rw [hGB r]; unfold LocalCalculus.Bop; rw [hτ]
  have hstart := LocalCalculus.scalar_start_series xOp (Hop (SigM 0 0) (TauM 0 0)) (qPoly6 0 0 α β) (eta6c α β)
    (e6_zero α β) G hG0 (dv 0 0 0) hd0 hd1 hGz hGB'
  have hq6 : (qPoly6 0 0 α β).eval 0 = 1 / (8 * α * β) := by
    simp [qPoly6]
  -- the physical second start
  have hphys : LocalCalculus.smulS (LocalCalculus.eta (eta6c α β) 1) (fun r => phys6 0 0 hα hβ 1 r) =
      LocalCalculus.smulS (LocalCalculus.eta (eta6c α β) 1) (LocalCalculus.serG G (xOp (dv 0 0 0))) := by
    rw [hstart]
    funext r
    refine Fn.ext' fun y => ?_
    by_cases hy : y ∈ Sx
    · have hst := strictTri_gam6 hα hβ hy
      have h1 := congrArg (PowerSeries.coeff r) (Psi6_zero_zero_one hst)
      rw [cosA_gam6 hα hβ hy] at h1
      have hL : evAt y (LocalCalculus.smulS (LocalCalculus.eta (eta6c α β) 1)
          (fun r => phys6 0 0 hα hβ 1 r) r) = if r = 0 then y else if r = 1 then -(1 / (8 * α * β)) else 0 := by
        rw [evAt_smulS]
        have : (fun s => evAt y (phys6 0 0 hα hβ 1 s)) =
            fun s => PowerSeries.coeff s (PsiSer6 0 0 α β (gam6 α β y) 1) := by
          funext s
          show (phys6 0 0 hα hβ 1 s).1 y = _
          rw [phys6_apply 0 0 hα hβ 1 s hy,
            a6_eq_coeff_Psi6 (m := 0) (n := 0) (by simp) 1 s α β (gam6 α β y)]
        rw [this, coeff_smulS_real, mk_coeff_self, eta_e6, h1, map_sub, PowerSeries.coeff_C]
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
        by_cases hr0 : r = 0
        · subst hr0; simp
        · by_cases hr1 : r = 1
          · subst hr1; simp
          · simp [hr0, hr1]
      change evAt y _ = _
      rw [hL]
      by_cases hr0 : r = 0
      · subst hr0
        simp only [ite_true]
        show y = y * (dv 0 0 0).1 y
        rw [dv_zero_scalar_apply hy, mul_one]
      · by_cases hr1 : r = 1
        · subst hr1
          simp only [one_ne_zero, ite_false, ite_true]
          show -(1 / (8 * α * β)) = -((qPoly6 0 0 α β).eval 0 * (dv 0 0 0).1 y)
          rw [hq6, dv_zero_scalar_apply hy, mul_one]
        · simp [hr0, hr1]
    · have h0 : ∀ (g : Fn), g.1 y = 0 := fun g => g.zero_off hy
      rw [h0, h0]
  have hstart1 : (fun r => phys6 0 0 hα hβ 1 r) = LocalCalculus.serG G (xOp (dv 0 0 0)) :=
    LocalCalculus.smulS_cancel _ (by
      rw [LocalCalculus.constantCoeff_eta (eta6c α β) (e6_zero α β)]; exact one_ne_zero) hphys
  have hfwd : ∀ n' : ℕ, (kz 0 0 + ((n' + 1 : ℕ) : ℝ)) * Rn 0 0 (n' + 2) ≠ 0 := by
    intro n'
    have hR : 0 < Rn 0 0 (n' + 2) := by
      unfold Rn
      refine Rk_pos 0 0 _ ?_
      have : (0 : ℚ) < ((n' + 2 : ℕ) : ℚ) := by positivity
      simpa using this
    have : 0 < kz 0 0 + ((n' + 1 : ℕ) : ℝ) := by rw [hk]; positivity
    exact (mul_pos this hR).ne'
  have h0 : phys6 0 0 hα hβ 0 = LocalCalculus.serG G (dv 0 0 0) := by
    funext r
    refine Fn.ext' fun y => ?_
    by_cases hy : y ∈ Sx
    · cases r with
      | zero =>
        show (phys6 0 0 hα hβ 0 0).1 y = (G 0 (dv 0 0 0)).1 y
        rw [hG0, phys6_zero_eq_dv hp0 hq0 hα hβ 0 hy]; rfl
      | succ r =>
        show (phys6 0 0 hα hβ 0 (r + 1)).1 y = (G (r + 1) (dv 0 0 0)).1 y
        rw [hGz r, phys6_zero_zero_pos hα hβ (r + 1) (by omega) hy]; rfl
    · rw [Fn.zero_off _ hy]
      show 0 = (G r (dv 0 0 0)).1 y
      rw [Fn.zero_off _ hy]
  have hu := LocalCalculus.rank_unique_of_two_starts xOp (qPoly6 0 0 α β) (eta6c α β) (e6_zero α β) (TauM 0 0)
    (kz 0 0) (Rn 0 0) hfwd (Φ := phys6 0 0 hα hβ) (Φ' := fun n => LocalCalculus.serG G (dv 0 0 n))
    (fun n' => phys6_rankDefect_succ hp0 hq0 hα hβ n')
    (fun n' => LocalCalculus.local_calculus_ranks xOp _ (qPoly6 0 0 α β) (eta6c α β) (e6_zero α β) G hG0
      (TauM 0 0) (kz 0 0) (Rn 0 0) (dv 0 0) (Hop_dv 0 0) (dv_rec 0 0) hGB (n' + 1))
    h0 (by
      show (fun r => phys6 0 0 hα hβ 1 r) = fun r => G r (dv 0 0 1)
      rw [hstart1, dv_one_scalar]; rfl)
  refine ⟨G, hG0, hGm, hGB, hGz, fun d r y hy => ?_⟩
  have := congrFun (congrFun hu d) r
  rw [← phys6_apply 0 0 hα hβ d r hy, this]
  rfl

end Main6

end FormalResearch.Racah.LocalCalculus.Fun

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators6_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators6_pos

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators6_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators6_zero

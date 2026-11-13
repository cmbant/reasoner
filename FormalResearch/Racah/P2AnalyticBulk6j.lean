module

public import FormalResearch.Racah.P2AnalyticCarrier6jPoly
public import FormalResearch.Racah.P2AnalyticTaylor
public import FormalResearch.Racah.P2AnalyticCore

/-!
# The `6j` bulk expansion (Weyl P2, `thm:6jeven`; holomorphy paragraph of `lem:6jseed`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:6jeven` (`eq:6jleading`, `eq:6jevenexp`),
its proof, the cone `T_δ` (`eq:6jstrictcone`) and the holomorphy paragraph after `lem:6jseed`.

The generic analytic lemmas `analyticAt_Ct_comp`, `analyticAt_sqrt_comp` are those of `P2AnalyticCore`.
Points of `Shape6 × ℝ` are read as `((α, β, γ), t)`.

## Results

* `analyticAt_ptilde6`: `P̃_{m+d}(τ; u, v, w)` is real analytic in all arguments (the `ptilde6`
  recursion is a composition of analytic functions).
* `Dom6c`, `Dom6c_isOpen`, `analyticAt_G6c`, `analyticOnNhd_G6c`: the closed-form germ
  `G6c m n d α β γ t` is real analytic jointly in `(α,β,γ,t)` on the open set where `α,β > 0` and
  the radicands `edgeSqT`, `piSixT` are positive.
* `StrictTri` (open strict-triangle cone, scale invariant), `mem_Dom6c_zero`: `((α,β,γ), 0)` lies in
  the domain for every strict-triangle shape.
* `Dom6`, `analyticAt_G6`, `analyticOnNhd_G6`, `mem_Dom6_zero`: the same for `G6 f m n` in all
  four chambers.
* `a6 f m n r` (`= a_{f,r}`): `t^r` Taylor coefficient of the germ; `analyticOnNhd_a6`: analytic on
  `StrictTri`.  `G6even f m n r A B C = S^{-2r} a_{f,r}((A,B,C)/S)` (`= G_{f,2r}`), `S = A+B+C`;
  `G6even_homogeneous` (degree `-2r`), `analyticOnNhd_G6even` (analytic on the whole cone),
  `G6even_zero_eq_dZero6` (`G_{f,0} = dZero6 f m n (cosA A B C)`, `eq:6jleading`, not identified
  with the Wigner `d`).
* `Phi6_even_expansion` (**`thm:6jeven`, `eq:6jevenexp`**): for a compact set `K` of strict-triangle
  shapes and every `R` there are `C, S₀` with
  `|Φ_f - ∑_{r<R} G_{f,2r}| ≤ C S^{-2R}` at every physical point with `S ≥ S₀`, shape in `K`.
  No odd power of `S⁻¹` occurs.  `Phi6_even_expansion_cone` is the form on `T_δ` with the
  remainder `C H^{-2R}`, `H = max(A,B,C)`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set Filter Topology

/-! ### Analyticity of the carrier -/

/-- The carrier `P̃_{m+d}(τ; u, v, w)` is real analytic in all arguments. -/
theorem analyticAt_ptilde6 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (m n : ℚ) (d : ℕ)
    {τ u v w : X → ℝ} {x : X} (hτ : AnalyticAt ℝ τ x) (hu : AnalyticAt ℝ u x)
    (hv : AnalyticAt ℝ v x) (hw : AnalyticAt ℝ w x) :
    AnalyticAt ℝ (fun y => ptilde6 m n (τ y) (u y) (v y) (w y) d) x := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, ih with
    | 0, _ =>
      simp only [ptilde6_zero]; exact analyticAt_const
    | 1, _ =>
      by_cases hm : m = 0
      · subst hm
        simp only [ptilde6_one_of_eq]
        exact (analyticAt_const.sub (analyticAt_const.mul hτ)).sub hw.div_const
      · simp only [ptilde6_one_of_ne m n hm]
        exact (analyticAt_const.mul (analyticAt_const.mul
          ((analyticAt_const.mul ((analyticAt_const.sub (analyticAt_const.mul hτ)).sub
            (analyticAt_const.mul hw))).sub analyticAt_const))).mul analyticAt_const
    | d + 2, ih =>
      simp only [ptilde6_succ_succ]
      have h1 := ih (d + 1) (by omega)
      have h0 := ih d (by omega)
      fun_prop

/-! ### Analyticity of the closed-form germ `G6c` -/

/-- Points of `(ℝ × ℝ × ℝ) × ℝ` are read as `((α, β, γ), t)`. -/
abbrev Shape6 : Type := ℝ × ℝ × ℝ

lemma analyticAt_sh1 (p : Shape6 × ℝ) : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.1) p :=
  (analyticAt_fst (𝕜 := ℝ) (p := p.1)).comp (analyticAt_fst (𝕜 := ℝ) (p := p))

lemma analyticAt_sh2 (p : Shape6 × ℝ) : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.1) p :=
  ((analyticAt_fst (𝕜 := ℝ) (p := p.1.2)).comp (analyticAt_snd (𝕜 := ℝ) (p := p.1))).comp
    (analyticAt_fst (𝕜 := ℝ) (p := p))

lemma analyticAt_sh3 (p : Shape6 × ℝ) : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.2) p :=
  ((analyticAt_snd (𝕜 := ℝ) (p := p.1.2)).comp (analyticAt_snd (𝕜 := ℝ) (p := p.1))).comp
    (analyticAt_fst (𝕜 := ℝ) (p := p))

/-- The open set on which `G6c m n d` is analytic by construction: `α, β > 0` and both radicands
(`edgeSqT`, `piSixT`) are positive. -/
def Dom6c (m n : ℚ) (d : ℕ) : Set (Shape6 × ℝ) :=
  {p | 0 < p.1.1 ∧ 0 < p.1.2.1 ∧ 0 < edgeSqT m n p.1.1 p.1.2.1 p.1.2.2 p.2 ∧
    0 < piSixT (m + d) p.1.1 p.1.2.1 p.2}

lemma analyticAt_edgeSqT (m n : ℚ) {p : Shape6 × ℝ} (hα : p.1.1 ≠ 0) (hβ : p.1.2.1 ≠ 0) :
    AnalyticAt ℝ (fun q : Shape6 × ℝ => edgeSqT m n q.1.1 q.1.2.1 q.1.2.2 q.2) p := by
  have h1 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.1) p := analyticAt_sh1 p
  have h2 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.1) p := analyticAt_sh2 p
  have h3 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.2) p := analyticAt_sh3 p
  have ht : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.2) p := analyticAt_snd
  unfold edgeSqT
  have hd : AnalyticAt ℝ (fun q : Shape6 × ℝ => (4 * q.1.1 * q.1.2.1) ^ ⌊2 * m⌋₊) p := by fun_prop
  refine AnalyticAt.div ?_ hd ?_
  · refine (((analyticAt_Ct_comp _ (by fun_prop) ht).mul
      (analyticAt_Ct_comp _ (by fun_prop) ht)).mul
      (analyticAt_Ct_comp _ (by fun_prop) ht)).mul (analyticAt_Ct_comp _ (by fun_prop) ht)
  · exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ)

lemma analyticAt_piSixT (f : ℚ) {p : Shape6 × ℝ} (hα : p.1.1 ≠ 0) (hβ : p.1.2.1 ≠ 0) :
    AnalyticAt ℝ (fun q : Shape6 × ℝ => piSixT f q.1.1 q.1.2.1 q.2) p := by
  have h1 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.1) p := analyticAt_sh1 p
  have h2 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.1) p := analyticAt_sh2 p
  have ht : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.2) p := analyticAt_snd
  unfold piSixT
  refine Finset.analyticAt_fun_prod _ (fun k _ => ?_)
  have e1 : AnalyticAt ℝ (fun q : Shape6 × ℝ => (1 - ((f : ℝ) - k) ^ 2 * q.2 / (4 * q.1.1 ^ 2))) p :=
    analyticAt_const.sub (AnalyticAt.div (analyticAt_const.mul ht) (by fun_prop)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hα)))
  have e2 : AnalyticAt ℝ (fun q : Shape6 × ℝ => (1 - ((f : ℝ) - k) ^ 2 * q.2 / (4 * q.1.2.1 ^ 2))) p :=
    analyticAt_const.sub (AnalyticAt.div (analyticAt_const.mul ht) (by fun_prop)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hβ)))
  exact e1.mul e2

lemma analyticAt_cosA_shape {p : Shape6 × ℝ} (hα : p.1.1 ≠ 0) (hβ : p.1.2.1 ≠ 0) :
    AnalyticAt ℝ (fun q : Shape6 × ℝ => cosA q.1.1 q.1.2.1 q.1.2.2) p := by
  have h1 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.1) p := analyticAt_sh1 p
  have h2 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.1) p := analyticAt_sh2 p
  have h3 : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.1.2.2) p := analyticAt_sh3 p
  unfold cosA
  exact AnalyticAt.div (by fun_prop) (by fun_prop) (mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ)

lemma Dom6c_isOpen (m n : ℚ) (d : ℕ) :
    IsOpen (Dom6c m n d) := by
  have hV : IsOpen {p : Shape6 × ℝ | 0 < p.1.1 ∧ 0 < p.1.2.1} :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun p : Shape6 × ℝ => p.1.1)).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous fun p : Shape6 × ℝ => p.1.2.1))
  have hf : ContinuousOn (fun q : Shape6 × ℝ => edgeSqT m n q.1.1 q.1.2.1 q.1.2.2 q.2)
      {p : Shape6 × ℝ | 0 < p.1.1 ∧ 0 < p.1.2.1} :=
    fun p hp => (analyticAt_edgeSqT m n hp.1.ne' hp.2.ne').continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun q : Shape6 × ℝ => piSixT (m + d) q.1.1 q.1.2.1 q.2)
      {p : Shape6 × ℝ | 0 < p.1.1 ∧ 0 < p.1.2.1} :=
    fun p hp => (analyticAt_piSixT _ hp.1.ne' hp.2.ne').continuousAt.continuousWithinAt
  have := (hf.isOpen_inter_preimage hV (isOpen_Ioi (a := (0 : ℝ)))).inter
    (hg.isOpen_inter_preimage hV (isOpen_Ioi (a := (0 : ℝ))))
  convert this using 1
  ext p
  simp only [Dom6c, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
  tauto

/-- **`G6c` is real analytic, jointly in shape and `t`**, at every point of `Dom6c m n d`
(`thm:6jeven` proof: the radicands are polynomial in `t` and positive, `Π_f` is a finite product of
analytic factors, the carrier is a polynomial). -/
theorem analyticAt_G6c (m n : ℚ) (d : ℕ) {p : Shape6 × ℝ} (hp : p ∈ Dom6c m n d) :
    AnalyticAt ℝ (fun q : Shape6 × ℝ => G6c m n d q.1.1 q.1.2.1 q.1.2.2 q.2) p := by
  obtain ⟨hα, hβ, hE, hP⟩ := hp
  have h1 := analyticAt_sh1 p
  have h2 := analyticAt_sh2 p
  have h3 := analyticAt_sh3 p
  have ht : AnalyticAt ℝ (fun q : Shape6 × ℝ => q.2) p := analyticAt_snd
  have hsE := analyticAt_sqrt_comp (analyticAt_edgeSqT m n hα.ne' hβ.ne') hE
  have hsP := analyticAt_sqrt_comp (analyticAt_piSixT (m + d) hα.ne' hβ.ne') hP
  have hsP' : AnalyticAt ℝ (fun q : Shape6 × ℝ =>
      (Real.sqrt (piSixT (m + d) q.1.1 q.1.2.1 q.2))⁻¹) p :=
    hsP.inv (Real.sqrt_pos.mpr hP).ne'
  have hc := analyticAt_cosA_shape hα.ne' hβ.ne'
  have hpt := analyticAt_ptilde6 m n d (x := p)
    (τ := fun q : Shape6 × ℝ => (1 - cosA q.1.1 q.1.2.1 q.1.2.2) / 2)
    (u := fun q : Shape6 × ℝ => q.2 / q.1.1 ^ 2) (v := fun q : Shape6 × ℝ => q.2 / q.1.2.1 ^ 2)
    (w := fun q : Shape6 × ℝ => q.2 / (q.1.1 * q.1.2.1))
    ((analyticAt_const.sub hc).div_const)
    (AnalyticAt.div ht (by fun_prop) (pow_ne_zero 2 hα.ne'))
    (AnalyticAt.div ht (by fun_prop) (pow_ne_zero 2 hβ.ne'))
    (AnalyticAt.div ht (by fun_prop) (mul_ne_zero hα.ne' hβ.ne'))
  exact (hsE.mul hsP').mul hpt

theorem analyticOnNhd_G6c (m n : ℚ) (d : ℕ) :
    AnalyticOnNhd ℝ (fun q : Shape6 × ℝ => G6c m n d q.1.1 q.1.2.1 q.1.2.2 q.2) (Dom6c m n d) :=
  fun _ hp => analyticAt_G6c m n d hp

/-- The open strict-triangle cone (scale invariant: it is at once the set of shapes
`(α,β,γ) = (A,B,C)/S` and the cone of triples `(A,B,C)`): all of `α,β,γ`, `α+β-γ`, `β+γ-α`,
`γ+α-β` are positive. -/
def StrictTri : Set Shape6 :=
  {z | 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 ∧ z.2.2 < z.1 + z.2.1 ∧ z.1 < z.2.1 + z.2.2 ∧
    z.2.1 < z.1 + z.2.2}

lemma StrictTri_isOpen : IsOpen StrictTri := by
  have c1 : Continuous fun z : Shape6 => z.1 := by fun_prop
  have c2 : Continuous fun z : Shape6 => z.2.1 := by fun_prop
  have c3 : Continuous fun z : Shape6 => z.2.2 := by fun_prop
  refine (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
    ((isOpen_lt continuous_const c3).inter ((isOpen_lt c3 (c1.add c2)).inter
      ((isOpen_lt c1 (c2.add c3)).inter (isOpen_lt c2 (c1.add c3))))))

/-- At `t = 0` the point of every strict-triangle shape is in the domain of `G6c`:
the radicands are `((α-β+γ)(-α+β+γ))^p ((α+β-γ)(α+β+γ))^q/(4αβ)^{p+q} > 0` and `1`. -/
theorem mem_Dom6c_zero (m n : ℚ) (d : ℕ) {z : Shape6} (hz : z ∈ StrictTri) :
    (z, (0 : ℝ)) ∈ Dom6c m n d := by
  obtain ⟨hα, hβ, hγ, h1, h2, h3⟩ := hz
  refine ⟨hα, hβ, ?_, ?_⟩
  · unfold edgeSqT
    simp only [Ct_zero_t]
    have a1 : 0 < z.1 - z.2.1 + z.2.2 := by linarith
    have a2 : 0 < -z.1 + z.2.1 + z.2.2 := by linarith
    have a3 : 0 < z.1 + z.2.1 - z.2.2 := by linarith
    have a4 : 0 < z.1 + z.2.1 + z.2.2 := by linarith
    positivity
  · simp [piSixT_zero]

/-! ### All four chambers -/

/-- The swap `(α,β,γ,t) ↦ (β,α,γ,t)` used by the two chambers `|m| ≤ ±n` of `G6`. -/
def swap6 (p : Shape6 × ℝ) : Shape6 × ℝ := ((p.1.2.1, p.1.1, p.1.2.2), p.2)

lemma analyticAt_swap6 (p : Shape6 × ℝ) : AnalyticAt ℝ swap6 p :=
  ((analyticAt_sh2 p).prod ((analyticAt_sh1 p).prod (analyticAt_sh3 p))).prod analyticAt_snd

lemma continuous_swap6 : Continuous swap6 :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_swap6 p).continuousAt

/-- The domain of `G6 f m n`: the domain of the canonical `G6c` of the chamber (pulled back by
`swap6` in the two swapped chambers). -/
def Dom6 (f m n : ℚ) : Set (Shape6 × ℝ) :=
  if |n| ≤ m then Dom6c m n ⌊f - m⌋₊
  else if |n| ≤ -m then Dom6c (-m) (-n) ⌊f + m⌋₊
  else if |m| ≤ n then swap6 ⁻¹' Dom6c n m ⌊f - n⌋₊
  else swap6 ⁻¹' Dom6c (-n) (-m) ⌊f + n⌋₊

lemma Dom6_isOpen (f m n : ℚ) : IsOpen (Dom6 f m n) := by
  unfold Dom6
  split_ifs
  · exact Dom6c_isOpen _ _ _
  · exact Dom6c_isOpen _ _ _
  · exact (Dom6c_isOpen _ _ _).preimage continuous_swap6
  · exact (Dom6c_isOpen _ _ _).preimage continuous_swap6

/-- **`G6` is real analytic jointly in `(α,β,γ,t)`** on `Dom6 f m n`, in every chamber. -/
theorem analyticAt_G6 (f m n : ℚ) {p : Shape6 × ℝ} (hp : p ∈ Dom6 f m n) :
    AnalyticAt ℝ (fun q : Shape6 × ℝ => G6 f m n q.1.1 q.1.2.1 q.1.2.2 q.2) p := by
  unfold G6
  unfold Dom6 at hp
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte] at hp ⊢
    exact analyticAt_G6c _ _ _ hp
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte] at hp ⊢
    exact analyticAt_const.mul (analyticAt_G6c _ _ _ hp)
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte] at hp ⊢
    have hp' : swap6 p ∈ Dom6c n m ⌊f - n⌋₊ := hp
    have := (analyticAt_G6c n m ⌊f - n⌋₊ hp').comp_of_eq (analyticAt_swap6 p) rfl
    exact analyticAt_const.mul this
  · simp only [c1, c2, c3, ↓reduceIte] at hp ⊢
    have hp' : swap6 p ∈ Dom6c (-n) (-m) ⌊f + n⌋₊ := hp
    have := (analyticAt_G6c (-n) (-m) ⌊f + n⌋₊ hp').comp_of_eq (analyticAt_swap6 p) rfl
    exact this.congr (Filter.Eventually.of_forall fun q => rfl)

theorem analyticOnNhd_G6 (f m n : ℚ) :
    AnalyticOnNhd ℝ (fun q : Shape6 × ℝ => G6 f m n q.1.1 q.1.2.1 q.1.2.2 q.2) (Dom6 f m n) :=
  fun _ hp => analyticAt_G6 f m n hp

lemma swap6_mem_StrictTri {z : Shape6} (hz : z ∈ StrictTri) :
    (z.2.1, z.1, z.2.2) ∈ StrictTri := by
  obtain ⟨hα, hβ, hγ, h1, h2, h3⟩ := hz
  exact ⟨hβ, hα, hγ, by linarith, by linarith, by linarith⟩

theorem mem_Dom6_zero (f m n : ℚ) {z : Shape6} (hz : z ∈ StrictTri) :
    (z, (0 : ℝ)) ∈ Dom6 f m n := by
  unfold Dom6
  split_ifs
  · exact mem_Dom6c_zero _ _ _ hz
  · exact mem_Dom6c_zero _ _ _ hz
  · exact mem_Dom6c_zero _ _ _ (swap6_mem_StrictTri hz)
  · exact mem_Dom6c_zero _ _ _ (swap6_mem_StrictTri hz)

/-! ### The Taylor coefficients `a_{f,r}` and the homogeneous functions `G_{f,2r}` -/

/-- The paper's `a_{f,r}(α,β,γ)`: the `t^r` Taylor coefficient at `t = 0` of the germ
`t ↦ G6 f m n α β γ t` (`thm:6jeven` proof). -/
noncomputable def a6 (f m n : ℚ) (r : ℕ) (z : Shape6) : ℝ :=
  taylorCoeff (fun z t => G6 f m n z.1 z.2.1 z.2.2 t) r z

/-- `a_{f,r}` is real analytic in the shape on the open strict-triangle cone. -/
theorem analyticOnNhd_a6 (f m n : ℚ) (r : ℕ) : AnalyticOnNhd ℝ (a6 f m n r) StrictTri := by
  have h := analyticOnNhd_taylorCoeff (Dom6_isOpen f m n) (analyticOnNhd_G6 f m n) r
  exact h.mono (fun z hz => mem_Dom6_zero f m n hz)

theorem continuousOn_a6 (f m n : ℚ) (r : ℕ) : ContinuousOn (a6 f m n r) StrictTri :=
  (analyticOnNhd_a6 f m n r).continuousOn

/-- `a_{f,0}` is the `t = 0` value of the germ. -/
theorem a6_zero (f m n : ℚ) (z : Shape6) : a6 f m n 0 z = G6 f m n z.1 z.2.1 z.2.2 0 := by
  simp [a6, taylorCoeff]

/-- The paper's `G_{f,2r}(A,B,C) := S^{-2r} a_{f,r}(A/S, B/S, C/S)`, `S = A+B+C`. -/
noncomputable def G6even (f m n : ℚ) (r : ℕ) (A B C : ℝ) : ℝ :=
  ((A + B + C) ^ (2 * r))⁻¹ * a6 f m n r (A / (A + B + C), B / (A + B + C), C / (A + B + C))

/-- **Homogeneity of degree `-2r`**: `G_{f,2r}(sA,sB,sC) = s^{-2r} G_{f,2r}(A,B,C)` for `s ≠ 0`. -/
theorem G6even_homogeneous (f m n : ℚ) (r : ℕ) (A B C s : ℝ) (hs : s ≠ 0) :
    G6even f m n r (s * A) (s * B) (s * C) = (s ^ (2 * r))⁻¹ * G6even f m n r A B C := by
  unfold G6even
  have e : s * A + s * B + s * C = s * (A + B + C) := by ring
  rw [e, mul_div_mul_left _ _ hs, mul_div_mul_left _ _ hs, mul_div_mul_left _ _ hs, mul_pow,
    mul_inv, mul_assoc]

/-- `G_{f,2r}` is real analytic on the whole open strict-triangle cone (not merely chamberwise:
`S = A+B+C` is positive, homogeneous and analytic). -/
theorem analyticOnNhd_G6even (f m n : ℚ) (r : ℕ) :
    AnalyticOnNhd ℝ (fun p : Shape6 => G6even f m n r p.1 p.2.1 p.2.2) StrictTri := by
  intro p hp
  have hS : 0 < p.1 + p.2.1 + p.2.2 := by
    obtain ⟨h1, h2, h3, -⟩ := hp; linarith
  have hp1 : AnalyticAt ℝ (fun q : Shape6 => q.1) p := analyticAt_fst
  have hp2 : AnalyticAt ℝ (fun q : Shape6 => q.2.1) p :=
    (analyticAt_fst (𝕜 := ℝ) (p := p.2)).comp (analyticAt_snd (𝕜 := ℝ) (p := p))
  have hp3 : AnalyticAt ℝ (fun q : Shape6 => q.2.2) p :=
    (analyticAt_snd (𝕜 := ℝ) (p := p.2)).comp (analyticAt_snd (𝕜 := ℝ) (p := p))
  have hSa : AnalyticAt ℝ (fun q : Shape6 => q.1 + q.2.1 + q.2.2) p := (hp1.add hp2).add hp3
  have hshape : AnalyticAt ℝ (fun q : Shape6 =>
      (q.1 / (q.1 + q.2.1 + q.2.2), q.2.1 / (q.1 + q.2.1 + q.2.2), q.2.2 / (q.1 + q.2.1 + q.2.2))) p :=
    (hp1.div hSa hS.ne').prod ((hp2.div hSa hS.ne').prod (hp3.div hSa hS.ne'))
  have hmem : (p.1 / (p.1 + p.2.1 + p.2.2), p.2.1 / (p.1 + p.2.1 + p.2.2),
      p.2.2 / (p.1 + p.2.1 + p.2.2)) ∈ StrictTri := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
    refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩ <;>
      rw [← add_div, div_lt_div_iff_of_pos_right hS] <;> assumption
  have ha := (analyticOnNhd_a6 f m n r _ hmem).comp_of_eq hshape rfl
  have hinv : AnalyticAt ℝ (fun q : Shape6 => ((q.1 + q.2.1 + q.2.2) ^ (2 * r))⁻¹) p :=
    (hSa.pow _).inv (pow_ne_zero _ hS.ne')
  exact hinv.mul ha

/-- **`G_{f,0}` is the `t = 0` germ value** `G6 f m n (A/S) (B/S) (C/S) 0`. -/
theorem G6even_zero (f m n : ℚ) (A B C : ℝ) :
    G6even f m n 0 A B C =
      G6 f m n (A / (A + B + C)) (B / (A + B + C)) (C / (A + B + C)) 0 := by
  simp [G6even, a6_zero]

/-- **`G_{f,0}` is `dZero6`**: the zero-scale germ value is the explicit `t = 0` carrier
`dZero6 f m n (cosA α β γ)` (`eq:6jleading`, not identified with the Wigner `d` here).  The label
hypothesis is the one implied by physical admissibility (`four_nat`). -/
theorem G6_zero_eq_dZero6 (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n)) (α β γ : ℝ)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    G6 f m n α β γ 0 = dZero6 f m n (cosA α β γ) := by
  obtain ⟨n1, n2, n3, n4⟩ := hlab
  have hsw : cosA β α γ = cosA α β γ := by
    unfold cosA; ring
  unfold G6 dZero6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels c1 n2 n3 n4
    exact G6c_zero m n p q hp hq _ α β γ hα hβ
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    congr 1
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -m) (n := -n) (by simpa using c2)
      (by simpa using n1) (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    exact G6c_zero (-m) (-n) p q hp hq _ α β γ hα hβ
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    congr 1
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    rw [G6c_zero n m p q hp hq _ β α γ hβ hα, hsw]
  · have c4 : |m| ≤ -n := by
      rcases le_total 0 n with hn | hn
      · rw [abs_of_nonneg hn] at c1 c2
        exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
      · rw [abs_of_nonpos hn] at c1 c2
        rw [abs_le]; push Not at c1 c2; constructor <;> linarith
    simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨⟨p, q, hp, hq⟩, -⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
      (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
    rw [G6c_zero (-n) (-m) p q hp hq _ β α γ hβ hα, hsw]

/-- `G_{f,0}(A,B,C) = dZero6 f m n (cosA A B C)` (`eq:6jleading`): the leading homogeneous term is
the `t = 0` carrier at the centred cosine `x = (A²+B²-C²)/(2AB)`, which is scale invariant. -/
theorem G6even_zero_eq_dZero6 (f m n : ℚ)
    (hlab : IsNat (f + m) ∧ IsNat (f - m) ∧ IsNat (f + n) ∧ IsNat (f - n)) {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hS : 0 < A + B + C) :
    G6even f m n 0 A B C = dZero6 f m n (cosA A B C) := by
  rw [G6even_zero, G6_zero_eq_dZero6 f m n hlab _ _ _ (div_pos hA hS).ne' (div_pos hB hS).ne',
    ← cosA_shape A B C _ hS.ne']

/-! ### `thm:6jeven` -/

/-- The scale `S = A + B + C` of a physical point is positive. -/
lemma physical_scale_pos {a b c f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) :
    0 < wA a n ∧ 0 < wB b m ∧ 0 < wC c ∧ 0 < wA a n + wB b m + wC c := by
  obtain ⟨hA, hB, -, -, -⟩ := admissible_facts h1 h2
  have hC : 0 < wC c := by
    have e1 := isNat_nonneg' h3.1
    have e2 := isNat_nonneg' h3.2.1
    have : (0 : ℝ) ≤ c := by
      have : (0 : ℚ) ≤ c := by linarith
      exact_mod_cast this
    unfold wC; linarith
  exact ⟨hA, hB, hC, by linarith⟩

/-- **`thm:6jeven`, `eq:6jevenexp`** (proved, Lean form).  Fix `f, m, n`, a compact set `K` of
strict-triangle shapes and `R`.  There are `C, S₀` such that for every physical admissible point
`(a,b,c)` (the four triads of the `6j` family) with `S = A+B+C ≥ S₀`, `A = wA a n`, `B = wB b m`,
`C = wC c`, and normalised shape `(A,B,C)/S ∈ K`,
`|Φ_f(A,B,C) - ∑_{r<R} G_{f,2r}(A,B,C)| ≤ C S^{-2R}`,
where `G_{f,2r}(A,B,C) = S^{-2r} a_{f,r}((A,B,C)/S) = G6even f m n r A B C` is homogeneous of degree
`-2r` (`G6even_homogeneous`), real analytic on the whole open strict-triangle cone
(`analyticOnNhd_G6even`), and the expansion is in `t = S⁻²` only (no odd power of `S⁻¹`).
The rank/label hypotheses are exactly those of the physical lattice (`IsTri` conditions of
`Phi6_eq_G6`). -/
theorem Phi6_even_expansion (f m n : ℚ) {K : Set Shape6} (hK : IsCompact K) (hKS : K ⊆ StrictTri)
    (R : ℕ) :
    ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → S₀ ≤ wA a n + wB b m + wC c →
      (wA a n / (wA a n + wB b m + wC c), wB b m / (wA a n + wB b m + wC c),
        wC c / (wA a n + wB b m + wC c)) ∈ K →
      |Phi6 a b c f m n - ∑ r ∈ Finset.range R, G6even f m n r (wA a n) (wB b m) (wC c)| ≤
        C / (wA a n + wB b m + wC c) ^ (2 * R) := by
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ Dom6 f m n := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have : t = 0 := ht
    subst this
    exact mem_Dom6_zero f m n (hKS hz)
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic (Dom6_isOpen f m n)
    (analyticOnNhd_G6 f m n) hK hKU R
  refine ⟨C, max 1 (1 / ρ), ?_⟩
  intro a b c h1 h2 h3 h4 hS0 hz
  obtain ⟨hA, hB, hC', hSpos⟩ := physical_scale_pos h1 h2 h3
  set S := wA a n + wB b m + wC c with hSdef
  have hS1 : 1 ≤ S := le_trans (le_max_left _ _) hS0
  have hS2 : 1 / ρ ≤ S := le_trans (le_max_right _ _) hS0
  have ht : |1 / S ^ 2| ≤ ρ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h3' : S ≤ S ^ 2 := by nlinarith
    have h4' : 1 / ρ ≤ S ^ 2 := le_trans hS2 h3'
    rw [div_le_iff₀ hρ] at h4'
    linarith
  have key := hC _ hz _ ht
  rw [Phi6_eq_G6 a b c f m n h1 h2 h3 h4]
  have e1 : ∀ r : ℕ, G6even f m n r (wA a n) (wB b m) (wC c) =
      taylorCoeff (fun z t => G6 f m n z.1 z.2.1 z.2.2 t) r
        (wA a n / S, wB b m / S, wC c / S) * (1 / S ^ 2) ^ r := by
    intro r
    unfold G6even a6
    rw [one_div, inv_pow, ← pow_mul, mul_comm]
  simp only [e1]
  have e2 : |1 / S ^ 2| ^ R = 1 / S ^ (2 * R) := by
    rw [abs_of_nonneg (by positivity), one_div, inv_pow, ← pow_mul, one_div]
  rw [e2] at key
  calc _ ≤ C * (1 / S ^ (2 * R)) := key
    _ = C / S ^ (2 * R) := by ring

/-! ### The cone `T_δ` and the `H^{-2R}` form -/

/-- `H = max (A,B,C)`. -/
noncomputable def Hscale (A B C : ℝ) : ℝ := max A (max B C)

/-- `min(A,B,C,A+B-C,A+C-B,B+C-A)` (numerator of `eq:6jstrictcone`). -/
noncomputable def Tmin (A B C : ℝ) : ℝ :=
  min A (min B (min C (min (A + B - C) (min (A + C - B) (B + C - A)))))

/-- The normalised shapes of the cone `T_δ` (`eq:6jstrictcone`): `α+β+γ = 1` and
`min(...) ≥ δ max(α,β,γ)`. -/
def TriDelta (δ : ℝ) : Set Shape6 :=
  {z | z.1 + z.2.1 + z.2.2 = 1 ∧ δ * Hscale z.1 z.2.1 z.2.2 ≤ Tmin z.1 z.2.1 z.2.2}

lemma Hscale_div (A B C S : ℝ) (hS : 0 < S) :
    Hscale (A / S) (B / S) (C / S) = Hscale A B C / S := by
  unfold Hscale
  rw [max_div_div_right hS.le, max_div_div_right hS.le]

lemma Tmin_div (A B C S : ℝ) (hS : 0 < S) :
    Tmin (A / S) (B / S) (C / S) = Tmin A B C / S := by
  unfold Tmin
  have e1 : A / S + B / S - C / S = (A + B - C) / S := by ring
  have e2 : A / S + C / S - B / S = (A + C - B) / S := by ring
  have e3 : B / S + C / S - A / S = (B + C - A) / S := by ring
  rw [e1, e2, e3]
  simp only [min_div_div_right hS.le]

lemma Hscale_le_sum {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Hscale A B C ≤ A + B + C := by
  unfold Hscale
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

lemma Hscale_ge_third {z : Shape6} (hz : z.1 + z.2.1 + z.2.2 = 1) :
    1 / 3 ≤ Hscale z.1 z.2.1 z.2.2 := by
  unfold Hscale
  have h1 : z.1 ≤ max z.1 (max z.2.1 z.2.2) := le_max_left _ _
  have h2 : z.2.1 ≤ max z.1 (max z.2.1 z.2.2) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : z.2.2 ≤ max z.1 (max z.2.1 z.2.2) := (le_max_right _ _).trans (le_max_right _ _)
  linarith

lemma TriDelta_subset {δ : ℝ} (hδ : 0 < δ) : TriDelta δ ⊆ StrictTri := by
  intro z ⟨hsum, hz⟩
  have hH := Hscale_ge_third hsum
  have hpos : 0 < Tmin z.1 z.2.1 z.2.2 := lt_of_lt_of_le (by positivity) hz
  unfold Tmin at hpos
  simp only [lt_min_iff] at hpos
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpos
  refine ⟨h1, h2, h3, by linarith, by linarith, by linarith⟩

lemma TriDelta_isCompact {δ : ℝ} (hδ : 0 < δ) : IsCompact (TriDelta δ) := by
  have hcl : IsClosed (TriDelta δ) := by
    have e : TriDelta δ = {z : Shape6 | z.1 + z.2.1 + z.2.2 = 1} ∩
        {z : Shape6 | δ * Hscale z.1 z.2.1 z.2.2 ≤ Tmin z.1 z.2.1 z.2.2} := rfl
    rw [e]
    refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const) (isClosed_le ?_ ?_)
    · unfold Hscale; fun_prop
    · unfold Tmin; fun_prop
  have hsub : TriDelta δ ⊆ Icc (0, 0, 0) (1, 1, 1) := by
    intro z hz
    have hS := TriDelta_subset hδ hz
    obtain ⟨h1, h2, h3, -⟩ := hS
    have hsum := hz.1
    refine ⟨⟨h1.le, h2.le, h3.le⟩, ?_, ?_, ?_⟩ <;> show _ ≤ (1 : ℝ) <;> linarith
  exact (isCompact_Icc).of_isClosed_subset hcl hsub

/-- **`thm:6jeven` with the paper's cone `T_δ` and scale `H = max(A,B,C)`** (proved, Lean form):
for every `δ > 0` and `R` there are `C, H₀` with
`|Φ_f - ∑_{r<R} G_{f,2r}| ≤ C H^{-2R}` for every physical admissible point with `H ≥ H₀` and
`min(A,B,C,A+B-C,A+C-B,B+C-A) ≥ δ H` (`eq:6jstrictcone`). -/
theorem Phi6_even_expansion_cone (f m n : ℚ) {δ : ℝ} (hδ : 0 < δ) (R : ℕ) :
    ∃ C H₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → H₀ ≤ Hscale (wA a n) (wB b m) (wC c) →
      δ * Hscale (wA a n) (wB b m) (wC c) ≤ Tmin (wA a n) (wB b m) (wC c) →
      |Phi6 a b c f m n - ∑ r ∈ Finset.range R, G6even f m n r (wA a n) (wB b m) (wC c)| ≤
        C / Hscale (wA a n) (wB b m) (wC c) ^ (2 * R) := by
  obtain ⟨C, S₀, hC⟩ := Phi6_even_expansion f m n (TriDelta_isCompact hδ) (TriDelta_subset hδ) R
  refine ⟨max C 0, max S₀ 1, ?_⟩
  intro a b c h1 h2 h3 h4 hH hT
  obtain ⟨hA, hB, hC', hSpos⟩ := physical_scale_pos h1 h2 h3
  have hHle : Hscale (wA a n) (wB b m) (wC c) ≤ wA a n + wB b m + wC c :=
    Hscale_le_sum hA.le hB.le hC'.le
  have hH1 : 1 ≤ Hscale (wA a n) (wB b m) (wC c) := le_trans (le_max_right _ _) hH
  have hHpos : 0 < Hscale (wA a n) (wB b m) (wC c) := by linarith
  have key := hC a b c h1 h2 h3 h4 (le_trans (le_trans (le_max_left _ _) hH) hHle) (by
    refine ⟨?_, ?_⟩
    · field_simp
    · rw [Hscale_div _ _ _ _ hSpos, Tmin_div _ _ _ _ hSpos, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hT hSpos.le)
  refine key.trans ?_
  calc C / (wA a n + wB b m + wC c) ^ (2 * R)
      ≤ max C 0 / (wA a n + wB b m + wC c) ^ (2 * R) :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 / Hscale (wA a n) (wB b m) (wC c) ^ (2 * R) :=
        div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
          (pow_le_pow_left₀ hHpos.le hHle _)

/-- info: 'FormalResearch.Racah.Phi6_even_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_even_expansion

/-- info: 'FormalResearch.Racah.analyticAt_G6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_G6

/-- info: 'FormalResearch.Racah.analyticOnNhd_G6even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_G6even

/-- info: 'FormalResearch.Racah.G6even_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6even_homogeneous

/-- info: 'FormalResearch.Racah.G6even_zero_eq_dZero6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6even_zero_eq_dZero6

/-- info: 'FormalResearch.Racah.Phi6_even_expansion_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_even_expansion_cone

end FormalResearch.Racah

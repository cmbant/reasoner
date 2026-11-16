module

public import Mathlib
public import FormalResearch.Racah.P2AnalyticAllOrder3jSeries
public import FormalResearch.Racah.P2AnalyticBulk6j
public import FormalResearch.Racah.P2AnalyticBridge6j

/-!
# The Taylor coefficients of the `6j` germ satisfy the deformed rank recurrence as formal series
(Weyl P2, `app:6j-allorder`; `thm:6jallorderlocal`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `app:6j-allorder` (the `6j` instance of the general
construction: `(a,b) = (n,m)`, `k = f`, `η(k) = η_k` of `eq:etak`, `q(λ) = (2λ+1-Σ)/(8AB)`, so that
`eq:generalrankrec` is `eq:6jrec`), "Link to the physical kernels" (`app:localgeneral`) and `eq:6jrankpoly`.

This is the `6j` mirror of `P2AnalyticAllOrder3jSeries`.  Fix the canonical sector `m ∓ n ∈ ℕ`
(`p = m-n`, `q = m+n`) and a strict-triangle shape `(α,β,γ)` (`StrictTri`), put `x = cosA α β γ ∈ (-1,1)`
and `t = Λ^{-2}`.  The closed-form germ `G6c m n d α β γ t` (`P2AnalyticCarrier6jShape`) factors as
`G = A · S_d · P̃_d` with the rank-independent `A = √edgeSqT`, `S_d = Π_{m+d}^{-1/2}` and
`P̃_d = ptilde6 m n τ (t/α²) (t/β²) (t/(αβ)) d`; the polynomial recurrence `eq:6jrankpoly`
(`ptilde6_succ_succ`) and `Π_{f+1} = η_{f+1}² Π_f` (`piSixT_succ`) give, for the formal Taylor series
`Ψ_d = ∑_r a_{m+d,r}(α,β,γ) t^r` (`a6`), in `ℝ⟦t⟧`:

`(2f+1)[λ_f(x - t q(λ_f)) - mn]Ψ_f = (f+1) R_f η(f) Ψ_{f-1} + f R_{f+1} η(f+1) Ψ_{f+1}`,

`λ_f = f(f+1)`, `R_f = √((f²-m²)(f²-n²))`, `q(λ) = (2λ+1-m²-n²)/(8αβ)`,
`η(k) = √((1-k²t/(4α²))(1-k²t/(4β²))) = ∑_s e_s k^{2s} t^s`.

* `Eta6`, `eta6c`, `eta_e6`: the formal square root `η(k)` and its coefficients `e_s` (`eq:6jetaallorders`);
* `piSixT_succ`, `sF6_relation`: `S_d = η_{m+d+1} S_{d+1}` as formal series;
* `Psi6_rank`, `Psi6_rank_row0`: the formal rank recurrence (rows `f = m+d+1` and `f = m`);
* `G6c_rankDefect`, `G6c_rankDefect_succ`: the same in the form `rankDefect = 0` of
  `P2LocalCalculusSeries` (module `ℝ`, `x` acting as multiplication by `cosA α β γ`);
* `Psi6_zero_zero_zero`, `Psi6_zero_zero_one`: the two exact starts of the scalar sector `m = n = 0`.

Claim class: proved.  Canonical sector only (`m ≥ |n|`); the other sectors of `G6` are `±` the canonical
germ of a reduced pair (`G6`), and are not treated.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Filter
open scoped ContDiff

/-! ### The formal square root `η(k)` -/

/-- `η_k(t) = √((1 - k²t/(4α²))(1 - k²t/(4β²)))` as a formal series. -/
noncomputable def Eta6 (α β k : ℝ) : PowerSeries ℝ := epsS (k / (2 * α)) * epsS (k / (2 * β))

/-- The coefficients `e_s(α,β)` of `√((1-z/(4α²))(1-z/(4β²))) = ∑ e_s z^s` (`eq:6jetaallorders`). -/
noncomputable def eta6c (α β : ℝ) (s : ℕ) : ℝ := PowerSeries.coeff s (Eta6 α β 1)

lemma rescale_epsS (k a : ℝ) : PowerSeries.rescale (k ^ 2) (epsS a) = epsS (k * a) := by
  ext s
  simp only [epsS, PowerSeries.coeff_rescale]
  rw [mul_pow, mul_pow]
  ring_nf

theorem E6_eq_rescale (α β k : ℝ) : Eta6 α β k = PowerSeries.rescale (k ^ 2) (Eta6 α β 1) := by
  unfold Eta6
  rw [map_mul, rescale_epsS, rescale_epsS]
  congr 2 <;> ring_nf

theorem eta_e6 (α β k : ℝ) : LocalCalculus.eta (eta6c α β) k = Eta6 α β k := by
  ext s
  rw [LocalCalculus.coeff_eta, E6_eq_rescale, PowerSeries.coeff_rescale, eta6c]
  rw [← pow_mul]
  ring_nf

theorem e6_zero (α β : ℝ) : eta6c α β 0 = 1 := by
  unfold eta6c Eta6
  rw [coeff_zero_mul', coeff_zero_epsS, coeff_zero_epsS]; norm_num

theorem E6_sq (α β k : ℝ) :
    Eta6 α β k ^ 2 = (1 - PowerSeries.C (k ^ 2 / (4 * α ^ 2)) * PowerSeries.X) *
      (1 - PowerSeries.C (k ^ 2 / (4 * β ^ 2)) * PowerSeries.X) := by
  unfold Eta6
  rw [mul_pow, epsS_sq, epsS_sq]
  congr 3 <;> field_simp <;> ring_nf

/-! ### The factorisation `G6c = A · S_d · P̃_d` and smoothness at `t = 0` -/

section Germ

variable (m n : ℚ) (α β γ : ℝ)

/-- The rank-independent edge factor `√edgeSqT` of `G6c`. -/
noncomputable def aF6 (t : ℝ) : ℝ := Real.sqrt (edgeSqT m n α β γ t)

/-- `S_d = Π_{m+d}^{-1/2}`. -/
noncomputable def sF6 (d : ℕ) (t : ℝ) : ℝ := 1 / Real.sqrt (piSixT (m + d) α β t)

/-- `P̃_{m+d}(τ; t/α², t/β², t/(αβ))`, `τ = (1 - cosA α β γ)/2`. -/
noncomputable def pF6 (d : ℕ) (t : ℝ) : ℝ :=
  ptilde6 m n ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d

theorem G6c_eq (d : ℕ) (t : ℝ) : G6c m n d α β γ t = aF6 m n α β γ t * sF6 m α β d t * pF6 m n α β γ d t := by
  unfold G6c aF6 sF6 pF6
  rw [one_div]

variable {m n α β γ}

lemma contDiff_edgeSqT : ContDiff ℝ ∞ (fun t => edgeSqT m n α β γ t) := by
  unfold edgeSqT
  exact ((((contDiff_Ct_t _ _).mul (contDiff_Ct_t _ _)).mul (contDiff_Ct_t _ _)).mul
    (contDiff_Ct_t _ _)).div_const _

lemma contDiff_piSixT (f : ℚ) : ContDiff ℝ ∞ (fun t => piSixT f α β t) := by
  unfold piSixT
  refine contDiff_prod fun k _ => ?_
  fun_prop

lemma edgeSqT_zero_pos (hs : (α, β, γ) ∈ StrictTri) : 0 < edgeSqT m n α β γ 0 := by
  simp only [StrictTri, Set.mem_ofPred_eq] at hs
  obtain ⟨hα, hβ, -, h1, h2, h3⟩ := hs
  unfold edgeSqT
  simp only [Ct_zero_t]
  have a1 : 0 < α - β + γ := by linarith
  have a2 : 0 < -α + β + γ := by linarith
  have a3 : 0 < α + β - γ := by linarith
  have a4 : 0 < α + β + γ := by linarith
  positivity

lemma smoothAt0_aF6 (hs : (α, β, γ) ∈ StrictTri) : SmoothAt0 (aF6 m n α β γ) :=
  (contDiff_edgeSqT.contDiffAt).sqrt (edgeSqT_zero_pos hs).ne'

lemma smoothAt0_piSixT (f : ℚ) : SmoothAt0 (fun t => piSixT f α β t) := (contDiff_piSixT f).contDiffAt

lemma smoothAt0_sF6 (d : ℕ) : SmoothAt0 (sF6 m α β d) := by
  have h0 : 0 < piSixT (m + d) α β 0 := by rw [piSixT_zero]; exact one_pos
  exact contDiffAt_const.div ((smoothAt0_piSixT (m + d)).sqrt h0.ne') (Real.sqrt_pos.mpr h0).ne'

lemma smoothAt0_pF6 (d : ℕ) : SmoothAt0 (pF6 m n α β γ d) := by
  have h : AnalyticAt ℝ (fun t : ℝ => ptilde6 m n ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2)
      (t / (α * β)) d) 0 :=
    analyticAt_ptilde6 m n d analyticAt_const (analyticAt_id.div_const) (analyticAt_id.div_const)
      (analyticAt_id.div_const)
  exact h.contDiffAt

lemma sF6_zero (d : ℕ) : sF6 m α β d 0 = 1 := by
  unfold sF6; rw [piSixT_zero]; simp

/-- `Π_{g+1} = η_{g+1}² Π_g` in shape variables. -/
lemma piSixT_succ (g : ℚ) (hg : 0 ≤ g) (t : ℝ) :
    piSixT (g + 1) α β t = ((1 - ((g : ℝ) + 1) ^ 2 * t / (4 * α ^ 2)) *
      (1 - ((g : ℝ) + 1) ^ 2 * t / (4 * β ^ 2))) * piSixT g α β t := by
  unfold piSixT
  rw [Nat.ceil_add_one hg, Finset.prod_range_succ']
  push_cast
  have : ∀ k ∈ Finset.range ⌈g⌉₊, (1 - ((g : ℝ) + 1 - ((k : ℝ) + 1)) ^ 2 * t / (4 * α ^ 2)) *
      (1 - ((g : ℝ) + 1 - ((k : ℝ) + 1)) ^ 2 * t / (4 * β ^ 2)) =
      (1 - ((g : ℝ) - k) ^ 2 * t / (4 * α ^ 2)) * (1 - ((g : ℝ) - k) ^ 2 * t / (4 * β ^ 2)) := by
    intro k _; ring_nf
  rw [Finset.prod_congr rfl this]
  ring

/-- The linear factor `1 - c t` as a formal series. -/
lemma taylorSer_lin (c : ℝ) : taylorSer (fun t => 1 - c * t) = 1 - PowerSeries.C c * PowerSeries.X := by
  rw [taylorSer_sub (SmoothAt0.const 1) ((SmoothAt0.const _).mul SmoothAt0.id), taylorSer_const,
    taylorSer_C_mul SmoothAt0.id, taylorSer_id]
  simp

/-- **`S_d = η_{m+d+1} S_{d+1}` as formal series** (`Π_{f+1} = η_{f+1}²Π_f`, `f = m+d`). -/
theorem sF6_relation (hm : 0 ≤ m) (d : ℕ) :
    taylorSer (sF6 m α β d) = Eta6 α β ((m : ℝ) + d + 1) * taylorSer (sF6 m α β (d + 1)) := by
  set L : ℝ := (m : ℝ) + d + 1 with hL
  have p0 : ∀ j : ℕ, 0 < piSixT (m + j) α β 0 := fun j => by rw [piSixT_zero]; exact one_pos
  have h1 := taylorSer_inv_sqrt_sq (smoothAt0_piSixT (m + (d : ℚ))) (p0 d)
  have h2 := taylorSer_inv_sqrt_sq (smoothAt0_piSixT (m + ((d + 1 : ℕ) : ℚ))) (p0 (d + 1))
  have hlin : ∀ c : ℝ, SmoothAt0 (fun t : ℝ => 1 - c * t) :=
    fun c => (SmoothAt0.const 1).sub ((SmoothAt0.const _).mul SmoothAt0.id)
  have hpi : taylorSer (fun t => piSixT (m + ((d + 1 : ℕ) : ℚ)) α β t) =
      ((1 - PowerSeries.C (L ^ 2 / (4 * α ^ 2)) * PowerSeries.X) *
        (1 - PowerSeries.C (L ^ 2 / (4 * β ^ 2)) * PowerSeries.X)) *
        taylorSer (fun t => piSixT (m + (d : ℚ)) α β t) := by
    have e : (fun t => piSixT (m + ((d + 1 : ℕ) : ℚ)) α β t) =
        fun t => ((1 - (L ^ 2 / (4 * α ^ 2)) * t) * (1 - (L ^ 2 / (4 * β ^ 2)) * t)) *
          piSixT (m + (d : ℚ)) α β t := by
      funext t
      have := piSixT_succ (α := α) (β := β) (m + (d : ℚ)) (by positivity) t
      rw [show m + ((d + 1 : ℕ) : ℚ) = m + (d : ℚ) + 1 by push_cast; ring, this]
      simp only [hL]
      push_cast
      ring_nf
    rw [e, taylorSer_mul ((hlin _).mul (hlin _)) (smoothAt0_piSixT _),
      taylorSer_mul (hlin _) (hlin _), taylorSer_lin, taylorSer_lin]
  have hsq : taylorSer (sF6 m α β d) ^ 2 =
      (Eta6 α β L * taylorSer (sF6 m α β (d + 1))) ^ 2 := by
    have hne : taylorSer (fun t => piSixT (m + (d : ℚ)) α β t) ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.coeff 0) h
      rw [constantCoeff_taylorSer] at this
      exact (p0 d).ne' (by simpa using this)
    unfold sF6 at *
    rw [mul_pow, E6_sq]
    rw [hpi] at h2
    apply mul_right_cancel₀ hne
    rw [h1]
    linear_combination (-1 : PowerSeries ℝ) * h2
  have h0 : ∀ j : ℕ, PowerSeries.coeff 0 (taylorSer (sF6 m α β j)) = 1 := fun j => by
    rw [constantCoeff_taylorSer, sF6_zero]
  refine eq_of_sq_eq_of_coeff hsq ?_ ?_
  · rw [coeff_zero_mul', h0, h0]
    unfold Eta6
    rw [coeff_zero_mul', coeff_zero_epsS, coeff_zero_epsS]; norm_num
  · rw [h0]; exact one_ne_zero

end Germ

/-! ### The formal rank recurrence of the germ -/

section Rank

variable {m n : ℚ} {p q : ℕ} {α β γ : ℝ}

/-- The diagonal shift `q_f = (2λ_f + 1 - m² - n²)/(8αβ)`, `λ_f = f(f+1)` (`eq:qf`). -/
noncomputable def Qshift6 (m n : ℚ) (α β L : ℝ) : ℝ :=
  (2 * (L * (L + 1)) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / (8 * α * β)

/-- `Ψ_d = ∑_r a_{m+d,r}(α,β,γ) t^r` (formal Taylor series of the germ at a fixed shape). -/
noncomputable def PsiSer6 (m n : ℚ) (α β γ : ℝ) (d : ℕ) : PowerSeries ℝ := taylorSer (G6c m n d α β γ)

lemma m_nonneg_of_labels (hp : m - n = p) (hq : m + n = q) : 0 ≤ m := by
  have h1 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
  have h2 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  linarith

theorem taylorSer_G6c (hs : (α, β, γ) ∈ StrictTri) (d : ℕ) :
    PsiSer6 m n α β γ d = taylorSer (aF6 m n α β γ) * taylorSer (sF6 m α β d) *
      taylorSer (pF6 m n α β γ d) := by
  have : G6c m n d α β γ = fun t => aF6 m n α β γ t * sF6 m α β d t * pF6 m n α β γ d t :=
    funext (G6c_eq m n α β γ d)
  unfold PsiSer6
  rw [this, taylorSer_mul ((smoothAt0_aF6 hs).mul (smoothAt0_sF6 d)) (smoothAt0_pF6 d),
    taylorSer_mul (smoothAt0_aF6 hs) (smoothAt0_sF6 d)]

/-- The carrier recurrence `eq:6jrankpoly` at the shape, in the form `(2L+1)[λ(x - tq) - mn]P_{d+1} =
L R_{L+1}P_{d+2} + (L+1)R_Lη_L²P_d`, `L = m+d+1`. -/
lemma pF6_rank (hp : m - n = p) (hq : m + n = q) (hα : α ≠ 0) (hβ : β ≠ 0) (d : ℕ) (t : ℝ) :
    (2 * ((m : ℝ) + d + 1) + 1) * (((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1) *
        (cosA α β γ - t * Qshift6 m n α β ((m : ℝ) + d + 1)) - m * n) * pF6 m n α β γ (d + 1) t =
      ((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1) * pF6 m n α β γ (d + 2) t +
        (((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1) *
          ((1 - ((m : ℝ) + d + 1) ^ 2 / 4 * (t / α ^ 2)) * (1 - ((m : ℝ) + d + 1) ^ 2 / 4 * (t / β ^ 2))) *
            pF6 m n α β γ d t := by
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast m_nonneg_of_labels hp hq
  have hR : 0 < rootR m n ((m : ℝ) + d + 1 + 1) := rootR_pos_canon p q hp hq (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  have hf : 0 < (m : ℝ) + d + 1 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have h := ptilde6_succ_succ m n ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d
  unfold pF6 Qshift6
  rw [h]
  have e1 : (1 : ℝ) - 2 * ((1 - cosA α β γ) / 2) = cosA α β γ := by ring
  rw [e1]
  field_simp
  ring

/-- `L_d = m + d + 1`, the rank of the row `d + 1`. -/
noncomputable def Lrk6 (m : ℚ) (d : ℕ) : ℝ := (m : ℝ) + d + 1

/-- **The formal rank recurrence of the `6j` germ** (`eq:6jrec` for the formal Taylor series, rows
`f = m+d+1`): in `ℝ⟦t⟧`,
`(2f+1)[λ_f x - mn]Ψ_f - (2f+1)λ_f q_f t Ψ_f = (f+1)R_f η_f Ψ_{f-1} + f R_{f+1} η_{f+1} Ψ_{f+1}`. -/
theorem Psi6_rank (hp : m - n = p) (hq : m + n = q) (hs : (α, β, γ) ∈ StrictTri) (d : ℕ) :
    PowerSeries.C ((2 * Lrk6 m d + 1) * (Lrk6 m d * (Lrk6 m d + 1) * cosA α β γ - m * n)) *
          PsiSer6 m n α β γ (d + 1) -
        PowerSeries.C ((2 * Lrk6 m d + 1) * (Lrk6 m d * (Lrk6 m d + 1)) * Qshift6 m n α β (Lrk6 m d)) *
          PowerSeries.X * PsiSer6 m n α β γ (d + 1) =
      PowerSeries.C ((Lrk6 m d + 1) * rootR m n (Lrk6 m d)) * Eta6 α β (Lrk6 m d) * PsiSer6 m n α β γ d +
        PowerSeries.C (Lrk6 m d * rootR m n (Lrk6 m d + 1)) * Eta6 α β (Lrk6 m d + 1) *
          PsiSer6 m n α β γ (d + 2) := by
  have hα : 0 < α := hs.1
  have hβ : 0 < β := hs.2.1
  have hm0 : 0 ≤ m := m_nonneg_of_labels hp hq
  set L := Lrk6 m d with hL
  have hpt : ∀ t : ℝ, (2 * L + 1) * (L * (L + 1) * cosA α β γ - m * n) * pF6 m n α β γ (d + 1) t -
      (2 * L + 1) * (L * (L + 1)) * Qshift6 m n α β L * (t * pF6 m n α β γ (d + 1) t) =
      (L + 1) * rootR m n L * ((1 - (L ^ 2 / (4 * α ^ 2)) * t) * (1 - (L ^ 2 / (4 * β ^ 2)) * t) *
        pF6 m n α β γ d t) + L * rootR m n (L + 1) * pF6 m n α β γ (d + 2) t := by
    intro t
    have h := pF6_rank (γ := γ) hp hq hα.ne' hβ.ne' d t
    simp only [hL, Lrk6] at h ⊢
    linear_combination h
  have sp := smoothAt0_pF6 (m := m) (n := n) (α := α) (β := β) (γ := γ)
  have hlin : ∀ c : ℝ, SmoothAt0 (fun t : ℝ => 1 - c * t) :=
    fun c => (SmoothAt0.const 1).sub ((SmoothAt0.const _).mul SmoothAt0.id)
  have hP : PowerSeries.C ((2 * L + 1) * (L * (L + 1) * cosA α β γ - m * n)) *
        taylorSer (pF6 m n α β γ (d + 1)) -
      PowerSeries.C ((2 * L + 1) * (L * (L + 1)) * Qshift6 m n α β L) *
        (PowerSeries.X * taylorSer (pF6 m n α β γ (d + 1))) =
      PowerSeries.C ((L + 1) * rootR m n L) *
        ((1 - PowerSeries.C (L ^ 2 / (4 * α ^ 2)) * PowerSeries.X) *
          (1 - PowerSeries.C (L ^ 2 / (4 * β ^ 2)) * PowerSeries.X) * taylorSer (pF6 m n α β γ d)) +
        PowerSeries.C (L * rootR m n (L + 1)) * taylorSer (pF6 m n α β γ (d + 2)) := by
    have h1 := congrArg taylorSer (funext hpt)
    have hA : SmoothAt0 (fun t => (2 * L + 1) * (L * (L + 1) * cosA α β γ - m * n) *
        pF6 m n α β γ (d + 1) t) := (SmoothAt0.const _).mul (sp (d + 1))
    have hB : SmoothAt0 (fun t => (2 * L + 1) * (L * (L + 1)) * Qshift6 m n α β L *
        (t * pF6 m n α β γ (d + 1) t)) := (SmoothAt0.const _).mul (SmoothAt0.id.mul (sp (d + 1)))
    have hC : SmoothAt0 (fun t => (1 - (L ^ 2 / (4 * α ^ 2)) * t) * (1 - (L ^ 2 / (4 * β ^ 2)) * t) *
        pF6 m n α β γ d t) := ((hlin _).mul (hlin _)).mul (sp d)
    rw [taylorSer_sub hA hB, taylorSer_add ((SmoothAt0.const _).mul hC) ((SmoothAt0.const _).mul (sp (d + 2))),
      taylorSer_C_mul (sp (d + 1)), taylorSer_C_mul (SmoothAt0.id.mul (sp (d + 1))),
      taylorSer_mul SmoothAt0.id (sp (d + 1)), taylorSer_id, taylorSer_C_mul hC,
      taylorSer_C_mul (sp (d + 2)), taylorSer_mul ((hlin _).mul (hlin _)) (sp d),
      taylorSer_mul (hlin _) (hlin _), taylorSer_lin, taylorSer_lin] at h1
    exact h1
  have hSd : taylorSer (sF6 m α β d) = Eta6 α β L * taylorSer (sF6 m α β (d + 1)) :=
    sF6_relation hm0 d
  have hSd1 : taylorSer (sF6 m α β (d + 1)) = Eta6 α β (L + 1) * taylorSer (sF6 m α β (d + 2)) := by
    have := sF6_relation (α := α) (β := β) hm0 (d + 1)
    simp only [hL, Lrk6]
    push_cast at this ⊢
    rw [this]; ring_nf
  have heps := E6_sq α β L
  rw [taylorSer_G6c hs d, taylorSer_G6c hs (d + 1), taylorSer_G6c hs (d + 2), hSd]
  have hS1' : Eta6 α β (L + 1) * taylorSer (sF6 m α β (d + 2)) = taylorSer (sF6 m α β (d + 1)) := hSd1.symm
  linear_combination (taylorSer (aF6 m n α β γ) * taylorSer (sF6 m α β (d + 1))) * hP -
    (PowerSeries.C ((L + 1) * rootR m n L) * taylorSer (aF6 m n α β γ) *
      taylorSer (sF6 m α β (d + 1)) * taylorSer (pF6 m n α β γ d)) * heps -
    (PowerSeries.C (L * rootR m n (L + 1)) * taylorSer (aF6 m n α β γ) *
      taylorSer (pF6 m n α β γ (d + 2))) * hS1'

/-- **The row at the minimal rank** `f = m` (`R_m = 0`, `m ≠ 0`):
`(2m+1)[λ_m x - mn]Ψ_0 - (2m+1)λ_m q_m tΨ_0 = m R_{m+1} η(m+1) Ψ_1`. -/
theorem Psi6_rank_row0 (hp : m - n = p) (hq : m + n = q) (hs : (α, β, γ) ∈ StrictTri) (hm : m ≠ 0) :
    PowerSeries.C ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) * cosA α β γ - m * n)) *
          PsiSer6 m n α β γ 0 -
        PowerSeries.C ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) * Qshift6 m n α β (m : ℝ)) *
          (PowerSeries.X * PsiSer6 m n α β γ 0) =
      PowerSeries.C ((m : ℝ) * rootR m n ((m : ℝ) + 1)) * (Eta6 α β ((m : ℝ) + 1) * PsiSer6 m n α β γ 1) := by
  have hα : 0 < α := hs.1
  have hβ : 0 < β := hs.2.1
  have hm0 : 0 ≤ m := m_nonneg_of_labels hp hq
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hR : 0 < rootR m n ((m : ℝ) + 1) := rootR_pos_canon p q hp hq (by linarith)
  have hpt : ∀ t : ℝ, (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) * cosA α β γ - m * n) *
        pF6 m n α β γ 0 t -
      (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) * Qshift6 m n α β (m : ℝ) * (t * pF6 m n α β γ 0 t) =
      (m : ℝ) * rootR m n ((m : ℝ) + 1) * pF6 m n α β γ 1 t := by
    intro t
    have h1 := ptilde6_one_of_ne m n hm ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2) (t / (α * β))
    have e1 : (1 : ℝ) - 2 * ((1 - cosA α β γ) / 2) = cosA α β γ := by ring
    unfold pF6 Qshift6
    rw [h1, ptilde6_zero, e1]
    field_simp
    ring
  have sp := smoothAt0_pF6 (m := m) (n := n) (α := α) (β := β) (γ := γ)
  have hP : PowerSeries.C ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) * cosA α β γ - m * n)) *
        taylorSer (pF6 m n α β γ 0) -
      PowerSeries.C ((2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1)) * Qshift6 m n α β (m : ℝ)) *
        (PowerSeries.X * taylorSer (pF6 m n α β γ 0)) =
      PowerSeries.C ((m : ℝ) * rootR m n ((m : ℝ) + 1)) * taylorSer (pF6 m n α β γ 1) := by
    have h1 := congrArg taylorSer (funext hpt)
    rw [taylorSer_sub ((SmoothAt0.const _).mul (sp 0))
        ((SmoothAt0.const _).mul (SmoothAt0.id.mul (sp 0))),
      taylorSer_C_mul (sp 0), taylorSer_C_mul (SmoothAt0.id.mul (sp 0)),
      taylorSer_mul SmoothAt0.id (sp 0), taylorSer_id, taylorSer_C_mul (sp 1)] at h1
    exact h1
  have hS0 : taylorSer (sF6 m α β 0) = Eta6 α β ((m : ℝ) + 1) * taylorSer (sF6 m α β 1) := by
    have := sF6_relation (α := α) (β := β) hm0 0
    simpa using this
  rw [taylorSer_G6c hs 0, taylorSer_G6c hs 1, hS0]
  linear_combination (taylorSer (aF6 m n α β γ) * Eta6 α β ((m : ℝ) + 1) * taylorSer (sF6 m α β 1)) * hP

/-! ### The scalar sector `m = n = 0`: the two starts -/

lemma G6c_zero_zero_zero (α β γ t : ℝ) : G6c 0 0 0 α β γ t = 1 := by
  simp [G6c, edgeSqT, piSixT, Ct_zero, ptilde6_zero]

lemma Psi6_zero_zero_zero (α β γ : ℝ) : PsiSer6 0 0 α β γ 0 = 1 := by
  unfold PsiSer6
  have : G6c 0 0 0 α β γ = fun _ => 1 := funext (G6c_zero_zero_zero α β γ)
  rw [this, taylorSer_one]

/-- **The second start of the scalar sector** (`eq:6jexceptionalseed`, `prop:localcalculus` (c)):
`η(1) Ψ_1 = x - t/(8αβ)` (`q(0) = 1/(8αβ)`). -/
theorem Psi6_zero_zero_one (hs : (α, β, γ) ∈ StrictTri) :
    Eta6 α β 1 * PsiSer6 0 0 α β γ 1 =
      PowerSeries.C (cosA α β γ) - PowerSeries.C (1 / (8 * α * β)) * PowerSeries.X := by
  have hα : 0 < α := hs.1
  have hβ : 0 < β := hs.2.1
  have hA : taylorSer (aF6 0 0 α β γ) = 1 := by
    have : aF6 0 0 α β γ = fun _ => 1 := by
      funext t; simp [aF6, edgeSqT, Ct_zero]
    rw [this, taylorSer_one]
  have hS0 : taylorSer (sF6 (0 : ℚ) α β 0) = 1 := by
    have : sF6 (0 : ℚ) α β 0 = fun _ => 1 := by
      funext t; simp [sF6, piSixT]
    rw [this, taylorSer_one]
  have hP : taylorSer (pF6 0 0 α β γ 1) =
      PowerSeries.C (cosA α β γ) - PowerSeries.C (1 / (8 * α * β)) * PowerSeries.X := by
    have : pF6 0 0 α β γ 1 = fun t => cosA α β γ - (1 / (8 * α * β)) * t := by
      funext t
      simp only [pF6]
      rw [ptilde6_one_of_eq]
      field_simp
      ring
    rw [this, taylorSer_sub (SmoothAt0.const _) ((SmoothAt0.const _).mul SmoothAt0.id), taylorSer_const,
      taylorSer_C_mul SmoothAt0.id, taylorSer_id]
  have hrel := sF6_relation (m := (0 : ℚ)) (α := α) (β := β) le_rfl 0
  simp only [Rat.cast_zero, Nat.cast_zero, zero_add] at hrel
  rw [hS0] at hrel
  rw [taylorSer_G6c hs 1, hA, hP]
  linear_combination (PowerSeries.C (cosA α β γ) - PowerSeries.C (1 / (8 * α * β)) * PowerSeries.X) *
    (-1 : PowerSeries ℝ) * hrel

/-! ### The `rankDefect` form -/

/-- The diagonal shift `q(λ) = (2λ+1-m²-n²)/(8αβ)` of `app:6j-allorder` as a polynomial in `λ`. -/
noncomputable def qPoly6 (m n : ℚ) (α β : ℝ) : Polynomial ℝ :=
  Polynomial.C (2 / (8 * α * β)) * Polynomial.X +
    Polynomial.C ((1 - ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) / (8 * α * β))

lemma q6_eval (m n : ℚ) (α β L : ℝ) : (qPoly6 m n α β).eval (L * (L + 1)) = Qshift6 m n α β L := by
  unfold qPoly6 Qshift6
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

lemma shiftS_real (F : PowerSeries ℝ) (r : ℕ) :
    LocalCalculus.shiftS (fun r => PowerSeries.coeff r F) r = PowerSeries.coeff r (PowerSeries.X * F) := by
  cases r with
  | zero => simp [LocalCalculus.shiftS]
  | succ r => simp [LocalCalculus.shiftS, PowerSeries.coeff_succ_X_mul]

lemma mk_coeff_self (F : PowerSeries ℝ) : PowerSeries.mk (fun r => PowerSeries.coeff r F) = F := by
  ext r; simp

/-- **The germ's Taylor coefficients solve the deformed rank recurrence at every rank `≥ 1`**
(`eq:6jrec` order by order, rows `f = m+n'+1`): in the form `rankDefect = 0` of `P2LocalCalculusSeries`, for
the module `ℝ` with `x` acting as multiplication by `cosA α β γ`, `q = qPoly6`, `τ = nm`, `e_s = eta6c`,
`R_j = R_{m+j}`, `k₀ = m` (`τ = nm = mn`). -/
theorem G6c_rankDefect_succ (hp : m - n = p) (hq : m + n = q) (hs : (α, β, γ) ∈ StrictTri) (n' : ℕ) :
    LocalCalculus.rankDefect (M := ℝ) (LinearMap.lsmul ℝ ℝ (cosA α β γ)) (qPoly6 m n α β) (eta6c α β)
        ((n : ℝ) * m) (m : ℝ) (fun j => rootR m n ((m : ℝ) + j))
        (fun d r => PowerSeries.coeff r (PsiSer6 m n α β γ d)) (n' + 1) = 0 := by
  funext r
  have h := congrArg (PowerSeries.coeff r) (Psi6_rank hp hq hs n')
  simp only [mul_assoc, PowerSeries.coeff_C_mul, map_sub, map_add] at h
  have hk : (m : ℝ) + ((n' + 1 : ℕ) : ℝ) = Lrk6 m n' := by unfold Lrk6; push_cast; ring
  have hk2 : (m : ℝ) + ((n' + 1 + 1 : ℕ) : ℝ) = Lrk6 m n' + 1 := by unfold Lrk6; push_cast; ring
  unfold LocalCalculus.rankDefect LocalCalculus.defectS
  simp only [hk, hk2, LocalCalculus.prevS, smul_eq_mul, LinearMap.lsmul_apply, Pi.zero_apply]
  rw [coeff_smulS_real, coeff_smulS_real, eta_e6, eta_e6, mk_coeff_self, mk_coeff_self, shiftS_real]
  have e : n' + 1 + 1 = n' + 2 := rfl
  simp only [e, LocalCalculus.lam, q6_eval]
  linear_combination h

/-- The row `n' = 0` of the rank recurrence (rank `f = m`, `R_m = 0`; `m ≠ 0`). -/
theorem G6c_rankDefect_zero (hp : m - n = p) (hq : m + n = q) (hs : (α, β, γ) ∈ StrictTri) (hm : m ≠ 0) :
    LocalCalculus.rankDefect (M := ℝ) (LinearMap.lsmul ℝ ℝ (cosA α β γ)) (qPoly6 m n α β) (eta6c α β)
        ((n : ℝ) * m) (m : ℝ) (fun j => rootR m n ((m : ℝ) + j))
        (fun d r => PowerSeries.coeff r (PsiSer6 m n α β γ d)) 0 = 0 := by
  funext r
  have h := congrArg (PowerSeries.coeff r) (Psi6_rank_row0 hp hq hs hm)
  simp only [mul_assoc, PowerSeries.coeff_C_mul, map_sub] at h
  have hR0 : rootR (m : ℝ) (n : ℝ) (m : ℝ) = 0 := by simp [rootR]
  unfold LocalCalculus.rankDefect LocalCalculus.defectS
  simp only [LocalCalculus.prevS, smul_eq_mul, LinearMap.lsmul_apply, Pi.zero_apply, Nat.cast_zero,
    add_zero, zero_add]
  rw [coeff_smulS_real, eta_e6, mk_coeff_self, shiftS_real]
  simp only [LocalCalculus.lam, q6_eval, Nat.cast_one, hR0, zero_mul, mul_zero, sub_zero]
  linear_combination h

/-- `a_{m+d,r}` is the `t^r` coefficient of `Ψ_d` (`G6` in the canonical sector is `G6c`). -/
theorem a6_eq_coeff_Psi6 (hn : |n| ≤ m) (d r : ℕ) (α β γ : ℝ) :
    a6 (m + (d : ℚ)) m n r (α, β, γ) = PowerSeries.coeff r (PsiSer6 m n α β γ d) := by
  have e : (fun t => G6 (m + (d : ℚ)) m n α β γ t) = G6c m n d α β γ := by
    funext t
    unfold G6
    simp [hn]
  unfold PsiSer6 a6 taylorCoeff
  rw [coeff_taylorSer, ← e]

end Rank

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.Psi6_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Psi6_rank

/-- info: 'FormalResearch.Racah.G6c_rankDefect_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.G6c_rankDefect_succ

/-- info: 'FormalResearch.Racah.G6c_rankDefect_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.G6c_rankDefect_zero

/-- info: 'FormalResearch.Racah.Psi6_zero_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Psi6_zero_zero_one

/-- info: 'FormalResearch.Racah.a6_eq_coeff_Psi6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.a6_eq_coeff_Psi6

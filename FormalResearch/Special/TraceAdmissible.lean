module

public import Mathlib
public import FormalResearch.Special.LatticeVarTail

/-!
# Admissible weights and the cutoff `h = h₁ + h₂` of `thm:tracecore`

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `def:admissible` and the proof of `thm:tracecore`.
With `d(t) = t(1-t)` (`ddf`), a function `h` is `(σ,δ,κ)`-admissible with constant `C_h` (`Admissible`) if it is
continuous on `[0,1]`, `C¹` on `(0,1)` with `|h| ≤ C_h d^σ(1+|log d|)`, `|h'| ≤ C_h d^{σ-1}(1+|log d|)`, and
`s ↦ h(ν(2πs))` has an analytic extension `g` to `|Im s| ≤ δ` with `|g| ≤ C_h e^{-κ|Re s|}`.
(Formalised with `h : ℝ → ℂ`, only its values on `[0,1]` being used; `g` is `DifferentiableOn ℂ` the closed strip,
which is at most as strong as analyticity on a neighbourhood of it; the field `dcont` is part of the paper's
definition but is not used by any proof here.  An instance: `h(t) = t(1-t)` with `σ = 1`, `δ = ¼`, `κ = 2π`, `C_h = 2`,
for which `g(s) = 1/(4 cosh² πs)`, `|g| ≤ e^{-2π|Re s|}` on the strip, checked numerically.)

The cutoff is the piecewise linear `χ(y) = min(max(y-1,0),1)` (`cutχ`; the paper's smooth `χ₀` is used only through
Lipschitz bounds, which `χ` satisfies with constant `1` instead of `2`), `ψ_ρ(t) = χ(d(t)/ρ)`,
`h₁ = ψ_ρ h` (`h1fn`), `h₂ = h - h₁` (`h2fn`).  For `0 < ρ ≤ 1/8`:

* `Admissible.zero_left`, `Admissible.zero_right` : `h(0) = h(1) = 0` (from (a) and continuity);
* `h1fn_eq_zero` : `h₁(t) = 0` where `d(t) ≤ ρ`;
* `h1_lipschitz` : `h₁` is `Λ₁`-Lipschitz on `[0,1]` with
  `Λ₁ = C_h ρ^{σ-1}(1+|log ρ|) + C_h (2ρ)^σ (1+|log ρ|)/ρ` (the paper's `sup|h₁'| ≤ C C_h ρ^{σ-1}(1+|log ρ|)`;
  the proof is by the mean value inequality for `h` on `{d ≥ ρ}`, not by differentiating the product);
* `h2fn_bound` : `|h₂(t)| ≤ C_h K_ρ d(t)^{σ/2}` on `[0,1]`, `K_ρ = (1 + 12/σ)(2ρ)^{5σ/12}`
  (the paper has `ε_ρ = ρ^{σ/2}(1+|log ρ|)`; here the exponent is `5σ/12`, which is all that the exponent
  `b_h = min(σ a/3, b₁)` needs and avoids a monotonicity argument for `d^{σ/2}(1+|log d|)`);
* `dd_nuR_le` : `d(ν(2πx)) ≤ e^{-2π|x|}`.
-/

@[expose] public section

namespace FormalResearch.Special.TraceCore

open Filter Topology Set FormalResearch.Special.Lattice

/-- `d(t) = t(1-t)`. -/
noncomputable def ddf (t : ℝ) : ℝ := t * (1 - t)

/-- `(σ, δ, κ)`-admissible weights with constant `C_h` (`def:admissible`). -/
structure Admissible (σ δ κ Ch : ℝ) (h : ℝ → ℂ) : Prop where
  cont : ContinuousOn h (Icc 0 1)
  diff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ h t
  dcont : ContinuousOn (deriv h) (Ioo 0 1)
  ha1 : ∀ t ∈ Ioo (0 : ℝ) 1, ‖h t‖ ≤ Ch * ddf t ^ σ * (1 + |Real.log (ddf t)|)
  ha2 : ∀ t ∈ Ioo (0 : ℝ) 1, ‖deriv h t‖ ≤ Ch * ddf t ^ (σ - 1) * (1 + |Real.log (ddf t)|)
  ext : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s | |s.im| ≤ δ} ∧ (∀ x : ℝ, g (x : ℂ) = h (nuR (2 * Real.pi * x))) ∧
    ∀ s : ℂ, |s.im| ≤ δ → ‖g s‖ ≤ Ch * Real.exp (-κ * |s.re|)

/-- The cutoff profile `χ(y) = min(max(y-1,0),1)`. -/
noncomputable def cutχ (y : ℝ) : ℝ := min (max (y - 1) 0) 1

/-- `ψ_ρ(t) = χ(d(t)/ρ)`. -/
noncomputable def psiρ (ρ t : ℝ) : ℝ := cutχ (ddf t / ρ)

/-- `h₁ = ψ_ρ h`. -/
noncomputable def h1fn (ρ : ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ := (psiρ ρ t : ℂ) * h t

/-- `h₂ = h - h₁`. -/
noncomputable def h2fn (ρ : ℝ) (h : ℝ → ℂ) (t : ℝ) : ℂ := h t - h1fn ρ h t

lemma cutχ_mem (y : ℝ) : 0 ≤ cutχ y ∧ cutχ y ≤ 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma cutχ_lip (a b : ℝ) : |cutχ a - cutχ b| ≤ |a - b| := by
  unfold cutχ
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  have h1 := abs_max_sub_max_le_abs (a - 1) (b - 1) 0
  have : |a - 1 - (b - 1)| = |a - b| := by ring_nf
  rw [this] at h1
  simpa using h1

lemma cutχ_eq_zero {y : ℝ} (hy : y ≤ 1) : cutχ y = 0 := by
  unfold cutχ
  rw [max_eq_right (by linarith), min_eq_left zero_le_one]

lemma cutχ_eq_one {y : ℝ} (hy : 2 ≤ y) : cutχ y = 1 := by
  unfold cutχ
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

lemma lt_two_of_cutχ_lt {y : ℝ} (h : cutχ y < 1) : y < 2 := by
  by_contra hc
  rw [cutχ_eq_one (not_lt.mp hc)] at h
  exact lt_irrefl _ h

lemma ddf_lip {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |ddf a - ddf b| ≤ |a - b| := by
  have e : ddf a - ddf b = (a - b) * (1 - a - b) := by unfold ddf; ring
  rw [e, abs_mul]
  have : |1 - a - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  nlinarith [abs_nonneg (a - b)]

lemma ddf_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ ddf t :=
  mul_nonneg ht.1 (by linarith [ht.2])

lemma ddf_le_quarter (t : ℝ) : ddf t ≤ 1 / 4 := by unfold ddf; nlinarith [sq_nonneg (t - 1 / 2)]

lemma ddf_symm (t : ℝ) : ddf (1 - t) = ddf t := by unfold ddf; ring

lemma psiρ_mem (ρ t : ℝ) : 0 ≤ psiρ ρ t ∧ psiρ ρ t ≤ 1 := cutχ_mem _

lemma psiρ_eq_zero {ρ t : ℝ} (hρ : 0 < ρ) (h : ddf t ≤ ρ) : psiρ ρ t = 0 :=
  cutχ_eq_zero ((div_le_one hρ).2 h)

lemma psiρ_eq_one {ρ t : ℝ} (hρ : 0 < ρ) (h : 2 * ρ ≤ ddf t) : psiρ ρ t = 1 :=
  cutχ_eq_one (by rw [le_div_iff₀ hρ]; linarith)

lemma ddf_lt_of_psiρ_lt {ρ t : ℝ} (hρ : 0 < ρ) (h : psiρ ρ t < 1) : ddf t < 2 * ρ := by
  have := lt_two_of_cutχ_lt h
  rw [div_lt_iff₀ hρ] at this; linarith

lemma psiρ_lip {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |psiρ ρ a - psiρ ρ b| ≤ |a - b| / ρ := by
  unfold psiρ
  refine (cutχ_lip _ _).trans ?_
  rw [← sub_div, abs_div, abs_of_pos hρ]
  exact div_le_div_of_nonneg_right (ddf_lip ha hb) hρ.le

lemma tendsto_G_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun x : ℝ => x ^ σ * (1 + |Real.log x|)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ σ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 σ (Or.inr hσ.le)).tendsto
    rw [Real.zero_rpow hσ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x : ℝ => Real.log x * x ^ σ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero hσ
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, x ^ σ * (1 + |Real.log x|) = x ^ σ - Real.log x * x ^ σ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [abs_of_neg (Real.log_neg hx.1 hx.2)]; ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  simpa using h1.sub h2

/-- A function continuous at the endpoint `a ∈ {0,1}` (within `(0,1)`) and bounded by `C d^σ(1+|log d|)` on `(0,1)`
vanishes at `a`. -/
lemma zero_of_bound {σ Ch : ℝ} {h : ℝ → ℂ} {a : ℝ} (hσ : 0 < σ) (ha : a = 0 ∨ a = 1)
    (hc : ContinuousWithinAt h (Ioo 0 1) a)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, ‖h t‖ ≤ Ch * ddf t ^ σ * (1 + |Real.log (ddf t)|)) : h a = 0 := by
  have hda : ddf a = 0 := by rcases ha with rfl | rfl <;> simp [ddf]
  have hcl : a ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rcases ha with rfl | rfl <;> simp
  have : (𝓝[Ioo (0 : ℝ) 1] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have h1 : Tendsto h (𝓝[Ioo 0 1] a) (𝓝 (h a)) := hc
  have hdd : Tendsto ddf (𝓝[Ioo 0 1] a) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous ddf := by unfold ddf; fun_prop
      have := hcont.continuousAt.tendsto (x := a)
      rw [hda] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht.1 (by linarith [ht.2])
  have hG := (tendsto_G_zero hσ).comp hdd
  have h2 : Tendsto (fun t => ‖h t‖) (𝓝[Ioo 0 1] a) (𝓝 0) := by
    have hG' : Tendsto (fun t => Ch * (ddf t ^ σ * (1 + |Real.log (ddf t)|))) (𝓝[Ioo 0 1] a) (𝓝 0) := by
      simpa using hG.const_mul Ch
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hG'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have := hb t ht
    calc ‖h t‖ ≤ _ := this
      _ = _ := by ring
  have h3 : Tendsto (fun t => ‖h t‖) (𝓝[Ioo 0 1] a) (𝓝 ‖h a‖) := h1.norm
  have := tendsto_nhds_unique h3 h2
  exact norm_eq_zero.mp this

lemma Admissible.zero_left {σ δ κ Ch : ℝ} {h : ℝ → ℂ} (H : Admissible σ δ κ Ch h) (hσ : 0 < σ) :
    h 0 = 0 :=
  zero_of_bound hσ (Or.inl rfl) ((H.cont 0 ⟨le_rfl, zero_le_one⟩).mono Ioo_subset_Icc_self) H.ha1

lemma Admissible.zero_right {σ δ κ Ch : ℝ} {h : ℝ → ℂ} (H : Admissible σ δ κ Ch h) (hσ : 0 < σ) :
    h 1 = 0 :=
  zero_of_bound hσ (Or.inr rfl) ((H.cont 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self) H.ha1

lemma abs_log_le_of_le {ρ x : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ x) (h2 : x ≤ 1) :
    |Real.log x| ≤ |Real.log ρ| := by
  have hx : 0 < x := lt_of_lt_of_le hρ h1
  have a1 : Real.log ρ ≤ Real.log x := Real.log_le_log hρ h1
  have a2 : Real.log x ≤ 0 := Real.log_nonpos hx.le h2
  rw [abs_of_nonpos a2, abs_of_nonpos (a1.trans a2)]
  linarith

/-- Lipschitz bound for a product with a bounded cutoff, on a set where the cutoff is
`c`-Lipschitz, `h` is `H`-Lipschitz, and `h` is bounded by `B` wherever the cutoff is `< 1`. -/
lemma lip_mul_cutoff {J : Set ℝ} {h : ℝ → ℂ} {ψ : ℝ → ℝ} {H B c : ℝ}
    (hψ0 : ∀ a ∈ J, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hh : ∀ a ∈ J, ∀ b ∈ J, ‖h a - h b‖ ≤ H * |a - b|)
    (hψ : ∀ a ∈ J, ∀ b ∈ J, |ψ a - ψ b| ≤ c * |a - b|)
    (hB : ∀ a ∈ J, ψ a < 1 → ‖h a‖ ≤ B) (hc : 0 ≤ c) (hBn : 0 ≤ B) :
    ∀ a ∈ J, ∀ b ∈ J, ‖(ψ a : ℂ) * h a - (ψ b : ℂ) * h b‖ ≤ (H + B * c) * |a - b| := by
  intro a ha b hb
  have hab := abs_nonneg (a - b)
  have key : ∀ a ∈ J, ∀ b ∈ J, ψ a < 1 →
      ‖(ψ a : ℂ) * h a - (ψ b : ℂ) * h b‖ ≤ (H + B * c) * |a - b| := by
    intro a ha b hb hlt
    have e : (ψ a : ℂ) * h a - (ψ b : ℂ) * h b =
        (ψ b : ℂ) * (h a - h b) + ((ψ a - ψ b : ℝ) : ℂ) * h a := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hψ0 b hb).1]
    have t1 : ψ b * ‖h a - h b‖ ≤ H * |a - b| := by
      calc ψ b * ‖h a - h b‖ ≤ 1 * ‖h a - h b‖ :=
            mul_le_mul_of_nonneg_right (hψ0 b hb).2 (norm_nonneg _)
        _ ≤ H * |a - b| := by rw [one_mul]; exact hh a ha b hb
    have t2 : |ψ a - ψ b| * ‖h a‖ ≤ B * c * |a - b| := by
      calc |ψ a - ψ b| * ‖h a‖ ≤ (c * |a - b|) * B :=
            mul_le_mul (hψ a ha b hb) (hB a ha hlt) (norm_nonneg _) (by positivity)
        _ = B * c * |a - b| := by ring
    linarith
  by_cases h1 : ψ a < 1
  · exact key a ha b hb h1
  · by_cases h2 : ψ b < 1
    · have := key b hb a ha h2
      rw [norm_sub_rev, abs_sub_comm] at this
      exact this
    · have ea : ψ a = 1 := le_antisymm (hψ0 a ha).2 (not_lt.mp h1)
      have eb : ψ b = 1 := le_antisymm (hψ0 b hb).2 (not_lt.mp h2)
      rw [ea, eb]
      simp only [Complex.ofReal_one, one_mul]
      calc ‖h a - h b‖ ≤ H * |a - b| := hh a ha b hb
        _ ≤ (H + B * c) * |a - b| := by nlinarith [mul_nonneg hBn hc]

/-- `h₁ = ψ_ρ h` is Lipschitz on `[0,1]`. -/
theorem h1_lipschitz {σ δ κ Ch : ℝ} {h : ℝ → ℂ} (H : Admissible σ δ κ Ch h) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hCh : 0 ≤ Ch) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖h1fn ρ h a - h1fn ρ h b‖ ≤
        (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) + Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ)) *
          |a - b| := by
  set J : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ρ ≤ ddf t} with hJ
  have hJo : ∀ t ∈ J, t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨⟨h0, h1⟩, hd⟩ := ht
    refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
    · rintro rfl; simp [ddf] at hd; linarith
    · rintro rfl; simp [ddf] at hd; linarith
  have hJc : Convex ℝ J := by
    intro a ha b hb θ1 θ2 h1 h2 h12
    obtain ⟨⟨ha0, ha1⟩, had⟩ := ha
    obtain ⟨⟨hb0, hb1⟩, hbd⟩ := hb
    have hθ : θ2 = 1 - θ1 := by linarith
    subst hθ
    simp only [smul_eq_mul]
    refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
    have e : ddf (θ1 * a + (1 - θ1) * b) =
        θ1 * ddf a + (1 - θ1) * ddf b + θ1 * (1 - θ1) * (a - b) ^ 2 := by
      simp only [ddf]; ring
    rw [e]
    have : 0 ≤ θ1 * (1 - θ1) * (a - b) ^ 2 := by
      have := mul_nonneg h1 h2; positivity
    nlinarith
  -- Lipschitz bound for `h` on `J`
  set H0 : ℝ := Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) with hH0
  have hdiff : ∀ x ∈ J, DifferentiableAt ℝ h x := fun x hx => H.diff x (hJo x hx)
  have hder : ∀ x ∈ J, ‖deriv h x‖ ≤ H0 := by
    intro x hx
    have hxd : ρ ≤ ddf x := hx.2
    have hxo := hJo x hx
    refine (H.ha2 x hxo).trans ?_
    have hdd1 : ddf x ≤ 1 := (ddf_le_quarter x).trans (by norm_num)
    have a1 : ddf x ^ (σ - 1) ≤ ρ ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hρ hxd (by linarith)
    have a2 := abs_log_le_of_le hρ hxd hdd1
    have : 0 ≤ ρ ^ (σ - 1) := (Real.rpow_pos_of_pos hρ _).le
    calc Ch * ddf x ^ (σ - 1) * (1 + |Real.log (ddf x)|)
        ≤ Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left a1 hCh) (by linarith) (by positivity)
            (by positivity)
      _ = H0 := hH0.symm
  have hHnn : 0 ≤ H0 := by positivity
  have hh : ∀ a ∈ J, ∀ b ∈ J, ‖h a - h b‖ ≤ H0 * |a - b| := by
    intro a ha b hb
    have := hJc.norm_image_sub_le_of_norm_deriv_le hdiff hder hb ha
    rwa [Real.norm_eq_abs] at this
  -- bound for `h` where the cutoff is not 1
  set B0 : ℝ := Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) with hB0
  have hBnn : 0 ≤ B0 := by positivity
  have hB : ∀ a ∈ J, psiρ ρ a < 1 → ‖h a‖ ≤ B0 := by
    intro a ha hlt
    have hlt2 := ddf_lt_of_psiρ_lt hρ hlt
    have had : ρ ≤ ddf a := ha.2
    refine (H.ha1 a (hJo a ha)).trans ?_
    have hdd1 : ddf a ≤ 1 := (ddf_le_quarter a).trans (by norm_num)
    have a1 : ddf a ^ σ ≤ (2 * ρ) ^ σ :=
      Real.rpow_le_rpow (hρ.le.trans had) hlt2.le hσ.le
    have a2 := abs_log_le_of_le hρ had hdd1
    calc Ch * ddf a ^ σ * (1 + |Real.log (ddf a)|) ≤ Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left a1 hCh) (by linarith) (by positivity)
            (by positivity)
      _ = B0 := hB0.symm
  have hlipJ := lip_mul_cutoff (J := J) (h := h) (ψ := psiρ ρ) (H := H0) (B := B0) (c := 1 / ρ)
    (fun a _ => psiρ_mem ρ a) hh
    (fun a ha b hb => by
      have := psiρ_lip hρ ha.1 hb.1
      rwa [div_eq_mul_inv, mul_comm, ← one_div] at this)
    hB (by positivity) hBnn
  -- extension to `[0,1]`
  set Λ : ℝ := H0 + B0 * (1 / ρ) with hΛ
  have hlipJ' : ∀ a ∈ J, ∀ b ∈ J, ‖h1fn ρ h a - h1fn ρ h b‖ ≤ Λ * |a - b| := hlipJ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ddf t ≤ ρ → h1fn ρ h t = 0 := by
    intro t _ ht
    simp [h1fn, psiρ_eq_zero hρ ht]
  have hcd : Continuous ddf := by unfold ddf; fun_prop
  intro a ha b hb
  by_cases haJ : ρ ≤ ddf a
  · by_cases hbJ : ρ ≤ ddf b
    · exact hlipJ' a ⟨ha, haJ⟩ b ⟨hb, hbJ⟩
    · -- `b` outside `J`
      have hbz := hzero b hb (not_le.mp hbJ).le
      have hlt : ddf b < ρ := not_le.mp hbJ
      have hiv := intermediate_value_uIcc (a := b) (b := a) hcd.continuousOn
      have hmem : ρ ∈ uIcc (ddf b) (ddf a) := by
        rw [uIcc_of_le (by linarith)]; exact ⟨hlt.le, haJ⟩
      obtain ⟨e, he, hed⟩ := hiv hmem
      have heI : e ∈ Icc (0 : ℝ) 1 := by
        rw [mem_uIcc] at he
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hb.1.trans h1, h2.trans ha.2⟩
        · exact ⟨ha.1.trans h1, h2.trans hb.2⟩
      have hez : h1fn ρ h e = 0 := hzero e heI hed.le
      have := hlipJ' a ⟨ha, haJ⟩ e ⟨heI, hed.ge⟩
      rw [hez, sub_zero] at this
      rw [hbz, sub_zero]
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
      rw [mem_uIcc] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have haz := hzero a ha (not_le.mp haJ).le
    by_cases hbJ : ρ ≤ ddf b
    · have hlt : ddf a < ρ := not_le.mp haJ
      have hiv := intermediate_value_uIcc (a := a) (b := b) hcd.continuousOn
      have hmem : ρ ∈ uIcc (ddf a) (ddf b) := by
        rw [uIcc_of_le (by linarith)]; exact ⟨hlt.le, hbJ⟩
      obtain ⟨e, he, hed⟩ := hiv hmem
      have heI : e ∈ Icc (0 : ℝ) 1 := by
        rw [mem_uIcc] at he
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨ha.1.trans h1, h2.trans hb.2⟩
        · exact ⟨hb.1.trans h1, h2.trans ha.2⟩
      have hez : h1fn ρ h e = 0 := hzero e heI hed.le
      have := hlipJ' b ⟨hb, hbJ⟩ e ⟨heI, hed.ge⟩
      rw [hez, sub_zero] at this
      rw [haz, zero_sub, norm_neg]
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
      rw [mem_uIcc] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [haz, hzero b hb (not_le.mp hbJ).le, sub_zero, norm_zero]
      positivity

lemma h1fn_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (h : ℝ → ℂ) {t : ℝ} (ht : ddf t ≤ ρ) : h1fn ρ h t = 0 := by
  simp [h1fn, psiρ_eq_zero hρ ht]

/-- `d^σ (1 + |log d|) ≤ K d^{σ/2}` for `0 < d < 2ρ ≤ 1`, `K = (1 + 12/σ)(2ρ)^{5σ/12}`. -/
lemma pow_log_le {σ ρ d : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : 2 * ρ ≤ 1) (hd : 0 < d) (hd2 : d < 2 * ρ) :
    d ^ σ * (1 + |Real.log d|) ≤ ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) * d ^ (σ / 2) := by
  have hd1 : d ≤ 1 := by linarith
  have hlog : |Real.log d| ≤ 12 / σ * (d ^ (σ / 12))⁻¹ := by
    rw [abs_of_nonpos (Real.log_nonpos hd.le hd1), ← Real.log_inv]
    have := Real.log_le_rpow_div (inv_nonneg.2 hd.le) (show 0 < σ / 12 by positivity)
    rw [Real.inv_rpow hd.le] at this
    calc Real.log d⁻¹ ≤ (d ^ (σ / 12))⁻¹ / (σ / 12) := this
      _ = 12 / σ * (d ^ (σ / 12))⁻¹ := by field_simp
  have hdp : 0 < d ^ (σ / 12) := Real.rpow_pos_of_pos hd _
  have e1 : d ^ σ = d ^ (σ / 2) * d ^ (σ / 2) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have e2 : d ^ (σ / 2) * (d ^ (σ / 12))⁻¹ = d ^ (5 * σ / 12) := by
    rw [← Real.rpow_neg hd.le, ← Real.rpow_add hd]; congr 1; ring
  have a1 : d ^ (5 * σ / 12) ≤ (2 * ρ) ^ (5 * σ / 12) :=
    Real.rpow_le_rpow hd.le hd2.le (by positivity)
  have a2 : d ^ (σ / 2) ≤ (2 * ρ) ^ (5 * σ / 12) := by
    calc d ^ (σ / 2) ≤ (2 * ρ) ^ (σ / 2) := Real.rpow_le_rpow hd.le hd2.le (by positivity)
      _ ≤ (2 * ρ) ^ (5 * σ / 12) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) hρ1 (by linarith)
  have hdh : 0 ≤ d ^ (σ / 2) := (Real.rpow_pos_of_pos hd _).le
  have h12 : d ^ (σ / 2) * |Real.log d| ≤ 12 / σ * (2 * ρ) ^ (5 * σ / 12) := by
    calc d ^ (σ / 2) * |Real.log d| ≤ d ^ (σ / 2) * (12 / σ * (d ^ (σ / 12))⁻¹) :=
          mul_le_mul_of_nonneg_left hlog hdh
      _ = 12 / σ * (d ^ (σ / 2) * (d ^ (σ / 12))⁻¹) := by ring
      _ = 12 / σ * d ^ (5 * σ / 12) := by rw [e2]
      _ ≤ 12 / σ * (2 * ρ) ^ (5 * σ / 12) := mul_le_mul_of_nonneg_left a1 (by positivity)
  calc d ^ σ * (1 + |Real.log d|) = d ^ (σ / 2) * (d ^ (σ / 2) + d ^ (σ / 2) * |Real.log d|) := by
        rw [e1]; ring
    _ ≤ d ^ (σ / 2) * ((2 * ρ) ^ (5 * σ / 12) + 12 / σ * (2 * ρ) ^ (5 * σ / 12)) :=
        mul_le_mul_of_nonneg_left (add_le_add a2 h12) hdh
    _ = ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) * d ^ (σ / 2) := by ring

/-- `|h₂| ≤ C_h K_ρ d^{σ/2}` on `[0,1]`. -/
theorem h2fn_bound {σ δ κ Ch : ℝ} {h : ℝ → ℂ} (H : Admissible σ δ κ Ch h) (hσ : 0 < σ) (hCh : 0 ≤ Ch)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : 2 * ρ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖h2fn ρ h t‖ ≤ Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) * ddf t ^ (σ / 2) := by
  have hd0 : 0 ≤ ddf t ^ (σ / 2) := Real.rpow_nonneg (ddf_nonneg ht) _
  have hK : 0 ≤ Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) := by positivity
  have hrhs : 0 ≤ Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) * ddf t ^ (σ / 2) := mul_nonneg hK hd0
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp only [h2fn, h1fn, H.zero_left hσ, mul_zero, sub_zero, norm_zero]
    exact hrhs
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    simp only [h2fn, h1fn, H.zero_right hσ, mul_zero, sub_zero, norm_zero]
    exact hrhs
  have hto : t ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hdpos : 0 < ddf t := mul_pos h0 (by linarith)
  by_cases hbig : 2 * ρ ≤ ddf t
  · have : h2fn ρ h t = 0 := by simp [h2fn, h1fn, psiρ_eq_one hρ hbig]
    rw [this, norm_zero]; exact hrhs
  · have hlt := not_le.mp hbig
    have hpsi := psiρ_mem ρ t
    have e : h2fn ρ h t = ((1 - psiρ ρ t : ℝ) : ℂ) * h t := by
      simp only [h2fn, h1fn]; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hpsi.2])]
    have h1' : (1 - psiρ ρ t) * ‖h t‖ ≤ ‖h t‖ := by
      nlinarith [norm_nonneg (h t), hpsi.1]
    refine h1'.trans ((H.ha1 t hto).trans ?_)
    have := pow_log_le hσ hρ hρ1 hdpos hlt
    calc Ch * ddf t ^ σ * (1 + |Real.log (ddf t)|) = Ch * (ddf t ^ σ * (1 + |Real.log (ddf t)|)) := by ring
      _ ≤ Ch * (((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) * ddf t ^ (σ / 2)) :=
        mul_le_mul_of_nonneg_left this hCh
      _ = _ := by ring

lemma dd_nuR_le (x : ℝ) : ddf (nuR (2 * Real.pi * x)) ≤ Real.exp (-(2 * Real.pi) * |x|) := by
  have := nuR_mul_one_sub x
  unfold ddf
  rw [this]
  exact wR_two_mul_le x

/-- info: 'FormalResearch.Special.TraceCore.h1_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms h1_lipschitz

/-- info: 'FormalResearch.Special.TraceCore.h2fn_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms h2fn_bound

end FormalResearch.Special.TraceCore

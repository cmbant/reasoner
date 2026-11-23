module

public import FormalResearch.ModularBootstrap.Upper.Assembly.Wire

/-!
# The same-site window algebra for the Virasoro designs (`SameSiteFamily designClass`)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (the designs `𝔇_A`, `𝔅_κ` of the proofs
of `sr:Sigma0`, `sr:Sigma`, steps 2, 3, 5), `upper_transfer.tex` (`ut:E`, `ut:V`).

The windows are `win k d = D(N₀ + k, η_k, d)` with `η_k = 1/(k + 4)`, and `G_k` is the design-independent
factor `W_{k,0}(u)/(a_1 - u) = F(u) Q_k(u)` (`W_{k,d}(u) = G_k(u) (a_1 - d - u)`, the product `Q_k` does
not depend on `d`).

Proved here from the Lean ingredients (`lemma_E`, `lemma_V_identity`, `lemma_V_eval_one`, the sign
structure `airyWindowProd_eq_neg_mul_pos`, and the exchange identity `airyWindowProd_swap` for the first
factor `(u - u_f)`):

* `designWinW_swap`: `W_d(u) (u - a_1) = W_0(u) (u - a_1 + d)`, hence the factorisation `W_eq`;
* positivity `G_pos` (`Q > 0`), continuity `G_cont` (removable singularity at `a_1`, from the
  factorisation at `d = 0` and `d = 1`), `R_ge` (`R_1 ≥ 1/2`, `lemma_E`), `E_small`
  (`E_0 ≤ C(η_*² + N^{-1/3}) → 0`, `lemma_E`).

**The two tail estimates.**  The two uniform estimates on the product `Q_k` that are fields of
`SameSiteFamily` (the Lipschitz bound `G_upper` near `a_1`, with a design-independent constant, and the
lower bound `Q ≥ 1/2` on compacta, `G_lower`) are collected in `SameSiteTailBounds G` and
`DesignTailBounds` (for the explicit `G_k = Gd N₀ k`).  `DesignTailBounds` is proved in
`Upper.Assembly.TailBounds` (`designTailBounds`), which gives the unconditional forms
`sameSiteFamily_designClass_exists` and `virasoro_sigmaZero_unconditional`.

* **`sameSiteFamily_designClass`**: `DesignTailBounds → Nonempty (SameSiteFamily designClass)`.
* **`virasoro_sigmaZero_of_tailBounds`**: `Σ₀` at Virasoro for the extremal measures from
  `DesignTailBounds` alone.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity

/-! ### The exchange identity for the first factor -/

lemma airyWindowProd_swap (f : ℕ) (uF uF' : ℝ) (uSite epsU : ℕ → ℝ) (u : ℂ) :
    airyWindowProd f uF uSite epsU u * (u - (uF' : ℂ)) =
      airyWindowProd f uF' uSite epsU u * (u - (uF : ℂ)) := by
  unfold airyWindowProd
  dsimp only
  split_ifs <;> ring

/-- `W_d(u) (u - a_1) = W_0(u) (u - a_1 + d)`. -/
lemma designWinW_swap (N : ℕ) (η d u : ℝ) :
    designWinW N η d u * (u - airyZero 1) = designWinW N η 0 u * (u - airyZero 1 + d) := by
  have h := congrArg Complex.re (airyWindowProd_swap 1 (airyZero 1 - d) (airyZero 1 - 0)
    (designSiteU N) (designWidthU N η) (u : ℂ))
  have e1 : (u : ℂ) - (((airyZero 1 - 0 : ℝ)) : ℂ) = ((u - airyZero 1 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (u : ℂ) - (((airyZero 1 - d : ℝ)) : ℂ) = ((u - airyZero 1 + d : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2, Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h
  unfold designWinW designWindowW
  exact h

/-- `W_d(a_1) = -d R_1 Ai'(a_1)²`. -/
lemma designWinW_at_a1 (N : ℕ) (η d : ℝ) :
    designWinW N η d (airyZero 1) = -d * designR1 N η * (airyAi' (airyZero 1)) ^ 2 := by
  have h := lemma_V_eval_one N η d
  rw [deriv_airyAiC_ofReal] at h
  have hne : (airyAi' (airyZero 1)) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyNode_ne 0)
  have h2 : designWindowW N η d (airyZero 1 : ℂ) =
      ((-d * designR1 N η * (airyAi' (airyZero 1)) ^ 2 : ℝ) : ℂ) := by
    have hc : ((airyAi' (airyZero 1) : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hne
    rw [div_eq_iff hc] at h
    rw [h]; push_cast; ring
  unfold designWinW
  rw [h2, Complex.ofReal_re]

/-! ### The explicit `G_k` -/

/-- `G_k(u) = W_{k,0}(u)/(a_1 - u)` for `u ≠ a_1`, `G_k(a_1) = R_1 Ai'(a_1)²`, for the design
`D(N₀ + k, 1/(k + 4), ·)`. -/
noncomputable def Gd (N₀ k : ℕ) (u : ℝ) : ℝ :=
  if u = airyZero 1 then designR1 (N₀ + k) (1 / ((k : ℝ) + 4)) * (airyAi' (airyZero 1)) ^ 2
  else designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 0 u / (airyZero 1 - u)

/-- The two uniform estimates on `Q_k` that are fields of `SameSiteFamily` and are **not formalised**:
the design-independent Lipschitz bound near `a_1` and the lower bound `Q ≥ 1/2` on compacta below `a_1`. -/
def SameSiteTailBounds (G : ℕ → ℝ → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ k u, |u - airyNode 0| ≤ 1 →
    G k u ≤ G k (airyNode 0) * (1 + C * |u - airyNode 0|)) ∧
  (∀ K : Set ℝ, IsCompact K → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ u ∈ K, u < airyNode 0 →
    (1 / 2) * (airyAi u) ^ 2 / (u - airyNode 0) ^ 2 ≤ G k u)

/-- **Named hypothesis (not formalised): the tail bounds for the designs `D(N₀ + k, η_k, d)`.**
`Q_k(u) = ∏_{j ≥ 2} ((u - u_j)² + ε_j²)/(u - a_j)²` has a uniformly bounded logarithmic derivative on
`|u - a_1| ≤ 1` and satisfies `Q_k ≥ 1/2` on compacta below `a_1` for large `k` (`ut:E`(iv)–(v),
`sr:Sigma0`, `sr:Sigma` Step 3). -/
def DesignTailBounds : Prop := ∀ N₀ : ℕ, 1 ≤ N₀ → SameSiteTailBounds (Gd N₀)

lemma Gd_at_a1 (N₀ k : ℕ) :
    Gd N₀ k (airyZero 1) = designR1 (N₀ + k) (1 / ((k : ℝ) + 4)) * (airyAi' (airyZero 1)) ^ 2 := by
  simp [Gd]

lemma Gd_of_ne (N₀ k : ℕ) {u : ℝ} (hu : u ≠ airyZero 1) :
    Gd N₀ k u = designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 0 u / (airyZero 1 - u) := by
  unfold Gd; simp [hu]

lemma eta_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 4) := by positivity

lemma eta_le (k : ℕ) : 1 / ((k : ℝ) + 4) ≤ 1 / 4 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The factorisation `W_{k,d}(u) = G_k(u)(a_1 - d - u)`. -/
lemma designWinW_eq_Gd (N₀ k : ℕ) (d u : ℝ) :
    designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) d u = Gd N₀ k u * (airyZero 1 - d - u) := by
  by_cases hu : u = airyZero 1
  · subst hu
    rw [designWinW_at_a1, Gd_at_a1]
    ring
  · rw [Gd_of_ne N₀ k hu]
    have hne : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hne' : u - airyZero 1 ≠ 0 := sub_ne_zero.mpr hu
    have hs := designWinW_swap (N₀ + k) (1 / ((k : ℝ) + 4)) d u
    field_simp
    nlinarith [hs]

lemma designWinW_zero_eq_neg_mul_pos (N : ℕ) {η : ℝ} (hη : 0 < η) (u : ℝ) :
    ∃ S : ℝ, 0 < S ∧ designWinW N η 0 u = -(u - airyZero 1) * S := by
  obtain ⟨S, hS, h⟩ := airyWindowProd_eq_neg_mul_pos (f := 1) (airyZero 1 - 0)
    (design_tail_hypothesis N η) (fun k hk => designWidthU_ne_zero N hη hk) u
  refine ⟨S, hS, ?_⟩
  unfold designWinW designWindowW
  rw [h, Complex.ofReal_re]
  ring

lemma Gd_pos {C : ℝ} {N₀ : ℕ} (hE : ∀ N : ℕ, N₀ ≤ N → ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 →
      (1 / 2 ≤ designR1 N η ∧ designR1 N η ≤ C)) (k : ℕ) (u : ℝ) : 0 < Gd N₀ k u := by
  by_cases hu : u = airyZero 1
  · subst hu
    rw [Gd_at_a1]
    have hR := (hE (N₀ + k) (Nat.le_add_right _ _) _ (eta_pos k).le (eta_le k)).1
    have := airyAi'_airyNode_ne 0
    have hpos : 0 < (airyAi' (airyZero 1)) ^ 2 := by
      have : airyAi' (airyZero 1) ≠ 0 := this
      positivity
    exact mul_pos (by linarith) hpos
  · rw [Gd_of_ne N₀ k hu]
    obtain ⟨S, hS, h⟩ := designWinW_zero_eq_neg_mul_pos (N₀ + k) (eta_pos k) u
    rw [h]
    have hne : airyZero 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    rw [show -(u - airyZero 1) * S / (airyZero 1 - u) = S by field_simp; ring]
    exact hS

lemma continuous_Gd (N₀ k : ℕ) : Continuous (Gd N₀ k) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  by_cases hu : u₀ = airyZero 1
  · subst hu
    have hW1 : Continuous (designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 1) :=
      continuous_designWinW _ _ _
    have hc : ContinuousAt (fun u => designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 1 u /
        (airyZero 1 - 1 - u)) (airyZero 1) :=
      hW1.continuousAt.div (by fun_prop) (by norm_num)
    refine hc.congr ?_
    have : ∀ᶠ u in 𝓝 (airyZero 1), u ≠ airyZero 1 - 1 :=
      (isOpen_ne.mem_nhds (by intro h; linarith : airyZero 1 ≠ airyZero 1 - 1))
    filter_upwards [this] with u hu1
    have hne : airyZero 1 - 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    rw [designWinW_eq_Gd N₀ k 1 u]
    field_simp
  · have hW0 : Continuous (designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 0) :=
      continuous_designWinW _ _ _
    have hc : ContinuousAt (fun u => designWinW (N₀ + k) (1 / ((k : ℝ) + 4)) 0 u /
        (airyZero 1 - u)) u₀ :=
      hW0.continuousAt.div (by fun_prop) (sub_ne_zero.mpr (Ne.symm hu))
    refine hc.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hu] with u hu1
    exact (Gd_of_ne N₀ k hu1).symm

lemma designWin_V_eq_E0_bounds (N : ℕ) (η : ℝ) :
    0 ≤ windowIntegralVD N η 0 ∧ windowIntegralVD N η 0 ≤ designE0 N η := by
  have hgap : (0 : ℝ) < |airyZero 1 - airyZero 2| :=
    abs_pos.mpr (sub_ne_zero.mpr (airyZero_strictAnti le_rfl).ne')
  obtain ⟨hpi, -, -, hV, hle⟩ := lemma_V_identity N η 0 le_rfl hgap
  refine ⟨?_, ?_⟩
  · unfold windowIntegralVD
    rw [hV]
    simp only [neg_zero, zero_mul, zero_add]
    exact tsum_nonneg fun n => (hpi (n + 2) (by omega)).1
  · unfold windowIntegralVD
    simpa using hle

/-- `E_0(k) → 0` along the designs `D(N₀ + k, η_k, 0)`. -/
lemma tendsto_V_zero {C : ℝ} {N₀ : ℕ}
    (hE : ∀ N : ℕ, N₀ ≤ N → ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 →
      designE0 N η ≤ C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ)))) :
    Tendsto (fun k : ℕ => windowIntegralVD (N₀ + k) (1 / ((k : ℝ) + 4)) 0) atTop (𝓝 0) := by
  have hη : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 4)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 4)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop.congr (fun k => by simp [one_div])
  have hN : Tendsto (fun k : ℕ => ((N₀ + k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => N₀ + k) atTop atTop :=
      tendsto_atTop_mono (fun k => Nat.le_add_left k N₀) tendsto_id
    have h1 : Tendsto (fun k : ℕ => ((N₀ + k : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp h0
    have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
    exact h3
  have hb : Tendsto (fun k : ℕ => C * ((1 / ((k : ℝ) + 4)) ^ 2 +
      ((N₀ + k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have h4 := (((hη.pow 2).add hN).const_mul C)
    have h0 : C * ((0 : ℝ) ^ 2 + 0) = 0 := by ring
    rw [h0] at h4
    exact h4
  refine squeeze_zero (fun k => (designWin_V_eq_E0_bounds _ _).1) (fun k => ?_) hb
  exact (designWin_V_eq_E0_bounds _ _).2.trans
    (hE _ (Nat.le_add_right _ _) _ (eta_pos k).le (eta_le k))

/-! ### The family -/

/-- **`SameSiteFamily designClass`** from the tail bounds `DesignTailBounds`. -/
theorem sameSiteFamily_designClass (h : DesignTailBounds) : Nonempty (SameSiteFamily designClass) := by
  obtain ⟨C, hC, N₀, hN₀, hE⟩ := lemma_E
  obtain ⟨hup, hlow⟩ := h N₀ hN₀
  have hR : ∀ N : ℕ, N₀ ≤ N → ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 →
      (1 / 2 ≤ designR1 N η ∧ designR1 N η ≤ C) := fun N hN η h0 h1 => (hE N hN η h0 h1).2.2.2
  have hE0 : ∀ N : ℕ, N₀ ≤ N → ∀ η : ℝ, 0 ≤ η → η ≤ 1 / 4 →
      designE0 N η ≤ C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) :=
    fun N hN η h0 h1 => (hE N hN η h0 h1).2.2.1
  refine ⟨{
    G := Gd N₀
    win := fun k d => designWin (N₀ + k) (eta_pos k) d
    mem := fun k d _ => designWin_mem (eta_pos k) (by omega) (eta_le k) d
    W_eq := fun k d u => designWinW_eq_Gd N₀ k d u
    uF_eq := fun k d => rfl
    G_pos := fun k u _ => Gd_pos hR k u
    G_cont := continuous_Gd N₀
    R_ge := fun k => by
      rw [airyNode_zero, Gd_at_a1]
      have := (hR (N₀ + k) (Nat.le_add_right _ _) _ (eta_pos k).le (eta_le k)).1
      have hpos : 0 ≤ (airyAi' (airyZero 1)) ^ 2 := sq_nonneg _
      nlinarith
    G_upper := hup
    G_lower := hlow
    E_small := tendsto_V_zero hE0 }⟩

/-- **`Σ₀` at Virasoro for the extremal measures from the tail bounds alone.** -/
theorem virasoro_sigmaZero_of_tailBounds (h : DesignTailBounds) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS :=
  virasoro_sigmaZero (sameSiteFamily_designClass h).some

/-- **Non-vacuity of `SameSiteTailBounds`**: it holds for `G_k ≡ k + 1` (the lower bound is
`F(u) = Ai(u)²/(u - a_1)² ≤ sup |Ai'|²` on compacta, by the mean value theorem). -/
theorem sameSiteTailBounds_nonvacuous : SameSiteTailBounds (fun k _ => (k : ℝ) + 1) := by
  refine ⟨⟨0, le_rfl, fun k u _ => by simp⟩, fun K hK => ?_⟩
  obtain ⟨m, hm⟩ := hK.bddBelow
  set a : ℝ := airyNode 0 with ha
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := min m a) (b := a)).exists_bound_of_continuousOn
    continuous_airyAi'.continuousOn
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (L ^ 2 / 2)
  refine ⟨k₀, fun k hk u hu hua => ?_⟩
  have hmu : min m a ≤ u := (min_le_left _ _).trans (hm hu)
  have hmem : u ∈ Icc (min m a) a := ⟨hmu, hua.le⟩
  have hmem2 : a ∈ Icc (min m a) a := ⟨min_le_right _ _, le_rfl⟩
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := airyAi) (f' := airyAi')
    (s := Icc (min m a) a) (C := L) (fun x _ => (hasDerivAt_airyAi x).hasDerivWithinAt)
    (fun x hx => hL x hx) (convex_Icc _ _) hmem2 hmem
  have hza : airyAi a = 0 := by rw [ha, airyNode_zero]; exact airyAi_airyZero 1
  rw [hza, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hb
  have hne : u - a ≠ 0 := sub_ne_zero.mpr hua.ne
  have hsq : (airyAi u) ^ 2 ≤ L ^ 2 * (u - a) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg (airyAi u), neg_abs_le (airyAi u)] : -(L * |u - a|) ≤ airyAi u)
      (by linarith [le_abs_self (airyAi u)] : airyAi u ≤ L * |u - a|)
    simpa [mul_pow, sq_abs] using this
  have hpos : 0 < (u - a) ^ 2 := by positivity
  have h1 : (1 / 2) * (airyAi u) ^ 2 / (u - a) ^ 2 ≤ L ^ 2 / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hsq]
  have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sameSiteFamily_designClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sameSiteFamily_designClass

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigmaZero_of_tailBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigmaZero_of_tailBounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sameSiteTailBounds_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sameSiteTailBounds_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.continuous_Gd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_Gd

end FormalResearch.ModularBootstrap.Upper.Assembly

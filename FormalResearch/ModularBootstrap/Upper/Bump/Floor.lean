module

public import FormalResearch.ModularBootstrap.Upper.Bump.Nearest

/-!
# The boosted floor `h^{(p)}/Lev ≥ (0.700 - o(1))(16/5)(η_big² + 1/4)` (`fw:e3.4a`, `fw:e3.5`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Reference comparison in the macroscopic region" and
"The improved lower floor for a boosted nearest pair".

* `exists_cut`, `blockAbove_of_fixed`: a cut `N` above the whole block exists, and a fixed base cut `N₀` lies below
  the block for `c'` large;
* `bump_floor` (`fw:e3.5`, for *any* base comb): if the base comb satisfies a floor
  `ν Lev ≤ sech²(πx/2) · base(x)` at `x ∈ [ξ_* + 3 r_p, X_p - 1]` then the bumped comb satisfies
  `(1 - τ)(η_big² + 1/4)/(η₀² + 1/4) · ν Lev ≤ sech²(πx/2) · bumped(x)`.  The base comb is arbitrary (a fixed
  design, the ramped comb, ...) and the reference level `Lev` is that of `levComb`;
* `reference_comparison` (`fw:e3.4a`): for a compact family, `|log (|B_D|/|B_ref|)| ≤ C λ` for `x ≥ ξ_* + r/2`
  (this is `lemma_P_b` with `x - ξ_* ≥ r/2`);
* `bump_floor_family` (`fw:e3.5`): the boosted floor for a compact family of finite modifications at `η₀ = 1/4`:
  `(1 - τ)(16/5)(η_big² + 1/4) · ν Lev ≤ sech²(πx/2) · bumped(x)` on `[ξ_* + 3 r_p, X_p - 1]`, with the explicit
  `ν = 0.7 · 0.998² · 0.999` that `Positivity.proposition_II_floor` provides in place of `0.700 - o(1)`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Holes
open scoped Classical

/-! ### 1. The cuts -/

/-- A cut above the whole block exists for every `c' > 0`. -/
theorem exists_cut (d : BumpData) {c' : ℝ} (hc' : 0 < c') :
    ∃ N : ℕ, ∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ d.X → k ≤ N := by
  obtain ⟨n, hn1, hcell⟩ := exists_inCell hc' (M := 1) le_rfl (x := max d.X (chiQuantile c' ((1 : ℕ) : ℝ)))
    (by exact_mod_cast le_max_right _ _)
  refine ⟨n, fun k hk hkX => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ chiQuantile c' (k : ℝ) :=
    chi_mono_nat hc' (by omega) (by omega)
  have h2 := hcell.2
  have h3 : d.X ≤ max d.X (chiQuantile c' ((1 : ℕ) : ℝ)) := le_max_left _ _
  linarith

/-- A fixed base cut lies below the block for `c'` large. -/
theorem blockAbove_of_fixed (d : BumpData) (N₀ : ℕ) :
    ∀ᶠ c' in atTop, d.BlockAbove c' N₀ := by
  have hlam : ∀ᶠ c' in atTop, lambdaComb c' * phiQuantile ((N₀ : ℝ) + 2) < d.r := by
    have := tendsto_lambdaComb_atTop.mul_const (phiQuantile ((N₀ : ℝ) + 2))
    simp only [zero_mul] at this
    exact this.eventually_lt_const d.r_pos
  filter_upwards [hlam, eventually_gt_atTop 0] with c' hl hc' k hk hb
  have hlo := hb.1
  unfold BumpData.lo at hlo
  have hr := d.r_pos
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have : chiQuantile c' ((0 : ℕ) : ℝ) = xiStar := by
      unfold chiQuantile
      have hn : ¬ (0 < c' ∧ 1 / 4 ≤ ((0 : ℕ) : ℝ)) := fun h => by
        have := h.2
        norm_num at this
      simp only [hn, dite_false]
    rw [this] at hlo
    linarith
  · have := (refSite_bounds hc' (k := k) (N := N₀) hk1 hk).2
    linarith

/-! ### 2. The floor for any base comb -/

/-- **`fw:e3.5` for any base comb.**  A floor of the base comb against the reference level `Lev` at `x` with
`ξ_* + 3 r_p ≤ x ≤ X_p - 1` becomes, after the bump, the floor multiplied by `(1 - τ)(η_big² + 1/4)/(η₀² + 1/4)`. -/
theorem bump_floor (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ c' in atTop, ∀ (f N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ) (x ν : ℝ), f ≤ N₀ → N₀ ≤ N →
      d.BlockAbove c' N₀ → (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ d.X → k ≤ N) →
      xiStar + 3 * d.r ≤ x → x ≤ d.X - 1 → 0 < ν →
      ν * levComb c' f x ≤ 1 / Real.cosh (π * x / 2) ^ 2 * combReal c' f N₀ η₀ σ₀ ε₀ x →
      ∃ rb : ℝ, bumpedComb d c' f N₀ N η₀ σ₀ ε₀ (x : ℂ) = (rb : ℂ) ∧
        (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * (ν * levComb c' f x) ≤
          1 / Real.cosh (π * x / 2) ^ 2 * rb := by
  filter_upwards [bumped_value d hη₀ hη₀1, bumpFactor_floor d hη₀ hη₀1 hτ,
    bumpFactor_one_le d hη₀ hη₀1]
    with c' hv hfl h1 f N₀ N σ₀ ε₀ x ν hfN hN hab hcut hx1 hx2 hν hbase
  obtain ⟨_, hb⟩ := hv f N₀ N σ₀ ε₀ x hfN hN
  refine ⟨_, hb, ?_⟩
  set R := bumpFactor d c' η₀ N₀ N x with hR
  set r0 := combReal c' f N₀ η₀ σ₀ ε₀ x with hr0
  set s := 1 / Real.cosh (π * x / 2) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hLev := levComb_pos c' f x
  have hr0pos : 0 < r0 := by
    by_contra hle
    push Not at hle
    have : s * r0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hspos.le hle
    have : 0 < ν * levComb c' f x := mul_pos hν hLev
    linarith
  have hRfl := hfl N₀ N x hab hcut hx1 hx2
  have hR1 := h1 N₀ N x
  rcases lt_or_ge ((1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4))) 0 with hneg | hg
  · have : 0 ≤ s * (R * r0) := by positivity
    have h2 : (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * (ν * levComb c' f x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (mul_pos hν hLev).le
    linarith
  · calc (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * (ν * levComb c' f x)
        ≤ (1 - τ) * ((d.H ^ 2 + 1 / 4) / (η₀ ^ 2 + 1 / 4)) * (s * r0) :=
          mul_le_mul_of_nonneg_left hbase hg
      _ ≤ R * (s * r0) := mul_le_mul_of_nonneg_right hRfl (by positivity)
      _ = s * (R * r0) := by ring

/-! ### 3. Compact families -/

/-- **`fw:e3.4a`, reference comparison in the macroscopic region.**  For a compact family of finite
modifications, uniformly in the family, `|log (|B_D(x)|/|B_ref(x)|)| ≤ C λ` for `x ≥ ξ_* + r/2`. -/
theorem reference_comparison (f N₀ : ℕ) (hf : 1 ≤ f) (hfN₀ : f ≤ N₀) (M E : ℝ) {η₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N₀ → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N₀ → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + r / 2 ≤ x →
        |Real.log (‖designComb c' f N₀ η₀ σ ε (x : ℂ)‖ / ‖refComb c' f η₀ (x : ℂ)‖)| ≤
          C * lambdaComb c' := by
  obtain ⟨C0, hC0, hP⟩ := lemma_P_b f N₀ hf hfN₀ M E
  refine ⟨2 * C0 / r, by positivity, ?_⟩
  have hlam : ∀ᶠ c' in atTop, 4 * max (phiQuantile ((N₀ : ℝ) + 2)) M * lambdaComb c' ≤ r / 2 := by
    have := tendsto_lambdaComb_atTop.const_mul (4 * max (phiQuantile ((N₀ : ℝ) + 2)) M)
    simp only [mul_zero] at this
    exact this.eventually_le_const (by positivity)
  filter_upwards [hP hη₀0 hη₀1, hlam, eventually_gt_atTop 0] with c' hc hl hc' σ ε hσ hε x hx
  have h1 := hc σ ε hσ hε x (by linarith)
  refine h1.trans ?_
  have hlam0 : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have hxr : r / 2 ≤ x - xiStar := by linarith
  have h2 : lambdaComb c' / (x - xiStar) ≤ lambdaComb c' / (r / 2) :=
    div_le_div_of_nonneg_left hlam0.le (by positivity) hxr
  calc C0 * (lambdaComb c' / (x - xiStar)) ≤ C0 * (lambdaComb c' / (r / 2)) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = 2 * C0 / r * lambdaComb c' := by field_simp

/-- **`fw:e3.5` for a compact family of finite modifications** (`η₀ = 1/4`).  For `c'` large, every member
`(σ₀, ε₀)` of the family, every cut `N ≥ N₀` above the block and every `x ∈ [ξ_* + 3 r_p, X_p - 1]`, the
bumped comb is a real number `rb` with
`(1 - τ)(16/5)(η_big² + 1/4) · ν · Lev^{(f)}(x) ≤ sech²(πx/2) · rb`, `ν = 0.7 · 0.998² · 0.999`. -/
theorem bump_floor_family (d : BumpData) (f N₀ : ℕ) (hf : 1 ≤ f) (hfN₀ : f ≤ N₀) (M E : ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ c' in atTop, ∀ (N : ℕ) (σ₀ ε₀ : ℕ → ℝ), N₀ ≤ N →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ d.X → k ≤ N) →
      (∀ k, f ≤ k → k ≤ N₀ → |σ₀ k| ≤ M) →
      (∀ k, f < k → k ≤ N₀ → 0 ≤ ε₀ k ∧ ε₀ k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + 3 * d.r ≤ x → x ≤ d.X - 1 →
        ∃ rb : ℝ, bumpedComb d c' f N₀ N (1 / 4) σ₀ ε₀ (x : ℂ) = (rb : ℂ) ∧
          (1 - τ) * ((16 / 5) * (d.H ^ 2 + 1 / 4)) *
              ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * levComb c' f x) ≤
            1 / Real.cosh (π * x / 2) ^ 2 * rb := by
  have hpow : ∀ᶠ c' : ℝ in atTop, c' ^ (-(2 / 5 : ℝ)) ≤ 3 * d.r := by
    have := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)
    exact this.eventually_le_const (by have := d.r_pos; positivity)
  filter_upwards [proposition_II_floor f N₀ hf hfN₀ M E, bump_floor d (η₀ := 1 / 4) (by norm_num)
    le_rfl hτ, blockAbove_of_fixed d N₀, bumped_value d (η₀ := 1 / 4) (by norm_num) le_rfl, hpow]
    with c' hII hfloor hab hv hp N σ₀ ε₀ hN hcut hσ hε x hx1 hx2
  have hx : xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x := by linarith
  obtain ⟨_, R, r, hR, hr, hD, hfl, hlog⟩ := hII σ₀ ε₀ hσ hε x hx
  obtain ⟨hbase, _⟩ := hv f N₀ N σ₀ ε₀ x hfN₀ hN
  have hrr : r = combReal c' f N₀ (1 / 4) σ₀ ε₀ x := by
    have := hD.symm.trans hbase
    exact_mod_cast this
  have hratio : (999 / 1000 : ℝ) ≤ r / R := by
    have hrR : 0 < r / R := div_pos hr hR
    have hl : -(1 / 1000 : ℝ) ≤ Real.log (r / R) := (abs_le.mp hlog).1
    have h1 : Real.exp (-(1 / 1000 : ℝ)) ≤ r / R := by
      calc Real.exp (-(1 / 1000 : ℝ)) ≤ Real.exp (Real.log (r / R)) := Real.exp_le_exp.mpr hl
        _ = r / R := Real.exp_log hrR
    have h2 := Real.add_one_le_exp (-(1 / 1000 : ℝ))
    have h3 : (999 / 1000 : ℝ) ≤ Real.exp (-(1 / 1000 : ℝ)) := by linarith only [h2]
    exact h3.trans h1
  have hr' : (999 / 1000 : ℝ) * R ≤ r := (le_div_iff₀ hR).mp hratio
  have hs : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hbase_fl : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * levComb c' f x ≤
      1 / Real.cosh (π * x / 2) ^ 2 * combReal c' f N₀ (1 / 4) σ₀ ε₀ x := by
    rw [← hrr]
    calc (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * levComb c' f x
        = (999 / 1000 : ℝ) * ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * levComb c' f x) := by ring
      _ ≤ (999 / 1000 : ℝ) * (1 / Real.cosh (π * x / 2) ^ 2 * R) :=
          mul_le_mul_of_nonneg_left hfl (by norm_num)
      _ = 1 / Real.cosh (π * x / 2) ^ 2 * ((999 / 1000 : ℝ) * R) := by ring
      _ ≤ 1 / Real.cosh (π * x / 2) ^ 2 * r := mul_le_mul_of_nonneg_left hr' hs.le
  obtain ⟨rb, hrb, hfin⟩ := hfloor f N₀ N σ₀ ε₀ x _ hfN₀ hN hab hcut hx1 hx2 (by norm_num) hbase_fl
  refine ⟨rb, hrb, ?_⟩
  have hg : (d.H ^ 2 + 1 / 4) / ((1 / 4 : ℝ) ^ 2 + 1 / 4) = (16 / 5) * (d.H ^ 2 + 1 / 4) := by
    field_simp; norm_num
  rw [hg] at hfin
  exact hfin

/-! ### 4. The bump lemma at comb level and non-vacuity -/

/-- **The quantitative bump lemma at comb level** (`fw:e3.3`).  For `0 < η₀ ≤ 1/4`, `c'` large, every finite
modification `(f, N₀, σ₀, ε₀)`, every cut `N ≥ N₀` and every real `x ≥ 0`: `B_D(x)` and the bumped comb are real,
the bumped comb equals `R_bump(x)` times the base, `1 ≤ R_bump ≤ C_p`, and `R_bump ≤ 1 + C/c'` for
`x ≤ ξ_* + r_p`.  The constants depend only on `(r_p, X_p, η_big, η₀)`. -/
theorem bump_lemma (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (f N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ) (x : ℝ), f ≤ N₀ → N₀ ≤ N → 0 ≤ x →
      designComb c' f N₀ η₀ σ₀ ε₀ (x : ℂ) = ((combReal c' f N₀ η₀ σ₀ ε₀ x : ℝ) : ℂ) ∧
      bumpedComb d c' f N₀ N η₀ σ₀ ε₀ (x : ℂ) =
        ((bumpFactor d c' η₀ N₀ N x * combReal c' f N₀ η₀ σ₀ ε₀ x : ℝ) : ℂ) ∧
      1 ≤ bumpFactor d c' η₀ N₀ N x ∧ bumpFactor d c' η₀ N₀ N x ≤ bumpC d η₀ ∧
      (x ≤ xiStar + d.r → bumpFactor d c' η₀ N₀ N x ≤ 1 + bumpC' d η₀ / c') := by
  filter_upwards [bumped_value d hη₀ hη₀1, bumpFactor_one_le d hη₀ hη₀1, bumpFactor_le d hη₀ hη₀1,
    bumpFactor_le_one_add d hη₀ hη₀1] with c' hv h1 h2 h3 f N₀ N σ₀ ε₀ x hfN hN hx
  obtain ⟨hb, hbump⟩ := hv f N₀ N σ₀ ε₀ x hfN hN
  exact ⟨hb, hbump, h1 N₀ N x, h2 N₀ N x hx, fun hxr => h3 N₀ N x hx hxr⟩

/-- Non-vacuity of the bump data: an instance of `BumpData`, a cut above its block for every `c' > 0`, a fixed
base cut below the block for `c'` large, and (for the reference data) `R_bump` is defined and `≥ 1` at `x = 0`. -/
theorem bump_nonvacuous :
    ∃ d : BumpData, d.r = 1 ∧ d.H = 1 / 4 ∧ (∀ c' : ℝ, 0 < c' → ∃ N : ℕ, ∀ k : ℕ, 1 ≤ k →
      chiQuantile c' (k : ℝ) ≤ d.X → k ≤ N) ∧ (∀ N₀ : ℕ, ∀ᶠ c' in atTop, d.BlockAbove c' N₀) ∧
      ∀ᶠ c' in atTop, ∀ N₀ N : ℕ, 1 ≤ bumpFactor d c' (1 / 4) N₀ N 0 := by
  have h : xiStar + 4 * 1 + 2 < xiStar + 7 := by linarith
  refine ⟨⟨1, xiStar + 7, 1 / 4, one_pos, h, le_rfl⟩, rfl, rfl, fun c' hc' => exists_cut _ hc',
    fun N₀ => blockAbove_of_fixed _ N₀, ?_⟩
  filter_upwards [bumpFactor_one_le ⟨1, xiStar + 7, 1 / 4, one_pos, h, le_rfl⟩ (η₀ := 1 / 4)
    (by norm_num) le_rfl] with c' hc N₀ N using hc N₀ N 0

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.exists_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_cut

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.blockAbove_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blockAbove_of_fixed

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bump_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_floor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.reference_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_comparison

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bump_floor_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_floor_family

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bump_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_lemma

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bump_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Bump

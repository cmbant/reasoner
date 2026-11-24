module

public import FormalResearch.ModularBootstrap.Upper.Design.PerturbPhi
public import FormalResearch.ModularBootstrap.Upper.Positivity.DesignReal
public import FormalResearch.ModularBootstrap.Upper.Window.LobeAndTail

/-!
# The macroscopic detuning bump: data, block and bumped comb (`fw:e2.2`, `fw:e2.3`, the extra modification)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Fixed designs plus a fixed macroscopic detuning bump".

* `BumpData`: the fixed data `(r_p, X_p, η_big)` of the bump (`r_p > 0`, `X_p > ξ_* + 4 r_p + 2`, `η_big ≥ 1/4`);
  they depend only on the order `p`, never on `c'`, the base comb or the cut.
* `BumpData.InBlock`: the block of quantile indices `ξ_* + 2 r_p ≤ χ_k ≤ X_p` that are raised from the
  reference height fraction `η₀` to `η_big`.
* `bumpSigma`, `bumpEps`, `bumpedComb`: the *bumped comb*.  It is the `designComb` with cut `N`
  that agrees with a base finite modification `(f, N₀, σ₀, ε₀)` on the indices `k ≤ N₀`, has the reference
  sites `χ_k` for `N₀ < k ≤ N`, and the heights `η_big ℓ_k` in the block and `η₀ ℓ_k` elsewhere.  The base
  comb is arbitrary (a fixed design, the ramped comb, ...); only `N₀ < k` for every block index `k` is used
  (`BlockAbove`).
* `block_gap_bounds`, `block_spacing`, `block_sum_le`, `block_card_le`: on the block the quantile gaps satisfy
  `ℓ_k ≍ 1/c'` (from `chiDeriv_le_siteGap_prev`, `siteGap_le_chiDeriv` and the monotonicity of `ρ_U`), the
  sites are `δ`-separated with `δ ≍ 1/c'`, the Lorentzian sum over the block is `O(1)` uniformly in `x`, and
  the block has at most `O(c')` indices.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

/-- The fixed data of the macroscopic bump: `r_p`, `X_p` and `η_big(p)`. -/
structure BumpData where
  /-- `r_p`: the bump starts at `ξ_* + 2 r_p`. -/
  r : ℝ
  /-- `X_p`: the bump ends at `X_p`. -/
  X : ℝ
  /-- `η_big(p)`: the raised height fraction. -/
  H : ℝ
  r_pos : 0 < r
  X_gt : xiStar + 4 * r + 2 < X
  H_ge : 1 / 4 ≤ H

namespace BumpData

variable (d : BumpData)

/-- The left end `ξ_* + 2 r_p` of the block. -/
noncomputable def lo : ℝ := xiStar + 2 * d.r

lemma xiStar_lt_lo : xiStar < d.lo := by
  unfold lo; linarith [d.r_pos]

lemma lo_lt_X : d.lo < d.X := by
  unfold lo; linarith [d.X_gt, d.r_pos]

lemma H_pos : 0 < d.H := lt_of_lt_of_le (by norm_num) d.H_ge

/-- The block of quantile indices `ξ_* + 2 r_p ≤ χ_k ≤ X_p`. -/
def InBlock (c' : ℝ) (k : ℕ) : Prop :=
  d.lo ≤ chiQuantile c' (k : ℝ) ∧ chiQuantile c' (k : ℝ) ≤ d.X

open Classical in
/-- The indices of the block among the pairs `N₀ < k ≤ N`. -/
noncomputable def blockSet (c' : ℝ) (N₀ N : ℕ) : Finset ℕ :=
  (Finset.Ioc N₀ N).filter (d.InBlock c')

/-- The density at the left end and at the right end of the block (`ρ_U(ξ_* + 2 r_p)`, `ρ_U(X_p + 1)`). -/
noncomputable def rhoLo : ℝ := rhoU d.lo

noncomputable def rhoHi : ℝ := rhoU (d.X + 1)

lemma rhoLo_pos : 0 < d.rhoLo := rhoU_pos d.xiStar_lt_lo

lemma rhoLo_le_rhoHi : d.rhoLo ≤ d.rhoHi :=
  rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.mpr d.xiStar_lt_lo.le)
    (Set.mem_Ici.mpr (d.xiStar_lt_lo.le.trans (by linarith [d.lo_lt_X]))) (by linarith [d.lo_lt_X])

lemma rhoHi_pos : 0 < d.rhoHi := lt_of_lt_of_le d.rhoLo_pos d.rhoLo_le_rhoHi

/-- The block is *above* the base cut `N₀`: no index `k ≤ N₀` lies in the block. -/
def BlockAbove (c' : ℝ) (N₀ : ℕ) : Prop := ∀ k : ℕ, k ≤ N₀ → ¬ d.InBlock c' k

end BumpData

/-! ### The bumped comb -/

open Classical in
/-- The sites of the bumped comb: those of the base for `k ≤ N₀`, the reference sites `χ_k` beyond. -/
noncomputable def bumpSigma (c' : ℝ) (N₀ : ℕ) (σ₀ : ℕ → ℝ) : ℕ → ℝ := fun k =>
  if k ≤ N₀ then σ₀ k else (chiQuantile c' (k : ℝ) - xiStar) / lambdaComb c'

open Classical in
/-- The heights of the bumped comb: those of the base for `k ≤ N₀`; beyond, `η_big ℓ_k` in the block and
`η₀ ℓ_k` elsewhere. -/
noncomputable def bumpEps (d : BumpData) (c' : ℝ) (N₀ : ℕ) (η₀ : ℝ) (ε₀ : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k ≤ N₀ then ε₀ k else (if d.InBlock c' k then d.H else η₀) * siteGap c' k

/-- The bumped comb: the `designComb` with cut `N` and the data `bumpSigma`, `bumpEps`. -/
noncomputable def bumpedComb (d : BumpData) (c' : ℝ) (f N₀ N : ℕ) (η₀ : ℝ) (σ₀ ε₀ : ℕ → ℝ) :
    ℂ → ℂ :=
  designComb c' f N η₀ (bumpSigma c' N₀ σ₀) (bumpEps d c' N₀ η₀ ε₀)

lemma designSite_bumpSigma_of_le {c' : ℝ} {N₀ k : ℕ} {σ₀ : ℕ → ℝ} (hk : k ≤ N₀) :
    designSite c' (bumpSigma c' N₀ σ₀) k = designSite c' σ₀ k := by
  unfold designSite bumpSigma
  simp [hk]

/-- Beyond the base cut the sites of the bumped comb are the reference sites. -/
lemma designSite_bumpSigma_of_gt {c' : ℝ} (hc' : 0 < c') {N₀ k : ℕ} {σ₀ : ℕ → ℝ} (hk : N₀ < k) :
    designSite c' (bumpSigma c' N₀ σ₀) k = chiQuantile c' (k : ℝ) := by
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  unfold designSite bumpSigma
  simp only [not_le.mpr hk, ite_false]
  field_simp
  ring

lemma bumpEps_of_le {d : BumpData} {c' : ℝ} {N₀ k : ℕ} {η₀ : ℝ} {ε₀ : ℕ → ℝ} (hk : k ≤ N₀) :
    bumpEps d c' N₀ η₀ ε₀ k = ε₀ k := by
  unfold bumpEps
  simp [hk]

lemma bumpEps_of_gt_block {d : BumpData} {c' : ℝ} {N₀ k : ℕ} {η₀ : ℝ} {ε₀ : ℕ → ℝ} (hk : N₀ < k)
    (hb : d.InBlock c' k) : bumpEps d c' N₀ η₀ ε₀ k = d.H * siteGap c' k := by
  unfold bumpEps
  simp [not_le.mpr hk, hb]

lemma bumpEps_of_gt_not_block {d : BumpData} {c' : ℝ} {N₀ k : ℕ} {η₀ : ℝ} {ε₀ : ℕ → ℝ}
    (hk : N₀ < k) (hb : ¬ d.InBlock c' k) :
    bumpEps d c' N₀ η₀ ε₀ k = η₀ * siteGap c' k := by
  unfold bumpEps
  simp [not_le.mpr hk, hb]

end FormalResearch.ModularBootstrap.Upper.Bump

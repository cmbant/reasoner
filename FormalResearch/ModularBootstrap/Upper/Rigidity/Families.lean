module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Core

/-!
# The design families used by `Σ₀` and `Σ` (window algebra, not formalised)

The proofs of `sr:Sigma0`, `sr:Sigma` use, besides Property `sr:P`, three explicit families of
windows (`spectral_rigidity.tex`, §2 and §4).  Their *algebra* (sign law, `E_0 → 0`, `R_1 ≥ 1/2`,
`Q ≥ 1/2` on compacta) is a property of the explicit Airy product `W_𝔇`; for the `f = 1`
designs without displacement it is `lemma_V_hasSum`, `lemma_V_eval_one`, `lemma_V_eval_succ`,
`lemma_E` for `designWindowW` (`Upper/Window`), but the general-`f` / displaced-site versions and
the lower bound `Q ≥ 1/2` are not in Lean.  They are therefore stated here as explicit structures
(named hypotheses), each field being the exact statement used in the TeX proof.  Sites are
0-indexed: site `i` is the zero `a_{i+1}`, `airyNode i`.

* `SameSiteFamily 𝒟` (Σ₀, Σ steps 2, 3, 5): designs `f = 1`, first site at `a₁ - d`, all with the same
  sites (same `Q`, i.e. the same `G_k = F Q_k`), `W_{k,d} = G_k(u) (a₁ - d - u)`, `k → ∞` the ideal
  limit `N → ∞`, `η_* → 0`.
* `DisplacedFamily 𝒟` (Σ step 5, `n ≥ 2`): one displaced site `n`, all `Π_m ≥ 0`.
* `OmittedFamily 𝒟` (Σ step 6): `f - 1` omitted sites, first kept site at `a_f` (`d = 0`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- `d₀ = min(|a₁|, |a₁ - a₂|)/2`, the admissible range of the first-site shift in Property `sr:P`. -/
noncomputable def designRadius : ℝ := min |airyZero 1| |airyZero 1 - airyZero 2| / 2

lemma designRadius_pos : 0 < designRadius := by
  unfold designRadius
  have h1 : 0 < |airyZero 1| := abs_pos.mpr (airyZero_neg 1).ne
  have h2 : 0 < |airyZero 1 - airyZero 2| :=
    abs_pos.mpr (sub_ne_zero.mpr (airyZero_strictAnti le_rfl).ne')
  exact div_pos (lt_min h1 h2) two_pos

/-- **Named hypothesis (window algebra for the same-site `f = 1` designs).**  See the module
docstring.  `G k` is `F · Q_k` (`F = Ai²/(u - a₁)²`), `win k d` the window of the `k`-th design with
first site `a₁ - d`, `W_{k,d}(u) = G_k(u)(a₁ - d - u)`.  Fields: membership in the class `𝒟`
(`|d| < d₀`); positivity of `G_k` up to `a₁ + d₀` (`η_* > 0`); `R_1 = G_k(a₁)/Ai'(a₁)² ≥ 1/2`
(`ut:E`(iv)); the design-independent Lipschitz bound `G_k(u) ≤ G_k(a₁)(1 + C|u - a₁|)` near `a₁`
(`sr:Sigma0` proof, bound on `|W_A|`); `Q ≥ 1/2` on compacta below `a₁` for `k` large
(`sr:Sigma` Step 3); `E_0 = V_{k,0} → 0` (`ut:E`(iii)). -/
structure SameSiteFamily (𝒟 : Set Window) where
  G : ℕ → ℝ → ℝ
  win : ℕ → ℝ → Window
  mem : ∀ k d, |d| < designRadius → win k d ∈ 𝒟
  W_eq : ∀ k d u, (win k d).W u = G k u * (airyNode 0 - d - u)
  uF_eq : ∀ k d, (win k d).uF = airyNode 0 - d
  G_pos : ∀ k u, u ≤ airyNode 0 + designRadius → 0 < G k u
  G_cont : ∀ k, Continuous (G k)
  R_ge : ∀ k, (1 / 2) * (airyAi' (airyNode 0)) ^ 2 ≤ G k (airyNode 0)
  G_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ k u, |u - airyNode 0| ≤ 1 →
    G k u ≤ G k (airyNode 0) * (1 + C * |u - airyNode 0|)
  G_lower : ∀ K : Set ℝ, IsCompact K → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ u ∈ K, u < airyNode 0 →
    (1 / 2) * (airyAi u) ^ 2 / (u - airyNode 0) ^ 2 ≤ G k u
  E_small : Tendsto (fun k => (win k 0).V) atTop (𝓝 0)

/-- **Named hypothesis (window algebra for the displaced-site designs, Σ step 5).**  For each site
`n ≥ 1` (0-indexed, i.e. `a_{n+1}`, `n + 1 ≥ 2`): windows `win n k ∈ 𝒟` with all `Π_m ≥ 0`,
`Π_n ≥ ω > 0` (`Π_n ≈ e² ω_n`) and `Σ_{m ≠ 1, n + 1} Π_m → 0` as the design tends to the ideal. -/
structure DisplacedFamily (𝒟 : Set Window) where
  win : ℕ → ℕ → Window
  mem : ∀ n k, 1 ≤ n → win n k ∈ 𝒟
  pi_nonneg : ∀ n k i, 1 ≤ n → 0 ≤ (win n k).pi i
  pi_lower : ∀ n, 1 ≤ n → ∃ ω : ℝ, 0 < ω ∧ ∀ k, ω ≤ (win n k).pi n
  rest_small : ∀ n, 1 ≤ n →
    Tendsto (fun k => ∑' i, if i = 0 ∨ i = n then 0 else (win n k).pi i) atTop (𝓝 0)

/-- **Named hypothesis (window algebra for the omitted-site designs, Σ step 6).**  For `f ≥ 1`
(0-indexed first kept site `a_{f+1}`, sites `i < f` omitted, `d = 0`): windows `win f k ∈ 𝒟` with the
strict sign pattern `Π_i < 0` (`i < f`), `Π_f = 0`, `Π_i ≥ 0` (`i > f`), `|Π_i| ≥ ω_i > 0` for
`i < f` eventually, and `Σ_{i > f} Π_i → 0`. -/
structure OmittedFamily (𝒟 : Set Window) where
  win : ℕ → ℕ → Window
  mem : ∀ f k, 1 ≤ f → win f k ∈ 𝒟
  pi_neg : ∀ f k i, 1 ≤ f → i < f → (win f k).pi i < 0
  pi_first : ∀ f k, 1 ≤ f → (win f k).pi f = 0
  pi_nonneg : ∀ f k i, 1 ≤ f → f < i → 0 ≤ (win f k).pi i
  pi_lower : ∀ f i, 1 ≤ f → i < f → ∃ ω : ℝ, 0 < ω ∧ ∀ᶠ k in atTop, ω ≤ -(win f k).pi i
  tail_small : ∀ f, 1 ≤ f →
    Tendsto (fun k => ∑' i, if f < i then (win f k).pi i else 0) atTop (𝓝 0)

namespace SameSiteFamily

variable {𝒟 : Set Window} (F : SameSiteFamily 𝒟)

/-- `R̃_k = R_1 = G_k(a₁)/Ai'(a₁)²`, so that `Π_1 = -d R̃_k`. -/
noncomputable def Rt (k : ℕ) : ℝ := F.G k (airyNode 0) * airyNodeWeight 0

lemma G_nonneg (k : ℕ) {u : ℝ} (hu : u ≤ airyNode 0 + designRadius) : 0 ≤ F.G k u :=
  (F.G_pos k u hu).le

lemma Rt_ge (k : ℕ) : 1 / 2 ≤ F.Rt k := by
  unfold Rt airyNodeWeight
  have h := F.R_ge k
  have hne : (airyAi' (airyNode 0)) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyNode_ne 0)
  have hpos : 0 < (airyAi' (airyNode 0)) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
  rw [mul_one_div, le_div_iff₀ hpos]
  linarith

lemma Rt_pos (k : ℕ) : 0 < F.Rt k := lt_of_lt_of_le (by norm_num) (F.Rt_ge k)

lemma pi_win (k : ℕ) (d : ℝ) (i : ℕ) :
    (F.win k d).pi i = F.G k (airyNode i) * (airyNode 0 - d - airyNode i) * airyNodeWeight i := by
  unfold Window.pi; rw [F.W_eq]

lemma pi_win_zero (k : ℕ) (d : ℝ) : (F.win k d).pi 0 = -d * F.Rt k := by
  rw [pi_win]; unfold Rt; ring

lemma V_eq (k : ℕ) (d : ℝ) :
    (F.win k d).V = -d * F.Rt k + ∑' i, (F.win k d).pi (i + 1) := by
  rw [← (F.win k d).tsum_pi, (F.win k d).summable_pi.tsum_eq_zero_add, pi_win_zero]

lemma summable_pi_succ (k : ℕ) (d : ℝ) : Summable fun i => (F.win k d).pi (i + 1) :=
  (summable_nat_add_iff 1).2 (F.win k d).summable_pi

lemma V_zero_eq (k : ℕ) : (F.win k 0).V = ∑' i, (F.win k 0).pi (i + 1) := by
  rw [V_eq, neg_zero, zero_mul, zero_add]

lemma airyNode_succ_le (i : ℕ) : airyNode (i + 1) ≤ airyNode 1 :=
  airyNode_strictAnti.antitone (Nat.le_add_left 1 i)

/-- The gap `a₁ - a₂`. -/
noncomputable def gap1 : ℝ := airyNode 0 - airyNode 1

lemma gap1_pos : 0 < gap1 := sub_pos.2 (airyNode_strictAnti (Nat.zero_lt_one))

lemma gap1_le (i : ℕ) : gap1 ≤ airyNode 0 - airyNode (i + 1) := by
  unfold gap1; linarith [airyNode_succ_le i]

lemma G_nonneg_node (k i : ℕ) : 0 ≤ F.G k (airyNode i) :=
  F.G_nonneg k ((airyNode_le_airyNode_zero i).trans (by rw [← airyNode_zero]; linarith [designRadius_pos]))

/-- `V_{k,d} ≤ -d R̃_k + E_k` for `d ≥ 0` (`sr:Sigma0` proof: `V_A ≤ -dR_1 + E_0`). -/
lemma V_le_of_nonneg (k : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    (F.win k d).V ≤ -d * F.Rt k + (F.win k 0).V := by
  rw [V_eq, V_zero_eq]
  have : ∑' i, (F.win k d).pi (i + 1) ≤ ∑' i, (F.win k 0).pi (i + 1) := by
    refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_pi_succ k d) (F.summable_pi_succ k 0)
    rw [pi_win, pi_win]
    have h1 := F.G_nonneg_node k (i + 1)
    have h2 := (airyNodeWeight_pos (i + 1)).le
    have : (airyNode 0 - d - airyNode (i + 1)) ≤ (airyNode 0 - 0 - airyNode (i + 1)) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h1) h2
  linarith

/-- `V_{k,-κ} ≤ κ R̃_k + (1 + κ/g) E_k` for `κ ≥ 0` (`sr:Sigma`, Step 2, `V_𝔅`). -/
lemma V_le_of_neg (k : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    (F.win k (-κ)).V ≤ κ * F.Rt k + (1 + κ / gap1) * (F.win k 0).V := by
  rw [V_eq, V_zero_eq]
  have hs : Summable fun i => (1 + κ / gap1) * (F.win k 0).pi (i + 1) :=
    (F.summable_pi_succ k 0).mul_left _
  have : ∑' i, (F.win k (-κ)).pi (i + 1) ≤ ∑' i, (1 + κ / gap1) * (F.win k 0).pi (i + 1) := by
    refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_pi_succ k (-κ)) hs
    rw [pi_win, pi_win]
    have h1 := F.G_nonneg_node k (i + 1)
    have h2 := (airyNodeWeight_pos (i + 1)).le
    have hg := gap1_le i
    have hgp := gap1_pos
    have hκ' : κ ≤ κ / gap1 * (airyNode 0 - airyNode (i + 1)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hgp]
      exact mul_le_mul_of_nonneg_left hg hκ
    have : (airyNode 0 - -κ - airyNode (i + 1)) ≤
        (1 + κ / gap1) * (airyNode 0 - 0 - airyNode (i + 1)) := by nlinarith
    calc F.G k (airyNode (i + 1)) * (airyNode 0 - -κ - airyNode (i + 1)) * airyNodeWeight (i + 1)
        ≤ F.G k (airyNode (i + 1)) * ((1 + κ / gap1) * (airyNode 0 - 0 - airyNode (i + 1))) *
            airyNodeWeight (i + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h1) h2
      _ = (1 + κ / gap1) * (F.G k (airyNode (i + 1)) * (airyNode 0 - 0 - airyNode (i + 1)) *
            airyNodeWeight (i + 1)) := by ring
  rw [tsum_mul_left] at this
  have h' : ∑' i, (F.win k 0).pi (i + 1) = (F.win k 0).V := (V_zero_eq F k).symm
  nlinarith [this, h']

/-- For `κ ≥ 0` with `κ < d₀`, every `Π_i` of the design `win k (-κ)` is nonnegative. -/
lemma pi_win_neg_nonneg (k : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) (i : ℕ) : 0 ≤ (F.win k (-κ)).pi i := by
  rw [pi_win]
  refine mul_nonneg (mul_nonneg (F.G_nonneg_node k i) ?_) (airyNodeWeight_pos i).le
  have := airyNode_le_airyNode_zero i
  rw [← airyNode_zero] at this
  linarith

end SameSiteFamily

end FormalResearch.ModularBootstrap.Upper.Rigidity

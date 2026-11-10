module

public import FormalResearch.PPTThreeQubit.SwapSymmetric
public import FormalResearch.QIB.MatrixHelstrom

/-!
# Trace-distance bounds for the symmetrisation corollary and the kernel-penalty lift

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex` (`cor:ppt3-symmetrisation`) and
`kernel_penalty_lemma.tex` (`prop:ppt3-kernel-quant`).

* `traceDist ρ σ = ½ ‖ρ - σ‖₁` (the trace norm `QIB.tnorm` of a Hermitian matrix) and
  `bsDist ρ`, the infimum of `traceDist ρ σ` over unit-trace biseparable `σ`;
* `tnorm_real_smul`: homogeneity of the trace norm;
* `distance_lower_bound`: the witness bound `½‖ρ - σ‖₁ ≥ g / (2L + Λ)` when `-L ≤ W ≤ L + Λ`,
  `tr(Wρ) = -g`, `tr(Wσ) ≥ 0` (the `eq:ppt3-stability`-type bound used in `eq:ppt3-dist-lift`);
* `kernel_lift_distance`: `eq:ppt3-dist-lift`, for the lifted witness `W = W₀ + λ K†K`
  with `-L ≤ W₀ ≤ L` and `K†K ≤ β`;
* `kernel_quant_core`: the scalar inequality behind `eq:ppt3-lambda`
  (`α a² - 2 L a b + (λμ - L) b² ≥ 0` for `λ = (L + L²/α)/μ`);
* `bsDist_le_permAvg`: `eq:ppt3-asymmetry-upper`; `bsDist_le_swap_average`: the pinching bound of
  `eq:ppt3-pinch` in the Hermitian form `¼‖ρ - S_BC ρ S_BC‖₁`.

Not formalised: the identification of `¼‖ρ - S_BC ρ S_BC‖₁` with the non-Hermitian trace norm
`‖P₃ ρ P₁‖₁` of `eq:ppt3-pinch`, the cyclic form for a general transposition, and the cut-product
geometry (`M_c(a)`, `Ω_c(a)`) that discharges the hypotheses of `prop:ppt3-kernel-quant`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.QIB
open FormalResearch.FrameFree.Helstrom (IsEffect)
open scoped ComplexOrder

noncomputable section

/-! ### Trace norm: homogeneity -/

theorem tnorm_real_smul {n : Type*} [Fintype n] [DecidableEq n] {D : Matrix n n ℂ}
    (hD : D.IsHermitian) {c : ℝ} (hc : 0 ≤ c) : tnorm (c • D) = c * tnorm D := by
  have hcD : (c • D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hD.eq]; simp
  rcases hc.eq_or_lt with rfl | hpos
  · simp only [zero_smul, zero_mul]
    exact (tnorm_eq_zero_iff (Matrix.isHermitian_zero)).2 rfl
  obtain ⟨E, hE, hEq⟩ := exists_effect_trace_mul_eq hD
  obtain ⟨E', hE', hEq'⟩ := exists_effect_trace_mul_eq hcD
  have h1 := trace_mul_ge hcD hE
  have h2 := trace_mul_ge hD hE'
  have tr1 : (E * (c • D)).trace.re = c * (E * D).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]; simp
  have tr2 : (E' * (c • D)).trace.re = c * (E' * D).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]; simp
  have trc : (c • D).trace.re = c * D.trace.re := by rw [Matrix.trace_smul]; simp
  rw [tr1, hEq, trc] at h1
  rw [tr2, trc] at hEq'
  apply le_antisymm
  · nlinarith
  · nlinarith

/-! ### The witness distance bound -/

section Witness
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Witness distance bound** (`eq:ppt3-stability`, used in `eq:ppt3-dist-lift`).  If `-L ≤ W ≤ L + Λ`,
`tr(Wρ) = -g` and `tr(Wσ) ≥ 0` for density matrices `ρ, σ`, then `½‖ρ - σ‖₁ ≥ g / (2L + Λ)`. -/
theorem distance_lower_bound {W ρ σ : Matrix n n ℂ} {L Λ g : ℝ} (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (hLΛ : 0 < 2 * L + Λ) (hlo : (W + (L : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hhi : (((L + Λ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - W).PosSemidef)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρt : ρ.trace.re = 1) (hσt : σ.trace.re = 1)
    (hρW : (W * ρ).trace.re = -g) (hσW : 0 ≤ (W * σ).trace.re) :
    g / (2 * L + Λ) ≤ (1 / 2) * tnorm (ρ - σ) := by
  set c : ℝ := 2 * L + Λ with hc
  have hD : (ρ - σ).IsHermitian := hρ.sub hσ
  have hE : IsEffect ((1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ))) := by
    refine ⟨hlo.smul (by positivity), ?_⟩
    have : (1 : Matrix n n ℂ) - (1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ)) =
        (1 / c : ℝ) • (((L + Λ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - W) := by
      have hcpos : 0 < c := hLΛ
      have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
      have hcC' : (2 * (L : ℂ) + (Λ : ℂ)) ≠ 0 := by
        rw [hc] at hcC; push_cast at hcC; exact hcC
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
        Complex.real_smul, smul_eq_mul]
      split_ifs <;> (try rw [hc]) <;> push_cast <;> field_simp <;> ring
    rw [this]
    exact hhi.smul (by positivity)
  have h := trace_mul_ge hD hE
  have htr : (ρ - σ).trace.re = 0 := by
    rw [Matrix.trace_sub]; simp [hρt, hσt]
  have hmul : (((1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ))) * (ρ - σ)).trace.re =
      (1 / c) * ((W * ρ).trace.re - (W * σ).trace.re + L * (ρ - σ).trace.re) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub]
    simp
    ring
  rw [hmul, htr, hρW] at h
  have h' : (1 / c) * (-g - (W * σ).trace.re + L * 0) ≥ (1 / 2) * (0 - tnorm (ρ - σ)) := by
    simpa using h
  have hcpos : 0 < c := hLΛ
  have : -g / c ≥ -(tnorm (ρ - σ) / 2) := by
    have e : (1 / c) * (-g - (W * σ).trace.re + L * 0) ≤ -g / c := by
      rw [show -g / c = (1 / c) * (-g) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have : g / c ≤ tnorm (ρ - σ) / 2 := by
    have : -(g / c) ≥ -(tnorm (ρ - σ) / 2) := by simpa [neg_div] using this
    linarith
  linarith

end Witness

/-- **`eq:ppt3-dist-lift`.**  For the lifted witness `W = W₀ + λ K†K` with `-L ≤ W₀ ≤ L`, `K†K ≤ β`,
`tr(W₀ρ) = -g` for `K ρ = 0` (so `tr(Wρ) = -g`) and `tr(Wσ) ≥ 0`, one has
`½‖ρ - σ‖₁ ≥ g / (2L + λβ)`. -/
theorem kernel_lift_distance {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {W₀ ρ σ : Matrix n n ℂ} {K : Matrix m n ℂ} {L lam β g : ℝ} (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hβ : 0 ≤ β) (hLβ : 0 < 2 * L + lam * β)
    (hlo : (W₀ + (L : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hhi : ((L : ℂ) • (1 : Matrix n n ℂ) - W₀).PosSemidef)
    (hK : ((β : ℂ) • (1 : Matrix n n ℂ) - Kᴴ * K).PosSemidef)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρt : ρ.trace.re = 1) (hσt : σ.trace.re = 1)
    (hρW : ((W₀ + (lam : ℂ) • (Kᴴ * K)) * ρ).trace.re = -g)
    (hσW : 0 ≤ ((W₀ + (lam : ℂ) • (Kᴴ * K)) * σ).trace.re) :
    g / (2 * L + lam * β) ≤ (1 / 2) * tnorm (ρ - σ) := by
  have hKK : (Kᴴ * K).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self K
  refine distance_lower_bound (W := W₀ + (lam : ℂ) • (Kᴴ * K)) (Λ := lam * β) hL (by positivity)
    hLβ ?_ ?_ hρ hσ hρt hσt hρW hσW
  · have : W₀ + (lam : ℂ) • (Kᴴ * K) + (L : ℂ) • (1 : Matrix n n ℂ) =
        (W₀ + (L : ℂ) • (1 : Matrix n n ℂ)) + (lam : ℂ) • (Kᴴ * K) := by abel
    rw [this]
    exact hlo.add (hKK.smul (by exact_mod_cast hlam))
  · have : (((L + lam * β : ℝ) : ℂ)) • (1 : Matrix n n ℂ) - (W₀ + (lam : ℂ) • (Kᴴ * K)) =
        ((L : ℂ) • (1 : Matrix n n ℂ) - W₀) + (lam : ℂ) • ((β : ℂ) • (1 : Matrix n n ℂ) - Kᴴ * K) := by
      push_cast
      module
    rw [this]
    exact hhi.add (hK.smul (by exact_mod_cast hlam))

/-- **The scalar core of `eq:ppt3-lambda`.**  With `λ = (L + L²/α)/μ` the conditional quadratic form
`α‖u‖² - 2L‖u‖‖v‖ + (λμ - L)‖v‖²` is non-negative. -/
theorem kernel_quant_core {α L μ lam a b : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hlam : lam = (L + L ^ 2 / α) / μ) :
    0 ≤ α * a ^ 2 - 2 * L * a * b + (lam * μ - L) * b ^ 2 := by
  have : lam * μ - L = L ^ 2 / α := by
    rw [hlam]; field_simp; ring
  rw [this]
  have e : α * a ^ 2 - 2 * L * a * b + L ^ 2 / α * b ^ 2 = (α * a - L * b) ^ 2 / α := by
    field_simp; ring
  rw [e]
  positivity

/-! ### Distance to the biseparable states -/

/-- The trace distance `½‖ρ - σ‖₁`. -/
def traceDist (ρ σ : Matrix (Fin 8) (Fin 8) ℂ) : ℝ := (1 / 2) * tnorm (ρ - σ)

/-- The distance `D(ρ, BS)` from the set of unit-trace biseparable states. -/
def bsDist (ρ : Matrix (Fin 8) (Fin 8) ℂ) : ℝ :=
  sInf {d | ∃ σ, IsBiseparable σ ∧ σ.trace = 1 ∧ d = traceDist ρ σ}

theorem bsDist_le {ρ σ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable σ) (ht : σ.trace = 1) :
    bsDist ρ ≤ traceDist ρ σ := by
  refine csInf_le ⟨0, ?_⟩ ⟨σ, h, ht, rfl⟩
  rintro _ ⟨τ, -, -, rfl⟩
  unfold traceDist
  have := tnorm_nonneg (ρ - τ)
  positivity

/-- Biseparable unit-trace states exist (a product state). -/
theorem exists_biseparable_state : ∃ σ : Matrix (Fin 8) (Fin 8) ℂ, IsBiseparable σ ∧ σ.trace = 1 := by
  refine ⟨vecMulVec (Pi.single 0 1) (star (Pi.single 0 1 : Fin 8 → ℂ)), ⟨1, fun _ => Pi.single 0 1, ?_, ?_⟩, ?_⟩
  · intro _
    left
    refine ⟨Pi.single 0 1, Pi.single 0 1, fun i => ?_⟩
    fin_cases i <;> simp [Pi.single_apply, Fin.ext_iff]
  · simp
  · simp [Matrix.trace, vecMulVec_apply, Pi.single_apply, Fin.sum_univ_succ]

/-- A lower bound on every `traceDist ρ σ` with `σ` biseparable of unit trace bounds `bsDist`. -/
theorem le_bsDist {ρ : Matrix (Fin 8) (Fin 8) ℂ} {c : ℝ}
    (h : ∀ σ, IsBiseparable σ → σ.trace = 1 → c ≤ traceDist ρ σ) : c ≤ bsDist ρ := by
  obtain ⟨σ₀, h0, t0⟩ := exists_biseparable_state
  refine le_csInf ⟨_, σ₀, h0, t0, rfl⟩ ?_
  rintro _ ⟨σ, hσ, ht, rfl⟩
  exact h σ hσ ht

/-! ### `cor:ppt3-symmetrisation`: distance bounds -/

theorem trace_submatrix_perm {f : Fin 8 → Fin 8} (hf : Function.Bijective f)
    (M : Matrix (Fin 8) (Fin 8) ℂ) : (M.submatrix f f).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact hf.sum_comp (fun i => M i i)

theorem trace_permAvg (ρ : Matrix (Fin 8) (Fin 8) ℂ) : (permAvg ρ).trace = ρ.trace := by
  have h1 : Function.Bijective cycShift := by decide
  have h2 : Function.Bijective (cycShift ∘ cycShift) := by decide
  have h3 : Function.Bijective swapBC := by decide
  have h4 : Function.Bijective swapAC := by decide
  have h5 : Function.Bijective swapAB := by decide
  unfold permAvg
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, trace_submatrix_perm h1, trace_submatrix_perm h2, trace_submatrix_perm h3,
    trace_submatrix_perm h4, trace_submatrix_perm h5]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **`eq:ppt3-asymmetry-upper`.**  For a fully-PPT state `ρ`, `D(ρ, BS) ≤ ½‖ρ - 𝒮(ρ)‖₁`, where
`𝒮 = permAvg` is the permutation average (biseparable by `isBiseparable_permAvg`). -/
theorem bsDist_le_permAvg {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef)
    (ht : ρ.trace = 1) : bsDist ρ ≤ (1 / 2) * tnorm (ρ - permAvg ρ) := by
  have := bsDist_le (ρ := ρ) (isBiseparable_permAvg hρ hA hB hC) (by rw [trace_permAvg, ht])
  simpa [traceDist] using this

/-- **`eq:ppt3-pinch`, Hermitian form.**  For a state `ρ` that is PPT at `A|BC`,
`D(ρ, BS) ≤ ¼‖ρ - S_BC ρ S_BC‖₁`; the state `(ρ + S_BC ρ S_BC)/2` is the pinching with the triplet and
singlet projectors of `BC` (`isBiseparable_swap_average`), and `¼‖ρ - S_BC ρ S_BC‖₁ = ‖P₃ ρ P₁‖₁`
for the (non-Hermitian) trace norm of the paper, an identity that is not formalised here. -/
theorem bsDist_le_swap_average {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) (ht : ρ.trace = 1) :
    bsDist ρ ≤ (1 / 4) * tnorm (ρ - ρ.submatrix swapBC swapBC) := by
  have h3 : Function.Bijective swapBC := by decide
  have hb := isBiseparable_swap_average hρ hT
  have htr : ((1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC)).trace = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_add, trace_submatrix_perm h3, ht]
    simp only [Complex.real_smul]; push_cast; ring
  have hle := bsDist_le (ρ := ρ) hb htr
  have hD : (ρ - ρ.submatrix swapBC swapBC).IsHermitian := hρ.1.sub (hρ.1.submatrix _)
  have e : ρ - (1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC) =
      (1 / 2 : ℝ) • (ρ - ρ.submatrix swapBC swapBC) := by module
  unfold traceDist at hle
  rw [e, tnorm_real_smul hD (by norm_num)] at hle
  linarith

/-- info: 'FormalResearch.PPTThreeQubit.distance_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distance_lower_bound

/-- info: 'FormalResearch.PPTThreeQubit.kernel_lift_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_lift_distance

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_permAvg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_permAvg

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_swap_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_swap_average

end

end FormalResearch.PPTThreeQubit

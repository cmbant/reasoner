module

public import FormalResearch.Special.DiscreteAiryLimitLattice
public import FormalResearch.Special.AiryWindowMain

/-!
# Discrete-to-Airy limit, step 3: the parametrix on the lattice, perturbed coefficients

Part of the wiring module `DiscreteAiryLimit*`.  Notation: `q_k = dalQ q₀ δ k = q₀ + kδ³` (`h = δ³`),
`X_k = dalX ζ q₀ δ k = h^{-2/3} ζ(q_k)`, `ψ_k = dalPsi g ζ q₀ δ k = g(q_k) Ai(X_k)`.

* `dal_exact_defect`: M7b's uniform lattice defect and relative defect for the Langer data on the window
  `[c₀ - r, c₀ + r] ⊆ U`, in the form used by the window theorem: for the *exact* coefficients
  `a⁰_k = A(q_k - h/2)`, `c⁰_k = 2A(q_k)u(q_k)` (eikonal relation `Ch(ζζ'²) = u` of `langer_hrel`):
  `|jac a⁰ c⁰ ψ k| ≤ K δ⁶ airyWt X_k`, and `≤ K' δ⁶ ψ_k` when `X_k ≥ -1`, whenever `q_k` lies in the window.
* `dal_jac_perturb`: the row operator is Lipschitz in the coefficients.
* `dal_psi_cmp`, `dal_psi_abs_le`: `κ₁ airyWt ≤ ψ ≤ κ₂ airyWt` on `X ≥ -1` (`κ₁ = g_min/20`, `κ₂ = 6 g_max`) and
  `|ψ| ≤ 25 g_max` everywhere (`apx_airy_global`).
* `dal_airyWt_nbr`: `airyWt X' ≤ (6/5) e^{c₂√(1+B)} airyWt X` for neighbouring lattice points (`|X'-X| ≤ c₂δ`,
  `0 ≤ X ≤ B/δ²`).

Proved; constants existential.
-/

@[expose] public section

open FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The lattice site `q_k = q₀ + k δ³` (`h = δ³`). -/
def dalQ (q₀ δ : ℝ) (k : ℤ) : ℝ := q₀ + (k : ℝ) * δ ^ 3

/-- The Langer lattice variable `X_k = h^{-2/3} ζ(q_k)` (`h = δ³`). -/
noncomputable def dalX (ζ : ℝ → ℝ) (q₀ δ : ℝ) (k : ℤ) : ℝ := (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (dalQ q₀ δ k)

/-- The parametrix `ψ_k = g(q_k) Ai(X_k)`. -/
noncomputable def dalPsi (g ζ : ℝ → ℝ) (q₀ δ : ℝ) (k : ℤ) : ℝ := g (dalQ q₀ δ k) * airyAi (dalX ζ q₀ δ k)

/-- The window indices of `dal_lattice_window`, packaged (see there for the meaning of the fields). -/
structure DalLat (ζ : ℝ → ℝ) (q₀ δ c0 r c1 c2 A0 : ℝ) (J m N : ℤ) : Prop where
  J_le : J ≤ m
  m_le : m ≤ N
  win : ∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)
  qJ : c0 - A0 * δ ^ 2 / c2 ≤ dalQ q₀ δ J
  qJc : dalQ q₀ δ J ≤ c0
  qm1 : c0 ≤ dalQ q₀ δ m
  qm2 : dalQ q₀ δ m < c0 + δ ^ 3
  qN1 : dalQ q₀ δ (N + 1) ≤ c0 + r / 2
  qN : c0 + r / 4 ≤ dalQ q₀ δ N
  dist : ∀ k ∈ Finset.Icc J m, |dalQ q₀ δ k - c0| ≤ (A0 / c2 + 1) * δ ^ 2
  X0 : ∀ k ∈ Finset.Icc m (N + 1), 0 ≤ dalX ζ q₀ δ k
  Xm : dalX ζ q₀ δ m ≤ c2 * δ
  XJ : ∀ k ∈ Finset.Icc J m, -A0 ≤ dalX ζ q₀ δ k
  span : dalX ζ q₀ δ m - dalX ζ q₀ δ J ≤ A0 + c2
  XB : ∀ k ∈ Finset.Icc m (N + 1), dalX ζ q₀ δ k ≤ (c2 * (r / 2)) / δ ^ 2
  XN : c1 * (r / 4) / δ ^ 2 ≤ dalX ζ q₀ δ N
  gap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ dalX ζ q₀ δ (k + 1) - dalX ζ q₀ δ k ∧
    dalX ζ q₀ δ (k + 1) - dalX ζ q₀ δ k ≤ c2 * δ

/-- `dal_lattice_window` with its output packaged as `DalLat`. -/
theorem dal_lattice_window_struct {ζ : ℝ → ℝ} {c0 r c1 c2 A0 : ℝ} (hr : 0 < r) (hc1 : 0 < c1) (hc12 : c1 ≤ c2)
    (hA0 : 0 < A0) (hz0 : ζ c0 = 0)
    (hd : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 →
      ∃ J m N : ℤ, DalLat ζ q₀ δ c0 r c1 c2 A0 J m N := by
  obtain ⟨δ0, h0, h1, H⟩ := dal_lattice_window hr hc1 hc12 hA0 hz0 hd
  refine ⟨δ0, h0, h1, fun δ q₀ hδ hδ0 => ?_⟩
  obtain ⟨J, m, N, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := H δ q₀ hδ hδ0
  exact ⟨J, m, N, ⟨a1, a2, a3, a4, a5, a6, a7, by unfold dalQ; push_cast; exact a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩⟩

lemma dal_jac_congr_c {a c c' y : ℤ → ℝ} {k : ℤ} (h : c k = c' k) : jac a c y k = jac a c' y k := by
  unfold jac; rw [h]

/-- The row operator is Lipschitz in its coefficients. -/
lemma dal_jac_perturb (a a' c c' y : ℤ → ℝ) (k : ℤ) :
    |jac a c y k - jac a' c' y k| ≤
      |a (k + 1) - a' (k + 1)| * |y (k + 1)| + |a k - a' k| * |y (k - 1)| + |c k - c' k| * |y k| := by
  have e : jac a c y k - jac a' c' y k =
      (a (k + 1) - a' (k + 1)) * y (k + 1) + (a k - a' k) * y (k - 1) - (c k - c' k) * y k := by
    unfold jac; ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_) <;> simp [abs_mul]

/-- **Exact-coefficient defect on the window** (M7b + `langer_hrel`), see the module docstring. -/
theorem dal_exact_defect {U : Set ℝ} {ζ A g u : ℝ → ℝ} {c0 r : ℝ} (hU : IsOpen U)
    (hsub : Set.Icc (c0 - r) (c0 + r) ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (heik : ∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) :
    ∃ K K' δ1 : ℝ, 0 < K ∧ 0 < K' ∧ 0 < δ1 ∧ δ1 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ1 → ∀ k : ℤ,
      dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r) →
        |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (dalPsi g ζ q₀ δ) k| ≤ K * δ ^ 6 * airyWt (dalX ζ q₀ δ k) ∧
        (-1 ≤ dalX ζ q₀ δ k →
          |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
            (dalPsi g ζ q₀ δ) k| ≤ K' * δ ^ 6 * |dalPsi g ζ q₀ δ k|) := by
  have hJ : IsCompact (Set.Icc (c0 - r) (c0 + r)) := isCompact_Icc
  obtain ⟨K, h0, hK, hh0, H⟩ := airyParametrix_defect_uniform_lattice hU hJ hsub hζ hA hg hrel
  obtain ⟨K', h0', hK', hh0', H'⟩ := airyParametrix_defect_uniform_rel hU hJ hsub hζ hA hg hrel
  refine ⟨K, K', min 1 (min h0 h0'), hK, hK', lt_min one_pos (lt_min hh0 hh0'), min_le_left _ _,
    fun δ q₀ hδ hδ1 k hk => ?_⟩
  have hδ1' : δ ≤ 1 := hδ1.trans (min_le_left _ _)
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  have hh0δ : δ ^ 3 ≤ h0 := h3δ.trans (hδ1.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hh0δ' : δ ^ 3 ≤ h0' := h3δ.trans (hδ1.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hkU : q₀ + (k : ℝ) * δ ^ 3 ∈ U := hsub hk
  set c' : ℤ → ℝ := fun j => 2 * A (q₀ + (j : ℝ) * δ ^ 3) *
    langerCosh (ζ (q₀ + (j : ℝ) * δ ^ 3) * deriv ζ (q₀ + (j : ℝ) * δ ^ 3) ^ 2) with hc'
  have hcc : c' k = 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k) := by
    simp only [hc', dalQ]; rw [heik _ hkU]
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  have key1 := H (δ ^ 3) q₀ (fun j => A (q₀ + (j : ℝ) * δ ^ 3 - δ ^ 3 / 2)) c'
    (dalPsi g ζ q₀ δ) h3 hh0δ (fun j => rfl) (fun j => rfl) (fun j => rfl) k hk
  have key2 := H' (δ ^ 3) q₀ (fun j => A (q₀ + (j : ℝ) * δ ^ 3 - δ ^ 3 / 2)) c'
    (dalPsi g ζ q₀ δ) h3 hh0δ' (fun j => rfl) (fun j => rfl) (fun j => rfl) k hk
  have hj : jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
      (dalPsi g ζ q₀ δ) k =
      jac (fun j => A (q₀ + (j : ℝ) * δ ^ 3 - δ ^ 3 / 2)) c' (dalPsi g ζ q₀ δ) k := by
    unfold jac
    rw [hcc]
    rfl
  rw [hj]
  refine ⟨?_, fun hX => ?_⟩
  · have := key1; rw [e6] at this; exact this
  · have := key2 hX; rw [e6] at this; exact this

/-- Comparison with the weight on `X ≥ -1`: `κ₁ airyWt ≤ g Ai ≤ κ₂ airyWt`. -/
lemma dal_psi_cmp {g X : ℝ} {gmin gmax : ℝ} (hg1 : gmin ≤ g) (hg2 : g ≤ gmax) (hgm : 0 < gmin) (hX : -1 ≤ X) :
    gmin / 20 * airyWt X ≤ g * airyAi X ∧ g * airyAi X ≤ 6 * gmax * airyWt X := by
  have h1 := airyWt_div_twenty_le_airyAi hX
  have h2 := airyAi_le_six_airyWt hX
  have hw := airyWt_pos X
  have hg0 : 0 < g := lt_of_lt_of_le hgm hg1
  have hAi : 0 < airyAi X := by linarith
  constructor
  · calc gmin / 20 * airyWt X = gmin * (airyWt X / 20) := by ring
      _ ≤ g * airyAi X := mul_le_mul hg1 h1 (by positivity) hg0.le
  · calc g * airyAi X ≤ gmax * (6 * airyWt X) := mul_le_mul hg2 h2 hAi.le (hg0.le.trans hg2)
      _ = 6 * gmax * airyWt X := by ring

/-- `|g Ai(X)| ≤ 25 g_max` for `0 ≤ g ≤ g_max`. -/
lemma dal_psi_abs_le {g X gmax : ℝ} (hg0 : 0 ≤ g) (hg2 : g ≤ gmax) : |g * airyAi X| ≤ 25 * gmax := by
  have h := (apx_airy_global X).1
  have hw := airyWt_le_one X
  rw [abs_mul, abs_of_nonneg hg0]
  have : |airyAi X| ≤ 25 := h.trans (by linarith)
  calc g * |airyAi X| ≤ gmax * 25 := mul_le_mul hg2 this (abs_nonneg _) (hg0.trans hg2)
    _ = 25 * gmax := by ring

/-- Neighbouring lattice points: `airyWt X' ≤ (6/5) e^{c₂√(1+B)} airyWt X` when `|X' - X| ≤ c₂ δ ≤ 1`,
`|X| ≤ B/δ²`, `δ ≤ 1`. -/
lemma dal_airyWt_nbr {X X' c2 B δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc2 : 0 ≤ c2) (hc2δ : c2 * δ ≤ 1)
    (hX : |X| ≤ B / δ ^ 2) (hB : 0 ≤ B) (hd : |X' - X| ≤ c2 * δ) :
    airyWt X' ≤ 6 / 5 * Real.exp (c2 * √(1 + B)) * airyWt X := by
  refine airyWt_le_of_close (hd.trans hc2δ) ?_
  have h1 : |X' - X| * √(1 + |X|) ≤ c2 * δ * √(1 + B / δ ^ 2) :=
    mul_le_mul hd (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)
  refine h1.trans ?_
  have h2 : δ * √(1 + B / δ ^ 2) = √(δ ^ 2 + B) := by
    have : (δ ^ 2 + B) = δ ^ 2 * (1 + B / δ ^ 2) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]
  have h3 : √(δ ^ 2 + B) ≤ √(1 + B) :=
    Real.sqrt_le_sqrt (by nlinarith)
  calc c2 * δ * √(1 + B / δ ^ 2) = c2 * (δ * √(1 + B / δ ^ 2)) := by ring
    _ = c2 * √(δ ^ 2 + B) := by rw [h2]
    _ ≤ c2 * √(1 + B) := mul_le_mul_of_nonneg_left h3 hc2

/-- info: 'FormalResearch.Special.dal_exact_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dal_exact_defect

end FormalResearch.Special

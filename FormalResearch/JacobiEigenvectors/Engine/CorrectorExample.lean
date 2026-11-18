module

public import FormalResearch.JacobiEigenvectors.Engine.Corrector

/-!
# Paper J engine, L1.2 (part 4): a non-vacuous instance of `thm:eng-corr` (`K = 1`)

Source: non-vacuity check for `CorrSetting` and `Correctors` of `Corrector` (`thm:eng-corr`).  Namespace
`FormalResearch.JacobiEigenvectors.Engine`.

## The instance
The lattice is rotated by a quarter turn at every step: `P ≡ 𝒟 ≡ 1`, `Π₊ = [[0,1],[-1,0]]`, `Π₋ = Π₊⁻¹ = [[0,-1],[1,0]]`
(constant, `Σ Π₋ Σ = Π₊`), `𝐰^{(1)}(u) = (cos θ, -sin θ)`, `𝐰^{(2)}(u) = (sin θ, cos θ)` with `θ = πu/(2h)`, `ω_mod = 1`
(`exLadder`).  The diagonal symbol is `𝒬_h(u) = h² cos u`, so that the Langer condition holds (`P₀(Π₊₁₁ + Π₋₁₁) = 0 = 𝒬₀`) but
`𝒬_h ≠ 0`.  Then `V₀ = -1`, `M₀ = Ω₀²V₀ = 1`, `c₀ = -1`, `g₀ = 1`, and the recursion of `thm:eng-corr` (`K = 1`) is explicit:

* `𝔄^tot[(g₀, 0)] = -h² cos u` (first order is exercised: `exDefect_m1`, and the order is sharp: `exDefect_m1_not_O3`);
* `(a)_1`: `𝒯[b₁] = -2 b₁' = cos u` gives `b₁ = -sin(u)/2`;
* `F_cas[(g₀, b₁)] = -1 - h² b₁(s+h/2) b₁(s-h/2) = -1 - h²(sin² s - sin²(h/2))/4`, so the coefficient of `h²` is `-sin² s/4`;
* `(b)_1` (`c₁ = 0`): `2V₀g₀g₁ = sin² s/4`, i.e. `g₁ = (cos 2u - 1)/16 = -sin² u/8`.

`exCorrSetting` and `exCorrectors` verify every hypothesis of `eng_corr` for this data (the recursions are checked in their universally
quantified form, so the coefficient characterisation is exercised), and `ex_eng_corr` is `eng_corr` for `m = 1, 2, 3`.  `exDefect_m3_pt`: the
defect of `v^{[3]}` is nonzero (`𝔄^tot(0,1) ≠ 0`), only `O(h⁴)`.
-/

@[expose] public section

noncomputable section

open Finset

namespace FormalResearch.JacobiEigenvectors.Engine

/-! ### Small lemmas -/

/-- If `h^n a(u) = O(h^{n+2})` then `a = 0`. -/
lemma coeff_unique {n : ℕ} {a : ℝ → ℝ} (h : UO (n + 2) (fun u h => h ^ n * a u)) : ∀ u, a u = 0 := by
  intro u
  obtain ⟨C, δ, hC, hδ, hδ1, H⟩ := h.norm
  refine eq_zero_of_le_mul_small (C := C) (δ := min δ 1) (lt_min hδ one_pos) fun t ht htδ => ?_
  have h1 := H u t (by rw [abs_of_pos ht]; exact lt_of_lt_of_le htδ (min_le_left _ _))
  rw [abs_of_pos ht, abs_mul, abs_pow, abs_of_pos ht] at h1
  have htn : 0 < t ^ n := pow_pos ht n
  have ht1 : t < 1 := lt_of_lt_of_le htδ (min_le_right _ _)
  have : t ^ n * |a u| ≤ t ^ n * (C * t) := by
    calc t ^ n * |a u| ≤ C * t ^ (n + 2) := h1
      _ = t ^ n * (C * t ^ 2) := by ring
      _ ≤ t ^ n * (C * t) := by
          apply mul_le_mul_of_nonneg_left _ htn.le
          exact mul_le_mul_of_nonneg_left (by nlinarith) hC
  exact le_of_mul_le_mul_left this htn

lemma bsmooth_const (c : ℝ) : ∀ N : ℕ, BSmooth N (fun _ => c) := by
  intro N
  induction N generalizing c with
  | zero => exact ⟨|c|, fun _ => le_rfl⟩
  | succ N ih =>
    refine ⟨⟨|c|, fun _ => le_rfl⟩, differentiable_const c, ?_⟩
    have : deriv (fun _ : ℝ => c) = fun _ => 0 := funext fun _ => deriv_const _ _
    rw [this]; exact ih 0

/-- `u ↦ a cos(ω u) + b sin(ω u) + d`. -/
def trigp (a b ω d : ℝ) (u : ℝ) : ℝ := a * Real.cos (ω * u) + b * Real.sin (ω * u) + d

lemma trigp_hasDerivAt (a b ω d u : ℝ) : HasDerivAt (trigp a b ω d) (trigp (b * ω) (-(a * ω)) ω 0 u) u := by
  have h1 : HasDerivAt (fun u : ℝ => ω * u) ω u := by simpa using (hasDerivAt_id u).const_mul ω
  have h2 := (h1.cos.const_mul a).add (h1.sin.const_mul b)
  have h3 := h2.add_const d
  unfold trigp
  convert h3 using 1
  ring

lemma trigp_deriv (a b ω d : ℝ) : deriv (trigp a b ω d) = trigp (b * ω) (-(a * ω)) ω 0 :=
  funext fun u => (trigp_hasDerivAt a b ω d u).deriv

lemma trigp_abs_le (a b ω d u : ℝ) : |trigp a b ω d u| ≤ |a| + |b| + |d| := by
  unfold trigp
  have c1 := Real.abs_cos_le_one (ω * u)
  have c2 := Real.abs_sin_le_one (ω * u)
  have t1 := abs_add_le (a * Real.cos (ω * u) + b * Real.sin (ω * u)) d
  have t2 := abs_add_le (a * Real.cos (ω * u)) (b * Real.sin (ω * u))
  rw [abs_mul, abs_mul] at t2
  have m1 := mul_le_mul_of_nonneg_left c1 (abs_nonneg a)
  have m2 := mul_le_mul_of_nonneg_left c2 (abs_nonneg b)
  nlinarith

lemma bsmooth_trigp : ∀ (N : ℕ) (a b ω d : ℝ), BSmooth N (trigp a b ω d) := by
  intro N
  induction N with
  | zero => intro a b ω d; exact ⟨_, trigp_abs_le a b ω d⟩
  | succ N ih =>
    intro a b ω d
    refine ⟨⟨_, trigp_abs_le a b ω d⟩, fun u => (trigp_hasDerivAt a b ω d u).differentiableAt, ?_⟩
    rw [trigp_deriv]
    exact ih _ _ _ _

/-! ### The ladder -/

/-- `𝒟 ≡ 1`. -/
def exDD : ℝ → ℝ → ℝ := fun _ _ => 1
/-- `P ≡ 1`. -/
def exPP : ℝ → ℝ → ℝ := fun _ _ => 1
/-- `𝒬_h(u) = h² cos u`. -/
def exQQ : ℝ → ℝ → ℝ := fun u h => h ^ 2 * Real.cos u
/-- `Π₊ = [[0,1],[-1,0]]`. -/
def exPiP : ℝ → ℝ → M2 := fun _ _ => !![0, 1; -1, 0]
/-- `Π₋ = Π₊⁻¹ = [[0,-1],[1,0]]`. -/
def exPiM : ℝ → ℝ → M2 := fun _ _ => !![0, -1; 1, 0]
/-- The model columns: rotation by `-π u/(2h)`. -/
def exW (α : Fin 2) (u h : ℝ) : V2 :=
  if α = 0 then ![Real.cos (Real.pi * u / (2 * h)), -Real.sin (Real.pi * u / (2 * h))]
  else ![Real.sin (Real.pi * u / (2 * h)), Real.cos (Real.pi * u / (2 * h))]

lemma exW_up (α : Fin 2) (u h : ℝ) (hh : h ≠ 0) : exW α (u + h) h = colMul (exPiP u h) (exW α u h) := by
  have e : Real.pi * (u + h) / (2 * h) = Real.pi * u / (2 * h) + Real.pi / 2 := by field_simp
  fin_cases α <;> funext i <;> fin_cases i <;>
    simp [exW, colMul, exPiP, e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

lemma exW_dn (α : Fin 2) (u h : ℝ) (hh : h ≠ 0) : exW α (u - h) h = colMul (exPiM u h) (exW α u h) := by
  have e : Real.pi * (u - h) / (2 * h) = Real.pi * u / (2 * h) - Real.pi / 2 := by field_simp
  fin_cases α <;> funext i <;> fin_cases i <;>
    simp [exW, colMul, exPiM, e, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]

lemma exW_wronsk (u h : ℝ) : colDet (exW 0 u h) (exW 1 u h) = 1 := by
  have := Real.cos_sq_add_sin_sq (Real.pi * u / (2 * h))
  simp [colDet, exW]
  nlinarith

/-- The quarter-turn ladder is a symplectic model ladder (shift `γ = 0`). -/
theorem exLadder : SymplecticLadder 0 exDD exPP exQQ exPiP exPiM exW (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h _ j
    exact exW_wronsk _ _
  · intro h _; norm_num
  · intro α h hh j
    simp only [Dp, exDD, one_smul]
    exact exW_up α _ h hh.ne'
  · intro α h hh j _
    simp only [Dm, exDD, one_smul]
    exact exW_dn α _ h hh.ne'
  · intro u h; simp [Dp, exDD, exPiP, Matrix.det_fin_two]
  · intro u h; simp [Dm, exDD, exPiM, Matrix.det_fin_two]
  · intro u h
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [exPiM, exPiP, Dp, exDD, Matrix.mul_apply, Fin.sum_univ_two]
  · intro u h; simp [Dp, Dm, exDD]
  · intro u h
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [exPiM, exPiP, Sg, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The hypotheses of `thm:eng-corr` -/

lemma exM0 : M0fun exPP exPiM = fun _ => (1 : ℝ) := funext fun s => by simp [M0fun, exPP, exPiM]

lemma exV0 (u : ℝ) : V0fun exPP exPiM u = -1 := by simp [V0fun, exPP, exPiM]

/-- The standing hypotheses of `thm:eng-corr` hold for the quarter-turn ladder with `𝒬_h = h² cos u` (`K = 1`). -/
theorem exCorrSetting : CorrSetting 1 0 exDD exPP exQQ exPiP exPiM exW (fun _ => (1 : ℝ)) where
  ladder := exLadder
  pp_even := fun _ _ => rfl
  qq_even := fun u h => by simp [exQQ]
  exp :=
    { sP := fun i j => (PApprox.const (exPiP 0 0 i j)).congr (fun u h => by simp [exPP, exPiP])
      sM := fun i j => (PApprox.const (exPiM 0 0 i j)).congr (fun u h => by simp [exPP, exPiM])
      qe := ((PApprox.hpow 2).mul (PApprox.of_fun Real.cos (C := 1) (fun u => Real.abs_cos_le_one u))).congr
        (fun u h => rfl)
      cM := fun i j => (PApprox.const (exPiM 0 0 i j)).congr (fun u h => by simp [exPP, exPiM])
      bddP := fun i j => UO.of_bdd (C := |exPiP 0 0 i j|) (fun u h => le_rfl)
      bddM := fun i j => UO.of_bdd (C := |exPiM 0 0 i j|) (fun u h => le_rfl) }
  nondeg := ⟨1, one_pos, fun s h _ _ => by simp [exDD]⟩
  langer := fun u => by simp [exPP, exPiP, exPiM, exQQ]
  M0_smooth := by rw [exM0]; exact bsmooth_const 1 2

/-! ### The correctors -/

/-- `g₀ = 1`, `g₁ = (cos 2u - 1)/16 = -sin² u/8`, `g_i = 0` for `i ≥ 2`. -/
def exG (i : ℕ) : ℝ → ℝ :=
  if i = 0 then fun _ => 1 else if i = 1 then trigp (1 / 16) 0 2 (-1 / 16) else fun _ => 0

/-- `b₁ = B₁ = -sin(u)/2`, `b_i = 0` otherwise. -/
def exB (i : ℕ) : ℝ → ℝ := if i = 1 then trigp 0 (-1 / 2) 1 0 else fun _ => 0

/-- `c₀ = -1`, `c_i = 0` for `i ≥ 1`. -/
def exC (i : ℕ) : ℝ := if i = 0 then -1 else 0

lemma exC1 : exC 1 = 0 := by simp [exC]

lemma exG0 (u : ℝ) : exG 0 u = 1 := by simp [exG]

lemma exG1 (u : ℝ) : exG 1 u = (Real.cos (2 * u) - 1) / 16 := by simp [exG, trigp]; ring

lemma exB1 (u : ℝ) : exB 1 u = -Real.sin u / 2 := by simp [exB, trigp]; ring

lemma exB1_deriv (u : ℝ) : deriv (exB 1) u = -Real.cos u / 2 := by
  have : exB 1 = trigp 0 (-1 / 2) 1 0 := by simp [exB]
  rw [this, trigp_deriv]
  simp [trigp]
  ring

lemma exA1 (u h : ℝ) : Aans exG 1 u h = 1 := by simp [Aans, exG0]

lemma exBans0 (u h : ℝ) : Bans exB 0 u h = 0 := by simp [Bans]

lemma exBans1 (u h : ℝ) : Bans exB 1 u h = -Real.sin u / 2 := by simp [Bans, exB1]

/-- The defect of `v^{[1]} = (g₀, 0)`: `𝔄^tot = -h² cos u`. -/
lemma exDefect_m1 (u h : ℝ) : dA exPP exQQ exPiP exPiM exG exB 1 0 u h = -(h ^ 2 * Real.cos u) := by
  simp [dA, defectRow, vrow, rowMul, exA1, exBans0, exPP, exQQ, exPiP, exPiM]

lemma sin_mul_sin (s t : ℝ) : Real.sin (s + t) * Real.sin (s - t) = Real.sin s ^ 2 - Real.sin t ^ 2 := by
  rw [Real.sin_add, Real.sin_sub]
  have hs := Real.sin_sq_add_cos_sq s
  have ht := Real.sin_sq_add_cos_sq t
  linear_combination (Real.sin s ^ 2) * ht - (Real.sin t ^ 2) * hs

/-- `F_cas` of `(g₀, b₁)`: `-1 - h² (sin² s - sin²(h/2))/4`. -/
lemma exFlux (s h : ℝ) :
    FF exPP exPiM exG exB 1 1 s h = -1 - h ^ 2 * (Real.sin s ^ 2 - Real.sin (h / 2) ^ 2) / 4 := by
  simp only [FF, Fcas_expand]
  simp [exPP, exPiM, exA1, exBans1]
  have := sin_mul_sin s (h / 2)
  linear_combination (h ^ 2 / 4) * this

lemma sin_sq_half_UO : UO 4 (fun (_ : ℝ) h => h ^ 2 * Real.sin (h / 2) ^ 2 / 4) := by
  refine ⟨1 / 16, 1, one_pos, fun u h _ => ?_⟩
  have h1 : Real.sin (h / 2) ^ 2 ≤ (h / 2) ^ 2 := by
    have := Real.abs_sin_le_abs (x := h / 2)
    calc Real.sin (h / 2) ^ 2 = |Real.sin (h / 2)| ^ 2 := (sq_abs _).symm
      _ ≤ |h / 2| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (h / 2) ^ 2 := sq_abs _
  have h2 : 0 ≤ h ^ 2 * Real.sin (h / 2) ^ 2 / 4 := by positivity
  rw [abs_of_nonneg h2]
  have h3 : |h| ^ 4 = h ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h3]
  nlinarith [sq_nonneg h, mul_le_mul_of_nonneg_left h1 (sq_nonneg h)]

/-- The correctors `exG`, `exB`, `exC` satisfy the recursion of `thm:eng-corr` (`K = 1`). -/
theorem exCorrectors : Correctors 1 exPP exQQ exPiP exPiM exG exB exC where
  g0 := fun u => by simp [exG0, exV0, exC]
  c0_sign := fun u => by simp [exV0, exC]
  g0_pos := ⟨1, one_pos, fun u => by simp [exG0]⟩
  g_reg := by
    intro i hi
    interval_cases i
    · have : exG 0 = fun _ => (1 : ℝ) := by funext u; simp [exG0]
      rw [this]; exact bsmooth_const 1 _
    · have : exG 1 = trigp (1 / 16) 0 2 (-1 / 16) := by simp [exG]
      rw [this]; exact bsmooth_trigp _ _ _ _ _
  b_reg := by
    intro i hi1 hi
    obtain rfl : i = 1 := by omega
    have : exB 1 = trigp 0 (-1 / 2) 1 0 := by simp [exB]
    rw [this]; exact bsmooth_trigp _ _ _ _ _
  transport := by
    intro k hk1 hkK a hUO
    obtain rfl : k = 1 := by omega
    have e : ∀ u h : ℝ, dA exPP exQQ exPiP exPiM exG exB 1 (1 - 1) u h - h ^ (2 * 1) * a u
        = h ^ 2 * (-(Real.cos u) - a u) := by
      intro u h
      have := exDefect_m1 u h
      simp only [Nat.sub_self] at this ⊢
      rw [this]; ring
    have hz := coeff_unique (n := 2) (a := fun u => -(Real.cos u) - a u) (hUO.congr e)
    intro u
    have hu := hz u
    simp only [transportOp, exM0, exB1_deriv]
    simp
    linarith
  flux := by
    intro k hk1 hkK f hUO
    obtain rfl : k = 1 := by omega
    intro s
    have e : ∀ s h : ℝ, FF exPP exPiM exG exB 1 1 s h - Pc exC 1 h - h ^ (2 * 1) * f s
        = h ^ 2 * (-(Real.sin s ^ 2) / 4 - f s) + h ^ 2 * Real.sin (h / 2) ^ 2 / 4 := by
      intro s h
      rw [exFlux]
      simp [Pc, exC]
      ring
    have hUO' := hUO.congr e
    have h2 : UO 4 (fun s h => h ^ 2 * (-(Real.sin s ^ 2) / 4 - f s)) := by
      have := hUO'.sub sin_sq_half_UO
      exact this.congr fun s h => by ring
    have hz := coeff_unique (n := 2) (a := fun s => -(Real.sin s ^ 2) / 4 - f s) h2 s
    simp only [exV0, exG0, exG1, exC1] at hz ⊢
    have hc : Real.cos (2 * s) = 1 - 2 * Real.sin s ^ 2 := by
      rw [Real.cos_two_mul, Real.cos_sq']; ring
    rw [hc]
    linarith

/-- **`thm:eng-corr` for the instance** (`K = 1`): the defect orders for `m = 1, 2, 3`. -/
theorem ex_eng_corr {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 3) :
    (Odd m → UO (m + 1) (fun u h => defectRow exPP exQQ (Ahat exG m) (Bhat exB m) exPiP exPiM u h 0) ∧
        UO (m + 2) (fun u h => defectRow exPP exQQ (Ahat exG m) (Bhat exB m) exPiP exPiM u h 1)) ∧
    (Even m → UO (m + 2) (fun u h => defectRow exPP exQQ (Ahat exG m) (Bhat exB m) exPiP exPiM u h 0) ∧
        UO (m + 1) (fun u h => defectRow exPP exQQ (Ahat exG m) (Bhat exB m) exPiP exPiM u h 1)) :=
  eng_corr exCorrSetting exCorrectors hm1 (by omega)

/-- The order `O(h²)` for `m = 1` is sharp: `𝔄^tot[(g₀,0)] = -h² cos u` is not `O(h³)` (the first corrector is needed). -/
theorem exDefect_m1_not_O3 : ¬ UO 3 (dA exPP exQQ exPiP exPiM exG exB 1 0) := by
  rintro ⟨C, δ, hδ, H⟩
  have := eq_zero_of_le_mul_small (a := (1 : ℝ)) (C := C) (δ := δ) hδ (fun t ht htδ => by
    have h1 := H 0 t (by rw [abs_of_pos ht]; exact htδ)
    rw [exDefect_m1, abs_of_pos ht] at h1
    simp only [Real.cos_zero, mul_one, abs_neg] at h1
    rw [abs_of_pos (by positivity)] at h1
    have ht2 : 0 < t ^ 2 := by positivity
    have : t ^ 2 * 1 ≤ t ^ 2 * (C * t) := by nlinarith [h1, pow_pos ht 3]
    simpa using le_of_mul_le_mul_left this ht2)
  simp at this

/-- The defect of `v^{[3]} = (1 + h² g₁, h b₁)` is not zero: `𝔄^tot(0,1) = sin 1 - 1 ≠ 0`. -/
theorem exDefect_m3_pt : dA exPP exQQ exPiP exPiM exG exB 2 1 0 1 ≠ 0 := by
  have h1 : dA exPP exQQ exPiP exPiM exG exB 2 1 0 1 = Real.sin 1 - 1 := by
    simp [dA, defectRow, vrow, rowMul, Aans, Bans, exPP, exQQ, exPiP, exPiM, exG0, exG1, exB1, Finset.sum_range_succ]
    ring_nf
  rw [h1]
  have := Real.sin_lt (show (0 : ℝ) < 1 by norm_num)
  linarith

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JacobiEigenvectors.Engine.exCorrSetting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.exCorrSetting

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.exCorrectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.exCorrectors

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ex_eng_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ex_eng_corr

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.exDefect_m1_not_O3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.exDefect_m1_not_O3

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.exDefect_m3_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.exDefect_m3_pt

end FormalResearch.JacobiEigenvectors.Engine

end

end

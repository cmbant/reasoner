module

public import FormalResearch.SignUncertainty.Gt1NegTailAmp
public import FormalResearch.SignUncertainty.Gt1Symbol
public import FormalResearch.SignUncertainty.Gt1Schwartz
public import FormalResearch.SignUncertainty.Gt1LiftSeed
public import FormalResearch.SignUncertainty.Gt1Interface

/-!
# `GT.1` for the three basis seeds: the negative-tail symbols and `Gt1BasisInput m`

`Gt1NegTailAmp.lean` gives `Ai(-w) = a₊ e^{-iξ} + a₋ e^{iξ}` (and the `Ai'` analogue) with amplitudes bounded on the sector by
`2‖w‖^{-1/4}` (resp. `4‖w‖^{1/4}`).  Here:

* `symBd_negAmp*`: the amplitudes are holomorphic on the sector `{x₀/2 < re w, |im w| < re w/2}` (`Ai`, `Ai'` entire, `w^{1/2}` holomorphic on
  `re w > 0`), so by the Cauchy lemma `symBd_of_sector` their restrictions to `(x₀, ∞)` are symbols of order `1/4` (resp. `-1/4`) through order `12`.
* `seed_of_quadratic`: if `X(-x) = (A e^{-iΞ} + B e^{iΞ})² · cc(x)` for `x ≥ x₀` (`Ξ = (2/3) x^{3/2}`) with `A, B, cc` symbols of orders `βA, βA, βc` with
  `βA + βA + βc ≥ 3/2`, then `X` is an `AiryTailSymbolSeed` with `b₀ = 2 A B cc`, `bPos = B² cc`, `bNeg = A² cc` (symbol algebra of `Gt1Symbol.lean`).
* the three seeds: `f₁ = Ai²/(u - a₁)`, `g₁ = Ai²/(u - a₁)²`, `g₁' = Ai'²/(u - a₁')²` for `u < a₁'` (`dslope` with `Ai(a₁) = Ai'(a₁') = 0`), hence
  `cc = -1/(x + a₁)` (order 1), `1/(x + a₁)²` (order 2), `1/(x + a₁')²` (order 2) and total orders `3/2`, `5/2`, `3/2`.
* `gt1BasisInput`: `Gt1BasisInput m` for every `m ≥ 3`, from `gt1Bounds_liftW_of_seed` and the three seeds.

Status: proved, unconditional.  This discharges the named input `Gt1BasisInput m` of the middle band (`Gt1Interface.lean`).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Holomorphy of the amplitudes -/

lemma differentiableAt_negPhase {w : ℂ} (hre : 0 < w.re) : DifferentiableAt ℂ negPhase w := by
  have hs : w ∈ Complex.slitPlane := Or.inl hre
  unfold negPhase
  have h1 : DifferentiableAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) w :=
    DifferentiableAt.cpow_const differentiableAt_fun_id hs
  exact (h1.pow 3).const_mul _

lemma differentiable_deriv_airyAiC' : Differentiable ℂ (deriv airyAiC) := fun z =>
  ((differentiable_airyAiC.differentiableOn.deriv isOpen_univ) z (mem_univ z)).differentiableAt Filter.univ_mem

lemma differentiableAt_negAmpP {w : ℂ} (hre : 0 < w.re) : DifferentiableAt ℂ negAmpP w := by
  have hφ := differentiableAt_negPhase hre
  have h1 : DifferentiableAt ℂ (fun w : ℂ => airyAiC (airyOmega ^ 2 * -w)) w :=
    DifferentiableAt.comp (g := airyAiC) w (differentiable_airyAiC _) (by fun_prop)
  unfold negAmpP
  exact ((h1.const_mul _).neg).mul ((hφ.const_mul I).cexp)

lemma differentiableAt_negAmpM {w : ℂ} (hre : 0 < w.re) : DifferentiableAt ℂ negAmpM w := by
  have hφ := differentiableAt_negPhase hre
  have h1 : DifferentiableAt ℂ (fun w : ℂ => airyAiC (airyOmega * -w)) w :=
    DifferentiableAt.comp (g := airyAiC) w (differentiable_airyAiC _) (by fun_prop)
  unfold negAmpM
  exact ((h1.const_mul _).neg).mul ((hφ.const_mul I).neg.cexp)

lemma differentiableAt_negAmpP' {w : ℂ} (hre : 0 < w.re) : DifferentiableAt ℂ negAmpP' w := by
  have hφ := differentiableAt_negPhase hre
  have h1 : DifferentiableAt ℂ (fun w : ℂ => deriv airyAiC (airyOmega ^ 2 * -w)) w :=
    DifferentiableAt.comp (g := deriv airyAiC) w (differentiable_deriv_airyAiC' _) (by fun_prop)
  unfold negAmpP'
  exact ((h1.const_mul _).neg).mul ((hφ.const_mul I).cexp)

lemma differentiableAt_negAmpM' {w : ℂ} (hre : 0 < w.re) : DifferentiableAt ℂ negAmpM' w := by
  have hφ := differentiableAt_negPhase hre
  have h1 : DifferentiableAt ℂ (fun w : ℂ => deriv airyAiC (airyOmega * -w)) w :=
    DifferentiableAt.comp (g := deriv airyAiC) w (differentiable_deriv_airyAiC' _) (by fun_prop)
  unfold negAmpM'
  exact ((h1.const_mul _).neg).mul ((hφ.const_mul I).neg.cexp)

lemma sector_pos {x₀ : ℝ} (hx₀ : 2 ≤ x₀) {w : ℂ} (h : x₀ / 2 < w.re) : 0 < w.re := by linarith

lemma sector_one_le {x₀ : ℝ} (hx₀ : 2 ≤ x₀) {w : ℂ} (h : x₀ / 2 < w.re) : 1 ≤ ‖w‖ :=
  (by linarith : (1 : ℝ) ≤ w.re).trans (Complex.re_le_norm w)

/-! ### The amplitudes are symbols -/

theorem symBd_negAmpP {x₀ : ℝ} (hx₀ : 2 ≤ x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd 12 x₀ (1 / 4) M (fun x : ℝ => negAmpP (x : ℂ)) := by
  obtain ⟨C, hC, h⟩ := symBd_of_sector 12 (1 / 4)
  refine ⟨C * 2, by positivity, h (x₀ := x₀) (M := 2) (g := negAmpP) (by linarith) (by norm_num)
    (fun w hw => (differentiableAt_negAmpP (sector_pos hx₀ hw.1)).differentiableWithinAt)
    (fun w h1 h2 => negAmpP_bound (sector_pos hx₀ h1) h2 (sector_one_le hx₀ h1))⟩

theorem symBd_negAmpM {x₀ : ℝ} (hx₀ : 2 ≤ x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd 12 x₀ (1 / 4) M (fun x : ℝ => negAmpM (x : ℂ)) := by
  obtain ⟨C, hC, h⟩ := symBd_of_sector 12 (1 / 4)
  refine ⟨C * 2, by positivity, h (x₀ := x₀) (M := 2) (g := negAmpM) (by linarith) (by norm_num)
    (fun w hw => (differentiableAt_negAmpM (sector_pos hx₀ hw.1)).differentiableWithinAt)
    (fun w h1 h2 => negAmpM_bound (sector_pos hx₀ h1) h2 (sector_one_le hx₀ h1))⟩

theorem symBd_negAmpP' {x₀ : ℝ} (hx₀ : 2 ≤ x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd 12 x₀ (-(1 / 4)) M (fun x : ℝ => negAmpP' (x : ℂ)) := by
  obtain ⟨C, hC, h⟩ := symBd_of_sector 12 (-(1 / 4))
  refine ⟨C * 4, by positivity, h (x₀ := x₀) (M := 4) (g := negAmpP') (by linarith) (by norm_num)
    (fun w hw => (differentiableAt_negAmpP' (sector_pos hx₀ hw.1)).differentiableWithinAt)
    (fun w h1 h2 => negAmpP'_bound (sector_pos hx₀ h1) h2 (sector_one_le hx₀ h1))⟩

theorem symBd_negAmpM' {x₀ : ℝ} (hx₀ : 2 ≤ x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd 12 x₀ (-(1 / 4)) M (fun x : ℝ => negAmpM' (x : ℂ)) := by
  obtain ⟨C, hC, h⟩ := symBd_of_sector 12 (-(1 / 4))
  refine ⟨C * 4, by positivity, h (x₀ := x₀) (M := 4) (g := negAmpM') (by linarith) (by norm_num)
    (fun w hw => (differentiableAt_negAmpM' (sector_pos hx₀ hw.1)).differentiableWithinAt)
    (fun w h1 h2 => negAmpM'_bound (sector_pos hx₀ h1) h2 (sector_one_le hx₀ h1))⟩

theorem SymBd.nonneg' {N : ℕ} {x₀ β M : ℝ} {b : ℝ → ℂ} (hx₀ : 0 < x₀) (h : SymBd N x₀ β M b) : 0 ≤ M :=
  le_trans (mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x₀ + 1) _) (norm_nonneg _))
    (h.bd 0 (Nat.zero_le _) (x₀ + 1) (by linarith))

/-! ### Assembly of an `AiryTailSymbolSeed` from a quadratic tail form -/

lemma quad_expand (A B cc : ℂ) (Ξ Θ₁ Θ₂ : ℝ) (h1 : Θ₁ = 2 * Ξ) (h2 : Θ₂ = -(2 * Ξ)) :
    (A * cexp (-(I * (Ξ : ℂ))) + B * cexp (I * (Ξ : ℂ))) ^ 2 * cc =
      2 * (A * B * cc) + (B * B * cc) * cexp (I * (Θ₁ : ℂ)) + (A * A * cc) * cexp (I * (Θ₂ : ℂ)) := by
  have e1 : cexp (I * (Θ₁ : ℂ)) = cexp (I * (Ξ : ℂ)) * cexp (I * (Ξ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; rw [h1]; push_cast; ring
  have e2 : cexp (I * (Θ₂ : ℂ)) = cexp (-(I * (Ξ : ℂ))) * cexp (-(I * (Ξ : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; rw [h2]; push_cast; ring
  have hE := exp_mul_exp_neg (Ξ : ℂ)
  rw [e1, e2]
  linear_combination (2 * A * B * cc) * hE

theorem seed_of_quadratic (X : ℝ → ℝ)
    (hX : X = ceF1 ∨ X = ceG1 (airyZero 1) ∨ X = ceG1Deriv airyDerivFirstZero)
    (x₀ : ℝ) (hx₀ : 1 ≤ x₀) (χ : AiryCutoff)
    (A B cc : ℝ → ℂ) (βA βc MA MB Mc : ℝ)
    (hA : SymBd 12 x₀ βA MA A) (hB : SymBd 12 x₀ βA MB B) (hcc : SymBd 12 x₀ βc Mc cc)
    (hβ : 3 / 2 ≤ βA + βA + βc)
    (hF : ∀ x : ℝ, x₀ ≤ x → ((X (-x) : ℝ) : ℂ) =
      (A x * cexp (-(I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) +
        B x * cexp (I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) ^ 2 * cc x) :
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ ∃ seed : AiryTailSymbolSeed x₀ χ S M, seed.F = X := by
  have hx0 : 0 < x₀ := by linarith
  have hAB := SymBd.mul hx0 hA hB
  have hAA := SymBd.mul hx0 hA hA
  have hBB := SymBd.mul hx0 hB hB
  have s0 := SymBd.const_mul (2 : ℂ) (SymBd.mul hx0 hAB hcc)
  have s1 := SymBd.mul hx0 hBB hcc
  have s2 := SymBd.mul hx0 hAA hcc
  have hord : (3 / 2 : ℝ) ≤ βA + βA + βc := hβ
  have t0 := SymBd.mono_order hx₀ (β' := 3 / 2) hord s0
  have t1 := SymBd.mono_order hx₀ (β' := 3 / 2) hord s1
  have t2 := SymBd.mono_order hx₀ (β' := 3 / 2) hord s2
  have n0 := SymBd.nonneg' hx0 t0
  have n1 := SymBd.nonneg' hx0 t1
  have n2 := SymBd.nonneg' hx0 t2
  obtain ⟨hcd, S, hS⟩ := seed_cutoff_schwartz X hX x₀ hx₀ χ
  have hS0 : 0 ≤ S := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (hS 0 (by norm_num) 0)
  have key : ∃ M₀ M₁ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      SymBd 12 x₀ (3 / 2) M₀ (fun x : ℝ => 2 * (A x * B x * cc x)) ∧
      SymBd 12 x₀ (3 / 2) M₁ (fun x : ℝ => B x * B x * cc x) ∧
      SymBd 12 x₀ (3 / 2) M₂ (fun x : ℝ => A x * A x * cc x) := ⟨_, _, _, n0, n1, n2, t0, t1, t2⟩
  obtain ⟨M₀, M₁, M₂, h0, h1, h2, u0, u1, u2⟩ := key
  refine ⟨S, M₀ + M₁ + M₂, hS0, by linarith, ?_⟩
  refine ⟨{ F := X
            continuous := (seed_contDiff X hX).continuous
            schwartz_cd := hcd
            schwartz_bd := fun k hk u => hS k hk u
            b₀ := fun x : ℝ => 2 * (A x * B x * cc x)
            bPos := fun x : ℝ => B x * B x * cc x
            bNeg := fun x : ℝ => A x * A x * cc x
            sym_cd := ⟨u0.cd, u1.cd, u2.cd⟩
            sym_bd := fun k hk x hx => ⟨?_, ?_, ?_⟩
            tail_eq := fun x hx => ?_ }, rfl⟩
  · exact (u0.bd k hk x hx).trans (by linarith)
  · exact (u1.bd k hk x hx).trans (by linarith)
  · exact (u2.bd k hk x hx).trans (by linarith)
  · show ((X (-x) : ℝ) : ℂ) = _
    rw [hF x hx]
    exact quad_expand (A x) (B x) (cc x) (2 / 3 * x ^ (3 / 2 : ℝ)) ((4 / 3 : ℝ) * x ^ (3 / 2 : ℝ))
      ((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) (by ring) (by ring)

/-! ### The three basis seeds -/

lemma negPhase_ofReal {x : ℝ} (hx : 0 ≤ x) : negPhase (x : ℂ) = ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  unfold negPhase
  have h1 : ((x : ℂ)) ^ (1 / 2 : ℂ) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx]; push_cast; rfl
  rw [h1]
  have h2 : (x ^ (1 / 2 : ℝ)) ^ 3 = x ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  rw [← h2]; push_cast; ring

lemma ai_real_split {x : ℝ} (hx : 0 ≤ x) :
    ((airyAi (-x) : ℝ) : ℂ) = negAmpP (x : ℂ) * cexp (-(I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) +
      negAmpM (x : ℂ) * cexp (I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) := by
  have h := neg_split (x : ℂ)
  rw [negPhase_ofReal hx] at h
  rw [← h, ← airyAiC_ofReal]; push_cast; rfl

lemma aip_real_split {x : ℝ} (hx : 0 ≤ x) :
    ((airyAi' (-x) : ℝ) : ℂ) = negAmpP' (x : ℂ) * cexp (-(I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) +
      negAmpM' (x : ℂ) * cexp (I * ((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) := by
  have h := neg_split' (x : ℂ)
  rw [negPhase_ofReal hx] at h
  rw [← h, ← deriv_airyAiC_ofReal]; push_cast; rfl

lemma pos_of_tail {a x x₀ : ℝ} (ha : a < 0) (hx : 2 * |a| ≤ x₀) (hxx : x₀ ≤ x) : 0 < x + a := by
  rw [abs_of_neg ha] at hx
  linarith

lemma tail_f1 {x x₀ : ℝ} (hx : 2 * |airyZero 1| ≤ x₀) (hxx : x₀ ≤ x) :
    ((ceF1 (-x) : ℝ) : ℂ) = ((airyAi (-x) : ℝ) : ℂ) ^ 2 * ((-1 : ℂ) * ((1 / (x + airyZero 1) ^ 1 : ℝ) : ℂ)) := by
  have ha : airyZero 1 < 0 := airyZero_neg 1
  have hp := pos_of_tail ha hx hxx
  have hne : -x ≠ airyZero 1 := by intro h; linarith
  have hd : x + airyZero 1 ≠ 0 := hp.ne'
  have hreal : ceF1 (-x) = airyAi (-x) ^ 2 * (-1 * (1 / (x + airyZero 1) ^ 1)) := by
    unfold ceF1
    rw [dslope_of_ne _ hne, slope_def_field, airyAi_airyZero 1]
    rw [show -x - airyZero 1 = -(x + airyZero 1) by ring]
    field_simp
    ring
  exact_mod_cast hreal

lemma tail_g1 {x x₀ : ℝ} (hx : 2 * |airyZero 1| ≤ x₀) (hxx : x₀ ≤ x) :
    ((ceG1 (airyZero 1) (-x) : ℝ) : ℂ) = ((airyAi (-x) : ℝ) : ℂ) ^ 2 * ((1 / (x + airyZero 1) ^ 2 : ℝ) : ℂ) := by
  have ha : airyZero 1 < 0 := airyZero_neg 1
  have hp := pos_of_tail ha hx hxx
  have hne : -x ≠ airyZero 1 := by intro h; linarith
  have hd : x + airyZero 1 ≠ 0 := hp.ne'
  have hreal : ceG1 (airyZero 1) (-x) = airyAi (-x) ^ 2 * (1 / (x + airyZero 1) ^ 2) := by
    unfold ceG1
    rw [dslope_of_ne _ hne, slope_def_field, airyAi_airyZero 1]
    rw [show -x - airyZero 1 = -(x + airyZero 1) by ring]
    field_simp
    ring
  exact_mod_cast hreal

lemma tail_g1d {x x₀ : ℝ} (hx : 2 * |airyDerivFirstZero| ≤ x₀) (hxx : x₀ ≤ x) :
    ((ceG1Deriv airyDerivFirstZero (-x) : ℝ) : ℂ) =
      ((airyAi' (-x) : ℝ) : ℂ) ^ 2 * ((1 / (x + airyDerivFirstZero) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨-, ha, hz⟩ := airyDerivFirstZero_spec
  have hp := pos_of_tail ha hx hxx
  have hne : -x ≠ airyDerivFirstZero := by intro h; linarith
  have hd : x + airyDerivFirstZero ≠ 0 := hp.ne'
  have hreal : ceG1Deriv airyDerivFirstZero (-x) = airyAi' (-x) ^ 2 * (1 / (x + airyDerivFirstZero) ^ 2) := by
    unfold ceG1Deriv
    rw [dslope_of_ne _ hne, slope_def_field, hz]
    rw [show -x - airyDerivFirstZero = -(x + airyDerivFirstZero) by ring]
    field_simp
    ring
  exact_mod_cast hreal

theorem seed_f1 {x₀ : ℝ} (hx₀ : 2 ≤ x₀) (h1 : 2 * |airyZero 1| ≤ x₀) (χ : AiryCutoff) :
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ ∃ seed : AiryTailSymbolSeed x₀ χ S M, seed.F = ceF1 := by
  obtain ⟨MA, -, hA⟩ := symBd_negAmpP hx₀
  obtain ⟨MB, -, hB⟩ := symBd_negAmpM hx₀
  obtain ⟨Mi, -, hi⟩ := symBd_inv_pow_add 12 (a := airyZero 1) 1 h1 (by linarith)
  have hc := SymBd.const_mul (-1 : ℂ) hi
  refine seed_of_quadratic ceF1 (Or.inl rfl) x₀ (by linarith) χ _ _ _ _ _ _ _ _ hA hB hc (by norm_num) ?_
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  rw [tail_f1 h1 hx, ai_real_split hx0]

theorem seed_g1 {x₀ : ℝ} (hx₀ : 2 ≤ x₀) (h1 : 2 * |airyZero 1| ≤ x₀) (χ : AiryCutoff) :
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ ∃ seed : AiryTailSymbolSeed x₀ χ S M, seed.F = ceG1 (airyZero 1) := by
  obtain ⟨MA, -, hA⟩ := symBd_negAmpP hx₀
  obtain ⟨MB, -, hB⟩ := symBd_negAmpM hx₀
  obtain ⟨Mi, -, hi⟩ := symBd_inv_pow_add 12 (a := airyZero 1) 2 h1 (by linarith)
  refine seed_of_quadratic (ceG1 (airyZero 1)) (Or.inr (Or.inl rfl)) x₀ (by linarith) χ _ _ _ _ _ _ _ _
    hA hB hi (by norm_num) ?_
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  rw [tail_g1 h1 hx, ai_real_split hx0]

theorem seed_g1d {x₀ : ℝ} (hx₀ : 2 ≤ x₀) (h1 : 2 * |airyDerivFirstZero| ≤ x₀) (χ : AiryCutoff) :
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ ∃ seed : AiryTailSymbolSeed x₀ χ S M, seed.F = ceG1Deriv airyDerivFirstZero := by
  obtain ⟨MA, -, hA⟩ := symBd_negAmpP' hx₀
  obtain ⟨MB, -, hB⟩ := symBd_negAmpM' hx₀
  obtain ⟨Mi, -, hi⟩ := symBd_inv_pow_add 12 (a := airyDerivFirstZero) 2 h1 (by linarith)
  refine seed_of_quadratic (ceG1Deriv airyDerivFirstZero) (Or.inr (Or.inr rfl)) x₀ (by linarith) χ _ _ _ _ _ _ _ _
    hA hB hi (by norm_num) ?_
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  rw [tail_g1d h1 hx, aip_real_split hx0]

/-- **`GT.1` for the three basis seeds** (`Gt1BasisInput m`), for every spline order `m ≥ 3`: the symbols `W(v) = M_ψ(iv) X̃(i c_s v)` of
`f₁, g₁, g₁'` satisfy the `GT.1` bounds, uniformly in `δ₀ ∈ [0, 2]`. -/
theorem gt1BasisInput (m : ℕ) (hm : 3 ≤ m) : Gt1BasisInput m := by
  obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : ℝ, x₀ = 2 + 2 * |airyZero 1| + 2 * |airyDerivFirstZero| := ⟨_, rfl⟩
  have hx2 : 2 ≤ x₀ := by
    rw [hx₀def]; have := abs_nonneg (airyZero 1); have := abs_nonneg airyDerivFirstZero; linarith
  have hxa : 2 * |airyZero 1| ≤ x₀ := by
    rw [hx₀def]; have := abs_nonneg airyDerivFirstZero; linarith
  have hxb : 2 * |airyDerivFirstZero| ≤ x₀ := by
    rw [hx₀def]; have := abs_nonneg (airyZero 1); linarith
  obtain ⟨S₁, M₁, hS₁, hM₁, s₁, hs₁⟩ := seed_f1 hx2 hxa AiryCutoff.standard
  obtain ⟨S₂, M₂, hS₂, hM₂, s₂, hs₂⟩ := seed_g1 hx2 hxa AiryCutoff.standard
  obtain ⟨S₃, M₃, hS₃, hM₃, s₃, hs₃⟩ := seed_g1d hx2 hxb AiryCutoff.standard
  obtain ⟨C, hC, hlift⟩ := gt1Bounds_liftW_of_seed m hm (by linarith : (1 : ℝ) ≤ x₀) AiryCutoff.standard
  refine ⟨C * (S₁ + M₁ + S₂ + M₂ + S₃ + M₃), by positivity, fun δ₀ hδ => ⟨?_, ?_, ?_⟩⟩
  · have h := hlift s₁ hδ
    rw [hs₁] at h
    have e : airySeedU2 1 0 0 = ceF1 := funext fun u => by simp [airySeedU2]
    rw [e]
    exact h.mono (by nlinarith)
  · have h := hlift s₂ hδ
    rw [hs₂] at h
    have e : airySeedU2 0 1 0 = ceG1 (airyZero 1) := funext fun u => by simp [airySeedU2]
    rw [e]
    exact h.mono (by nlinarith)
  · have h := hlift s₃ hδ
    rw [hs₃] at h
    have e : airySeedU2 0 0 1 = ceG1Deriv airyDerivFirstZero := funext fun u => by simp [airySeedU2]
    rw [e]
    exact h.mono (by nlinarith)

/-- info: 'FormalResearch.SignUncertainty.symBd_negAmpP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms symBd_negAmpP
/-- info: 'FormalResearch.SignUncertainty.symBd_negAmpM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms symBd_negAmpM
/-- info: 'FormalResearch.SignUncertainty.symBd_negAmpP'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms symBd_negAmpP'
/-- info: 'FormalResearch.SignUncertainty.symBd_negAmpM'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms symBd_negAmpM'
/-- info: 'FormalResearch.SignUncertainty.SymBd.nonneg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SymBd.nonneg'
/-- info: 'FormalResearch.SignUncertainty.seed_f1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seed_f1
/-- info: 'FormalResearch.SignUncertainty.seed_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seed_g1
/-- info: 'FormalResearch.SignUncertainty.seed_g1d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seed_g1d
/-- info: 'FormalResearch.SignUncertainty.seed_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seed_of_quadratic
/-- info: 'FormalResearch.SignUncertainty.gt1BasisInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gt1BasisInput

end FormalResearch.SignUncertainty

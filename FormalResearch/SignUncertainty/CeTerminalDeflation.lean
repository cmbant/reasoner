module

public import FormalResearch.SignUncertainty.AiryActiveHeight

/-!
# Terminal-cardinal deflation and unified Hermite–Biehler quadrature (`lem:ce-terminal-deflation`)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex` (`lem:ce-terminal-deflation`, lines 315–331).

Main results:

* `airyPQHB_eq_C_of_Q_eq_zero`, `hb_zero_weight_pos_all`, `hb_real_quadrature`: unified real-zero
  weight positivity (`D(t_n) > 0`, `N'(t_n) ≠ 0`) and unconditional quadrature
  `∫_ℝ H = ∑_n D(t_n) H(t_n) / N'(t_n)²` for every `D : ShellHBData` (covering both `D.Q = 0`, where
  `D.P` is a nonzero constant and `airyQ_hasSum_unc` applies, and `D.Q ≠ 0`, where
  `airyPQ_hasSum_unc` applies) and every `H ∈ 𝒢` (`InAiryClass`).
* `terminal_cardinal_integral`: for every `D : ShellHBData`, the terminal cardinal
  `H_N = dslope (-D.G) D.tm` lies in `𝒢`, `u ↦ -(D.G u).re / (u - D.tm)` is integrable on `ℝ`, and
  `I_N = ∫_ℝ (-(D.G u).re) / (u - D.tm) du = D(t_m) / ∏_{s ∈ shellSites D} (s - t_m) > 0`.
* `ce_terminal_deflation_full` (`lem:ce-terminal-deflation`, full statement): under
  `∀ y > 0, 0 ≤ airyLaplace (-D.G) y`, the above plus the Laplace lower bound `(eq:ce-deflation-pos)`
  `airyLaplace H_N y ≥ I_N exp(t_m y - y³ / 12) > 0` for all `y ≥ 0`. The Laplace hypothesis is used only for
  this last clause (and implies `m` odd); `terminal_cardinal_integral` proves the former `terminal_deflation`
  field of `CeCanonicalInputs` and makes `Headlines.uSh_eq_tm_of_canonical` unconditional.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Unified Hermite–Biehler weight positivity and real quadrature (`Q = 0` and `Q ≠ 0`) -/

/-- If `(P, 0)` is Hermite–Biehler (`AiryPQHB P 0`), then `P` has no complex roots (conjugate
symmetry would violate `Im z < 0`) and is therefore a nonzero real constant. -/
theorem airyPQHB_eq_C_of_Q_eq_zero {P : ℝ[X]} (hHB : AiryPQHB P 0) :
    ∃ p₀ : ℝ, p₀ ≠ 0 ∧ P = Polynomial.C p₀ := by
  have hroots : (airyPQF P 0).roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun w hw => ?_
    have hw_im : w.im < 0 := hHB.roots_im hw
    have hw_eval : (airyPQF P 0).eval w = 0 := (Polynomial.mem_roots hHB.F_ne_zero).mp hw
    rw [airyPQF_eval, airyPQc_zero, zero_add] at hw_eval
    have hPw : airyPQc P w = 0 := (mul_eq_zero.mp hw_eval).resolve_left I_ne_zero
    have hPconj : airyPQc P ((starRingEnd ℂ) w) = 0 := by
      rw [← conj_airyPQc, hPw, map_zero]
    have hconj_im : ((starRingEnd ℂ) w).im < 0 :=
      hHB ((starRingEnd ℂ) w) (by rw [airyPQc_zero, hPconj, mul_zero, add_zero])
    rw [Complex.conj_im] at hconj_im
    linarith
  have hdeg : (airyPQF P 0).natDegree = 0 := by
    rw [(IsAlgClosed.splits (airyPQF P 0)).natDegree_eq_card_roots, hroots]
    simp
  have hC : airyPQF P 0 = Polynomial.C ((airyPQF P 0).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  refine ⟨P.eval 0, fun h0 => airyPQHB_ne_zero_real hHB 0 ⟨Polynomial.eval_zero, h0⟩, ?_⟩
  refine Polynomial.funext fun x => ?_
  rw [Polynomial.eval_C]
  have hx := congrArg (fun q : ℂ[X] => q.eval (x : ℂ)) hC
  have h0 := congrArg (fun q : ℂ[X] => q.eval ((0 : ℝ) : ℂ)) hC
  rw [airyPQF_eval, airyPQc_zero, zero_add, airyPQc_ofReal, Polynomial.eval_C] at hx h0
  have heq : I * ((P.eval x : ℝ) : ℂ) = I * ((P.eval 0 : ℝ) : ℂ) := hx.trans h0.symm
  exact Complex.ofReal_injective (mul_left_cancel₀ I_ne_zero heq)

/-- At every real point `x`, `airyPQN' P Q x` is real. -/
lemma airyPQN'_im_ofReal (P Q : ℝ[X]) (x : ℝ) :
    (airyPQN' P Q (x : ℂ)).im = 0 := by
  unfold airyPQN'
  rw [airyPQc_ofReal, airyPQc_ofReal, airyPQc_ofReal, airyPQc_ofReal,
    airyAiC_ofReal, deriv_airyAiC_ofReal]
  simp

/-- Unified real-zero weight positivity (`gt:1.0pp`) for every `D : ShellHBData` (both `D.Q = 0`
and `D.Q ≠ 0`): at any real zero `x` of `N = P Ai + Q Ai'`, `D(x) > 0` and `(N'(x)).re ≠ 0`. -/
theorem hb_zero_weight_pos_all (D : ShellHBData) {x : ℝ}
    (hx : airyPQN D.P D.Q (x : ℂ) = 0) :
    0 < airyPQDr D.P D.Q x ∧ (airyPQN' D.P D.Q (x : ℂ)).re ≠ 0 := by
  have him0 := airyPQN'_im_ofReal D.P D.Q x
  by_cases hQ : D.Q = 0
  · obtain ⟨p₀, hp₀, hP⟩ := airyPQHB_eq_C_of_Q_eq_zero (hQ ▸ D.hHB)
    have hD_eq : airyPQDr D.P D.Q x = p₀ ^ 2 := by
      unfold airyPQDr
      rw [hP, hQ]
      simp [sq]
    have hAi0 : airyAi x = 0 := by
      rw [airyPQN_ofReal, hP, hQ] at hx
      simp only [Polynomial.eval_C, Polynomial.eval_zero, zero_mul, add_zero,
        Complex.ofReal_eq_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_left hp₀
    have hAi' : airyAi' x ≠ 0 := fun h' => airyAi_ne_zero_of_deriv_zero h' hAi0
    have hN'_re : (airyPQN' D.P D.Q (x : ℂ)).re = p₀ * airyAi' x := by
      unfold airyPQN'
      rw [hP, hQ, airyPQc_C, airyPQc_zero, Polynomial.derivative_C, Polynomial.derivative_zero,
        airyPQc_zero, airyAiC_ofReal, deriv_airyAiC_ofReal]
      simp
    exact ⟨hD_eq ▸ sq_pos_of_ne_zero hp₀, hN'_re ▸ mul_ne_zero hp₀ hAi'⟩
  · obtain ⟨hD, hN'_ne⟩ := airyPQ_zero_weight_pos D.hHB hQ hx
    refine ⟨hD, fun hre0 => hN'_ne (Complex.ext hre0 him0)⟩

/-- Unified unconditional real quadrature (`gt:1.0pp` / `airyQ_hasSum_unc` + `airyPQ_hasSum_unc`)
for any `D : ShellHBData`, zero enumeration `ht : IsHbZeroEnum D.P D.Q t`, and `H ∈ 𝒢`:
`∫_ℝ Re H(u) du = ∑_{n=0}^∞ D(t_n) Re H(t_n) / (Re N'(t_n))²`. -/
theorem hb_real_quadrature (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    {H : ℂ → ℂ} (hH : InAiryClass H) :
    HasSum (fun n : ℕ =>
      airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2)
      (∫ u : ℝ, (H (u : ℂ)).re) := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hreal⟩ := hH
  have hint_re : ∫ u : ℝ, (H (u : ℂ)).re = (∫ u : ℝ, H (u : ℂ)).re := integral_re hi
  by_cases hQ : D.Q = 0
  · obtain ⟨p₀, hp₀, hP⟩ := airyPQHB_eq_C_of_Q_eq_zero (hQ ▸ D.hHB)
    have hZ_enum : IsHbZeroEnum D.P D.Q (fun n => airyZero (n + 1)) := by
      refine ⟨fun a b hab => airyZero_lt_of_lt (by omega) (by omega), fun x => ?_⟩
      have hNf : at47_Nf D.P D.Q x = p₀ * airyAi x := by
        unfold at47_Nf
        rw [hP, hQ]
        simp
      rw [hNf, mul_eq_zero, or_iff_right hp₀]
      constructor
      · intro hAi
        obtain ⟨n, rfl⟩ := exists_airyZ_eq_of_airyAi_eq_zero hAi
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact airyAi_airyZero (n + 1)
    have ht_eq : ∀ n : ℕ, t n = airyZero (n + 1) :=
      congrFun (IsHbZeroEnum.unique ht hZ_enum)
    have hsumC := airyQ_hasSum_unc hd hi hC hb
    have hsumR := Complex.reCLM.hasSum hsumC
    change HasSum (fun n : ℕ =>
      (H (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re)
      (∫ x : ℝ, H (x : ℂ)).re at hsumR
    rw [← hint_re] at hsumR
    refine hsumR.congr_fun fun n => ?_
    rw [ht_eq n]
    set a := airyZero (n + 1)
    have hHa : H (a : ℂ) = (((H (a : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hreal a)
    have hAi' : airyAi' a ≠ 0 :=
      fun h' => airyAi_ne_zero_of_deriv_zero h' (airyAi_airyZero (n + 1))
    have hD_eq : airyPQDr D.P D.Q a = p₀ ^ 2 := by
      unfold airyPQDr; rw [hP, hQ]; simp [sq]
    have hN'_re : (airyPQN' D.P D.Q (a : ℂ)).re = p₀ * airyAi' a := by
      unfold airyPQN'
      rw [hP, hQ, airyPQc_C, airyPQc_zero, Polynomial.derivative_C, Polynomial.derivative_zero,
        airyPQc_zero, airyAiC_ofReal, deriv_airyAiC_ofReal]
      simp
    conv_rhs =>
      rw [hHa, deriv_airyAiC_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hD_eq, hN'_re]
    field_simp [hp₀, hAi']
  · have hsumZ := airyPQ_hasSum_unc D.hHB hQ hd hi hC hb
    let emb : ℕ → {z : ℂ // airyPQN D.P D.Q z = 0} := fun n =>
      ⟨(t n : ℂ), (nodeZero_iff D (t n)).2 ((ht.2 (t n)).2 ⟨n, rfl⟩)⟩
    have hemb_bij : Function.Bijective emb := by
      refine ⟨fun a b hab => ht.1.injective (Complex.ofReal_injective (congrArg Subtype.val hab)),
        fun z => ?_⟩
      have hzr : z.1 = ((z.1.re : ℝ) : ℂ) := airyPQ_zero_eq_ofReal D.hHB z.2
      have hNf0 : at47_Nf D.P D.Q z.1.re = 0 := (nodeZero_iff D z.1.re).1 (hzr ▸ z.2)
      obtain ⟨n, hn⟩ := (ht.2 z.1.re).1 hNf0
      refine ⟨n, Subtype.ext ?_⟩
      dsimp [emb]
      rw [hn, ← hzr]
    let e : ℕ ≃ {z : ℂ // airyPQN D.P D.Q z = 0} := Equiv.ofBijective emb hemb_bij
    have hsumN : HasSum (fun n : ℕ =>
        H (t n : ℂ) * (airyPQD D.P D.Q (t n : ℂ) / airyPQN' D.P D.Q (t n : ℂ) ^ 2))
        (∫ x : ℝ, H (x : ℂ)) := (Equiv.hasSum_iff e).2 hsumZ
    have hsumR := Complex.reCLM.hasSum hsumN
    change HasSum (fun n : ℕ =>
      (H (t n : ℂ) * (airyPQD D.P D.Q (t n : ℂ) / airyPQN' D.P D.Q (t n : ℂ) ^ 2)).re)
      (∫ x : ℝ, H (x : ℂ)).re at hsumR
    rw [← hint_re] at hsumR
    refine hsumR.congr_fun fun n => ?_
    have hHn : H (t n : ℂ) = (((H (t n : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hreal (t n))
    have hN'n : airyPQN' D.P D.Q (t n : ℂ) = (((airyPQN' D.P D.Q (t n : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (airyPQN'_im_ofReal D.P D.Q (t n))
    conv_rhs =>
      rw [hHn, airyPQD_ofReal, hN'n, ← Complex.ofReal_pow, ← Complex.ofReal_div,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    ring

/-! ### Terminal-cardinal deflation (`lem:ce-terminal-deflation`, `ce_shells.tex`) -/

private lemma prod_sub_swap (S : Finset ℝ) (z : ℂ) :
    (∏ s ∈ S, ((s : ℂ) - z)) = (-1 : ℂ) ^ S.card * ∏ s ∈ S, (z - (s : ℂ)) := by
  have h : ∀ s : ℝ, ((s : ℂ) - z) = (-1 : ℂ) * (z - (s : ℂ)) := fun s => by ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_const]

private lemma neg_one_pow_pred_mul {m : ℕ} (hm : 1 ≤ m) :
    (-1 : ℂ) ^ (m - 1) * (-1 : ℂ) ^ m = -1 := by
  rw [← pow_add]
  have hodd : Odd ((m - 1) + m) := ⟨m - 1, by omega⟩
  exact hodd.neg_one_pow

/-- Unconditional terminal-cardinal mass identity (`lem:hb-seed-mass` / `lem:ce-terminal-deflation`):
for every `D : ShellHBData`, `H_N = dslope (-D.G) D.tm ∈ 𝒢`, `u ↦ (-(D.G u).re) / (u - D.tm)` is
integrable on `ℝ`, and its integral equals `D(t_m) / ∏_{s ∈ shellSites D} (s - t_m) > 0`. -/
theorem terminal_cardinal_integral (D : ShellHBData) :
    InAiryClass (dslope (fun z => -D.G z) (D.tm : ℂ)) ∧
    Integrable (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) ∧
    (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      airyPQDr D.P D.Q D.tm / ∏ s ∈ shellSites D, (s - D.tm) ∧
    0 < ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm) := by
  let negG : ℂ → ℂ := fun z => -D.G z
  have hnegG_cl : InAiryClass negG := D.G_inAiryClass.neg
  have hnegG_tm0 : (negG (D.tm : ℂ)).re = 0 := by
    dsimp [negG]; rw [D.G_eq_zero_on_S D.tm D.tm_mem]; simp
  obtain ⟨hHN_cl, hdiv_int, hdiv_eq⟩ := deflation_inAiryClass hnegG_cl hnegG_tm0
  let H_N : ℂ → ℂ := dslope negG (D.tm : ℂ)
  change InAiryClass H_N at hHN_cl
  have hfun_eq : (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      fun u : ℝ => (negG (u : ℂ)).re / (u - D.tm) := rfl
  have hdiv_int' : Integrable (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) := by
    rwa [hfun_eq]
  have hdiv_eq' : (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) = ∫ u : ℝ, (H_N (u : ℂ)).re := by
    rw [hfun_eq, hdiv_eq]
  -- Algebraic identity: `H_N(z) * ∏_{s ∈ shellSites D} (s - z) = (dslope (airyPQN P Q) D.tm z)²`.
  let qN : ℂ → ℂ := dslope (airyPQN D.P D.Q) (D.tm : ℂ)
  have hqN_diff : Differentiable ℂ qN :=
    EntireDiv.differentiable_dslope_entire (differentiable_airyPQN D.P D.Q) (D.tm : ℂ)
  have hN_tm : airyPQN D.P D.Q (D.tm : ℂ) = 0 := D.S_zero D.tm_mem
  have hnegG_tm : negG (D.tm : ℂ) = 0 := by dsimp [negG]; rw [D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero]
  have hcard_pos : 1 ≤ D.S.card := Finset.card_pos.mpr D.S_nonempty
  have hcard_sh : (shellSites D).card = D.S.card - 1 := Finset.card_erase_of_mem D.tm_mem
  let prodSh : ℂ → ℂ := fun z => ∏ s ∈ shellSites D, ((s : ℂ) - z)
  have hprodSh_diff : Differentiable ℂ prodSh := by
    intro z
    dsimp [prodSh]
    fun_prop
  have h_ident : ∀ z : ℂ, H_N z * prodSh z = qN z ^ 2 := by
    have hdiff_sub : Differentiable ℂ (fun z => H_N z * prodSh z - qN z ^ 2) :=
      (hHN_cl.1.mul hprodSh_diff).sub (hqN_diff.pow 2)
    have hzero := airy_entire_eq_zero_of_real_interval hdiff_sub
      (by linarith : D.tm + 1 < D.tm + 2) fun x hx1 _ => sub_eq_zero.mpr <| by
        set z : ℂ := (x : ℂ)
        have hne : z - (D.tm : ℂ) ≠ 0 :=
          sub_ne_zero.mpr fun h => (by linarith : x ≠ D.tm) (Complex.ofReal_injective h)
        have hsq_ne : (z - (D.tm : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hne
        apply mul_left_cancel₀ hsq_ne
        have h1 : (z - (D.tm : ℂ)) * H_N z = -D.G z := by
          have e := sub_smul_dslope negG (D.tm : ℂ) z
          rw [hnegG_tm, sub_zero, smul_eq_mul] at e
          exact e
        have h2 : (z - (D.tm : ℂ)) * prodSh z = (-1 : ℂ) ^ (D.S.card - 1) * at47_pr D.S z := by
          dsimp [prodSh]
          rw [prod_sub_swap, hcard_sh]
          have hpr : (z - (D.tm : ℂ)) * (∏ s ∈ shellSites D, (z - (s : ℂ))) = at47_pr D.S z := by
            unfold shellSites at47_pr
            exact Finset.mul_prod_erase D.S (fun s => z - (s : ℂ)) D.tm_mem
          calc (z - (D.tm : ℂ)) * ((-1 : ℂ) ^ (D.S.card - 1) * ∏ s ∈ shellSites D, (z - (s : ℂ)))
              = (-1 : ℂ) ^ (D.S.card - 1) * ((z - (D.tm : ℂ)) * ∏ s ∈ shellSites D, (z - (s : ℂ))) := by ring
            _ = (-1 : ℂ) ^ (D.S.card - 1) * at47_pr D.S z := by rw [hpr]
        have h3 : (z - (D.tm : ℂ)) * qN z = airyPQN D.P D.Q z := by
          have e := sub_smul_dslope (airyPQN D.P D.Q) (D.tm : ℂ) z
          rwa [hN_tm, sub_zero, smul_eq_mul] at e
        have hG := D.G_prod_eq z
        have hsign : (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) = (-1 : ℂ) ^ D.S.card := by push_cast; rfl
        rw [hsign] at hG
        calc (z - (D.tm : ℂ)) ^ 2 * (H_N z * prodSh z)
            = ((z - (D.tm : ℂ)) * H_N z) * ((z - (D.tm : ℂ)) * prodSh z) := by ring
          _ = (-D.G z) * ((-1 : ℂ) ^ (D.S.card - 1) * at47_pr D.S z) := by rw [h1, h2]
          _ = -((-1 : ℂ) ^ (D.S.card - 1) * (D.G z * at47_pr D.S z)) := by ring
          _ = -(((-1 : ℂ) ^ (D.S.card - 1) * (-1 : ℂ) ^ D.S.card) * airyPQN D.P D.Q z ^ 2) := by
              rw [hG]; ring
          _ = airyPQN D.P D.Q z ^ 2 := by rw [neg_one_pow_pred_mul hcard_pos]; ring
          _ = ((z - (D.tm : ℂ)) * qN z) ^ 2 := by rw [h3]
          _ = (z - (D.tm : ℂ)) ^ 2 * qN z ^ 2 := by ring
    exact fun z => sub_eq_zero.mp (hzero z)
  -- Evaluate `h_ident` at `D.tm` (real parts).
  have hprod_pos : 0 < ∏ s ∈ shellSites D, (s - D.tm) := by
    refine Finset.prod_pos fun s hs => ?_
    obtain ⟨hs_ne, hs_mem⟩ := Finset.mem_erase.1 hs
    exact sub_pos.mpr (lt_of_le_of_ne (D.tm_min s hs_mem) hs_ne.symm)
  have hHN_tm : (H_N (D.tm : ℂ)).re =
      ((airyPQN' D.P D.Q (D.tm : ℂ)).re) ^ 2 / ∏ s ∈ shellSites D, (s - D.tm) := by
    have hev := h_ident (D.tm : ℂ)
    have hqN_tm : qN (D.tm : ℂ) = airyPQN' D.P D.Q (D.tm : ℂ) := by
      dsimp [qN]; rw [dslope_same, deriv_airyPQN]
    have hHN_c : H_N (D.tm : ℂ) = (((H_N (D.tm : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (hHN_cl.2.2.2 D.tm)
    have hN'_c : airyPQN' D.P D.Q (D.tm : ℂ) = (((airyPQN' D.P D.Q (D.tm : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (airyPQN'_im_ofReal D.P D.Q D.tm)
    have hpr_c : prodSh (D.tm : ℂ) = ((∏ s ∈ shellSites D, (s - D.tm) : ℝ) : ℂ) := by
      dsimp [prodSh]; push_cast; rfl
    rw [hqN_tm, hHN_c, hN'_c, hpr_c, ← Complex.ofReal_mul, ← Complex.ofReal_pow] at hev
    have hev_re : (H_N (D.tm : ℂ)).re * (∏ s ∈ shellSites D, (s - D.tm)) =
        ((airyPQN' D.P D.Q (D.tm : ℂ)).re) ^ 2 := Complex.ofReal_injective hev
    exact eq_div_of_mul_eq hprod_pos.ne' hev_re
  -- Apply `hb_real_quadrature` with `t = hbZeroEnum D`; only `n₀ = D.S.card - 1` (`t n₀ = D.tm`) survives.
  let t := hbZeroEnum D
  have ht : IsHbZeroEnum D.P D.Q t := hbZeroEnum_spec D
  have hquad := hb_real_quadrature D ht hHN_cl
  let n₀ : ℕ := D.S.card - 1
  have htn₀ : t n₀ = D.tm := (D.tm_eq_hbNode ht).symm
  have hHN_zero_other : ∀ n : ℕ, n ≠ n₀ → (H_N (t n : ℂ)).re = 0 := by
    intro n hne
    have htn_ne : t n ≠ D.tm := fun heq => hne (ht.1.injective (heq.trans htn₀.symm))
    have htn_c_ne : (t n : ℂ) ≠ (D.tm : ℂ) := fun h => htn_ne (Complex.ofReal_injective h)
    have hG_tn : D.G (t n : ℂ) = 0 := by
      by_cases hmem : t n ∈ D.S
      · exact D.G_eq_zero_on_S (t n) hmem
      · have hp := D.G_prod_eq (t n : ℂ)
        have hN0 : airyPQN D.P D.Q (t n : ℂ) = 0 := (nodeZero_iff D (t n)).2 ((ht.2 (t n)).2 ⟨n, rfl⟩)
        rw [hN0, zero_pow two_ne_zero, mul_zero] at hp
        exact (mul_eq_zero.mp hp).resolve_right (at47_pr_ne_zero hmem)
    have h0 : H_N (t n : ℂ) = 0 := by
      dsimp [H_N, negG]
      rw [dslope_of_ne _ htn_c_ne, slope_def_field, hG_tn, D.G_eq_zero_on_S D.tm D.tm_mem,
        neg_zero, sub_self, zero_div]
    rw [h0, Complex.zero_re]
  have hsingle : HasSum (fun n : ℕ =>
      airyPQDr D.P D.Q (t n) * (H_N (t n : ℂ)).re / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2)
      (airyPQDr D.P D.Q (t n₀) * (H_N (t n₀ : ℂ)).re / ((airyPQN' D.P D.Q (t n₀ : ℂ)).re) ^ 2) :=
    hasSum_single n₀ fun n hne => by rw [hHN_zero_other n hne, mul_zero, zero_div]
  obtain ⟨hD_pos, hN'_ne⟩ := hb_zero_weight_pos_all D hN_tm
  have hint_val : (∫ u : ℝ, (H_N (u : ℂ)).re) =
      airyPQDr D.P D.Q D.tm / ∏ s ∈ shellSites D, (s - D.tm) := by
    rw [hquad.unique hsingle, htn₀, hHN_tm]
    field_simp [hN'_ne, hprod_pos.ne']
  rw [hdiv_eq']
  exact ⟨hHN_cl, hdiv_int', hint_val, hint_val ▸ div_pos hD_pos hprod_pos⟩

/-- **`lem:ce-terminal-deflation` (`ce_shells.tex`, lines 315–331, full statement including
`(eq:ce-deflation-pos)`):** under `∀ y > 0, 0 ≤ airyLaplace (-D.G) y`, the terminal cardinal
`H_N = dslope (-D.G) D.tm ∈ 𝒢` has `I_N = ∫ H_N = D(t_m) / ∏_{s ∈ shellSites D} (s - t_m) > 0`
and `airyLaplace H_N y ≥ I_N exp(t_m y - y³ / 12) > 0` for every `y ≥ 0`. -/
theorem ce_terminal_deflation_full (D : ShellHBData)
    (hL : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) :
    InAiryClass (dslope (fun z => -D.G z) (D.tm : ℂ)) ∧
    Integrable (fun u : ℝ => (-(D.G (u : ℂ)).re) / (u - D.tm)) ∧
    (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      airyPQDr D.P D.Q D.tm / ∏ s ∈ shellSites D, (s - D.tm) ∧
    0 < ∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm) ∧
    ∀ y : ℝ, 0 ≤ y →
      (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) * Real.exp (D.tm * y - y ^ 3 / 12) ≤
        airyLaplace (fun u => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re) y ∧
      0 < (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) * Real.exp (D.tm * y - y ^ 3 / 12) := by
  obtain ⟨hHN_cl, hdiv_int, hval, hpos⟩ := terminal_cardinal_integral D
  refine ⟨hHN_cl, hdiv_int, hval, hpos, fun y hy => ?_⟩
  refine ⟨?_, mul_pos hpos (Real.exp_pos _)⟩
  let negG : ℂ → ℂ := fun z => -D.G z
  have hnegG_cl : InAiryClass negG := D.G_inAiryClass.neg
  have hnegG_tm0 : (negG (D.tm : ℂ)).re = 0 := by
    dsimp [negG]; rw [D.G_eq_zero_on_S D.tm D.tm_mem]; simp
  obtain ⟨-, -, hdiv_eq⟩ := deflation_inAiryClass hnegG_cl hnegG_tm0
  have hid := deflation_identity hnegG_cl hnegG_tm0 hy
  -- `L_{-G_N}(s) ≥ 0` for all `s ≥ 0`.
  have hL_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ laplaceL (fun u => (negG (u : ℂ)).re) s := by
    intro s hs
    rcases hs.eq_or_lt with rfl | hs_pos
    · unfold laplaceL
      have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
      simp_rw [zero_mul, Real.exp_zero, mul_one]
      dsimp [negG]
      rw [integral_neg, hre, D.G_integral_zero, Complex.zero_re, neg_zero]
    · have hs' := hL s hs_pos
      unfold airyLaplace at hs'
      have hint_nn : 0 ≤ ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (s * u) :=
        nonneg_of_mul_nonneg_right hs' (Real.exp_pos _)
      unfold laplaceL
      dsimp [negG]
      exact hint_nn
  have hint_s_nn : 0 ≤ ∫ s in (0 : ℝ)..y,
      Real.exp (-D.tm * s) * laplaceL (fun u => (negG (u : ℂ)).re) s := by
    refine intervalIntegral.integral_nonneg hy fun s hs => ?_
    exact mul_nonneg (Real.exp_pos _).le (hL_nn s hs.1)
  have hI_eq : (∫ u : ℝ, (-(D.G (u : ℂ)).re) / (u - D.tm)) =
      ∫ u : ℝ, (dslope negG (D.tm : ℂ) (u : ℂ)).re := hdiv_eq
  unfold airyLaplace
  have hlap_eq : (∫ u : ℝ, (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re * Real.exp (y * u)) =
      laplaceL (fun u => (dslope negG (D.tm : ℂ) (u : ℂ)).re) y := rfl
  rw [hlap_eq, hid, hI_eq]
  set I_N := ∫ u : ℝ, (dslope negG (D.tm : ℂ) (u : ℂ)).re
  set J := ∫ s in (0 : ℝ)..y, Real.exp (-D.tm * s) * laplaceL (fun u => (negG (u : ℂ)).re) s
  have hexp : D.tm * y - y ^ 3 / 12 = -y ^ 3 / 12 + D.tm * y := by ring
  calc I_N * Real.exp (D.tm * y - y ^ 3 / 12)
      = Real.exp (-y ^ 3 / 12) * (Real.exp (D.tm * y) * I_N) := by
          rw [hexp, Real.exp_add]; ring
    _ ≤ Real.exp (-y ^ 3 / 12) * (Real.exp (D.tm * y) * (I_N + J)) := by
          gcongr; linarith

/-- info: 'FormalResearch.SignUncertainty.ce_terminal_deflation_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_terminal_deflation_full

/-- info: 'FormalResearch.SignUncertainty.terminal_cardinal_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.terminal_cardinal_integral

end FormalResearch.SignUncertainty

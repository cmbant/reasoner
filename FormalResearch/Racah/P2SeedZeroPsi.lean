module

public import Mathlib
public import FormalResearch.Racah.P2SeedRational

/-!
# The scalar case `M = σ = 0`: `ψ_{2r} = 0` with the paper's `𝒥` (Weyl P2, `prop:localcalculus` (c))

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `app:3j-allorder`: `prop:localcalculus` (c)
("If `a = b = 0`, then `ψ_{2r} = 0` `(r ≥ 1)` gives the starts `Φ_0 = 1` and `Φ_1 = (x - q(0))/η(1)` to all
orders"), the `3j` instance ("For `M = σ = 0` one takes `ψ_{2r} = 0`"), `eq:3jscalarDallorder`,
`thm:3jallorderlocal`.

`P2AnalyticAllOrder3j.allorder_operators_zero` proves the identification `𝒢_r d_n = f_{2r}^{(n)}` for
`M = σ = 0` with operators obtained from the abstract recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` where
`𝒥 = Jsol` is an arbitrary left-normal solution of `[x, 𝒥(𝖡)] = 𝖡` and `ψ_{r+1}` the multiplier forced by the
start; the paper's statement is that the multiplier vanishes for the *specific* `𝒥(𝖡) = -∑ b_j ∂^{j+1}/(j+1)` of
`eq:3jJoperator`.  Here:

* `Jcan`, `exists_solution_canonical`: the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1})` with `ψ ≡ 0`, `𝒥` the explicit
  operator `Jop` of a left-normal representation `𝖡 = ∑ b_j ∂^j` (abstract: any `K`-module);
* `allorder_operators_zero_psi` (**`M = σ = 0`, `ψ_{2r} = 0`**): there are operators `𝒢_r`, `𝒢_0 = I`, left-normal
  with *rational* coefficients (`LN DOp Crat`), `[x, 𝒢_{r+1}] = 𝖡_{r+1}`, such that for every `r` there is a
  left-normal representation `𝖡_{r+1}` (hence `𝖡_r` of `Bop`) `= ∑_{j ≤ J} b_j ∂^j`, `b_j` rational, with
  `𝒢_{r+1} = 𝒥(𝖡_{r+1}) = -∑ b_j ∂^{j+1}/(j+1)` exactly (no multiplier), and `𝒢_r d_n = f_{2r}^{(n)}` at every
  rank `n` (`d_n = d^n_{00}`, `f_{2r}^{(n)}` the Taylor coefficients of the exact germ).

Claim class: proved.  The uniqueness of the left-normal representation `(b_j)` (so that `𝒥` is a function of
`𝖡`) is not formalised; the theorem is the existence statement with the paper's formula for `𝒥`.
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus

open Polynomial Module

section Canonical

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
variable (D : End K M) (C : Subalgebra K (End K M))

open Classical in
/-- The paper's `𝒥(𝖡) = -∑ b_j ∂^{j+1}/(j+1)` for a chosen left-normal representation of `𝖡`
(`0` if `𝖡` is not left-normal). -/
noncomputable def Jcan (B : End K M) : End K M :=
  if h : B ∈ LN D C then
    Jop D (Classical.choose (Classical.choose_spec (exists_rep h))) (Classical.choose (exists_rep h))
  else 0

variable {D C}

lemma Jop_mem_LN {b : ℕ → End K M} (hb : ∀ j, b j ∈ C) (J : ℕ) : Jop D b J ∈ LN D C := by
  unfold Jop
  exact neg_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (mem_LN_gen (hb j) _))

lemma Jcan_spec {B : End K M} (hB : B ∈ LN D C) :
    ∃ (J : ℕ) (b : ℕ → End K M), (∀ j, b j ∈ C) ∧ B = leftNormal D b J ∧ Jcan D C B = Jop D b J := by
  have h := Classical.choose_spec (Classical.choose_spec (exists_rep hB))
  refine ⟨Classical.choose (exists_rep hB), Classical.choose (Classical.choose_spec (exists_rep hB)),
    h.1, h.2, ?_⟩
  unfold Jcan
  simp only [hB, ↓reduceDIte]

lemma Jcan_comm [CharZero K] {x : End K M} (hD : D * x - x * D = 1) (hCx : ∀ c ∈ C, x * c = c * x)
    {B : End K M} (hB : B ∈ LN D C) : Jcan D C B ∈ LN D C ∧ comm x (Jcan D C B) = B := by
  obtain ⟨J, b, hb, hBb, hJ⟩ := Jcan_spec hB
  rw [hJ]
  exact ⟨Jop_mem_LN hb J, by rw [commutator_J x D hD b (fun j => hCx _ (hb j)) J, ← hBb]⟩

/-- **The recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1})` with no multiplier** (`ψ ≡ 0`, `eq:3jD2rrecursive`), where
`𝒥` is the explicit operator of `eq:3jJoperator`. -/
theorem exists_solution_canonical [CharZero K] {x : End K M} (hD : D * x - x * D = 1)
    (hCx : ∀ c ∈ C, x * c = c * x) (hCD : ∀ c ∈ C, D * c - c * D ∈ C) (hxC : x ∈ C) {H : End K M}
    (hH : H ∈ LN D C) (q : K[X]) (e : ℕ → K) (τ : K) :
    ∃ G : ℕ → End K M, G 0 = 1 ∧ (∀ r, G r ∈ LN D C) ∧
      (∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) ∧
      ∀ r, ∃ (J : ℕ) (b : ℕ → End K M), (∀ j, b j ∈ C) ∧ Bop x H q e τ G r = leftNormal D b J ∧
        G (r + 1) = Jop D b J := by
  set step : ℕ → End K M → End K M := fun _ B => Jcan D C B with hstep
  set G := Gseq x H q e τ step with hG
  have hG0 : G 0 = 1 := Gseq_zero x H q e τ step
  have hGs : ∀ r, G (r + 1) = Jcan D C (Bop x H q e τ G r) := fun r => Gseq_succ x H q e τ step r
  have hmem : ∀ r, ∀ n ≤ r, G n ∈ LN D C := by
    intro r
    induction r with
    | zero => intro n hn; obtain rfl : n = 0 := by omega
              rw [hG0]; exact C_le_LN C.one_mem
    | succ r ih =>
      intro n hn
      by_cases hnr : n = r + 1
      · subst hnr
        have hB := Bop_mem hD hCx hCD hxC hH q e τ ih
        rw [hGs]
        exact (Jcan_comm hD hCx hB).1
      · exact ih n (by omega)
  have hBm : ∀ r, Bop x H q e τ G r ∈ LN D C := fun r => Bop_mem hD hCx hCD hxC hH q e τ (hmem r)
  refine ⟨G, hG0, fun r => hmem r r le_rfl, fun r => ?_, fun r => ?_⟩
  · rw [hGs r]; exact (Jcan_comm hD hCx (hBm r)).2
  · obtain ⟨J, b, hb, hBb, hJ⟩ := Jcan_spec (hBm r)
    exact ⟨J, b, hb, hBb, by rw [hGs r, hJ]⟩

end Canonical

end FormalResearch.Racah.LocalCalculus

namespace FormalResearch.Racah.LocalCalculus.Fun

open Set Module FormalResearch.Wigner FormalResearch.Racah
open scoped ContDiff

/-- `d^0_{00} = 1` on `(-1,1)` is annihilated by `∂`. -/
lemma DOp_dv_scalar : DOp (dv 0 0 0) = 0 := by
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · rw [DOp_apply _ hy]
    have hev : (dv 0 0 0).1 =ᶠ[nhds y] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (isOpen_Sx.mem_nhds hy) fun z hz => dv_zero_scalar_apply hz
    rw [hev.deriv_eq]
    simp
  · rw [DOp_apply_off _ hy]; rfl

/-- The identification of a solution of the scalar recursion with the Taylor coefficients: any `𝒢_r`
(`𝒢_0 = 1`, `[x, 𝒢_{r+1}] = 𝖡_{r+1}`, `𝒢_{r+1} d_0 = 0`) satisfies `𝒢_r d_n = f_{2r}^{(n)}` for
`M = σ = 0` (`prop:localcalculus` (c) and forward uniqueness with the two starts). -/
theorem zero_ident (G : ℕ → End ℝ Fn) (hG0 : G 0 = 1)
    (hGB : ∀ r, comm xOp (G (r + 1)) =
      Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0) G r)
    (hGz : ∀ r, G (r + 1) (dv 0 0 0) = 0) :
    ∀ n r, ∀ y ∈ Sx, (G r (dv 0 0 n)).1 y = f3even 0 0 n r y := by
  have hα : |(0 : ℚ) - 0| = ((0 : ℕ) : ℚ) := by simp
  have hβ : |(0 : ℚ) + 0| = ((0 : ℕ) : ℚ) := by simp
  have hk : kz 0 0 = 0 := by simp [kz]
  have hτ : TauM 0 0 = 0 := by simp [TauM]
  have hd0 : Hop (SigM 0 0) (TauM 0 0) (dv 0 0 0) = 0 := by
    rw [Hop_dv]; simp [hk, LocalCalculus.lam]
  have hd1 : Hop (SigM 0 0) (TauM 0 0) (xOp (dv 0 0 0)) = (2 : ℝ) • xOp (dv 0 0 0) := by
    rw [← dv_one_scalar, Hop_dv]; simp [hk, LocalCalculus.lam]; norm_num
  have hGB' : ∀ r, comm xOp (G (r + 1)) =
      Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 0 G r := by
    intro r; rw [hGB r]; unfold LocalCalculus.Bop; rw [hτ]
  have hstart := LocalCalculus.scalar_start_series xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3
    c3_zero G hG0 (dv 0 0 0) hd0 hd1 hGz hGB'
  have hphys : LocalCalculus.smulS (LocalCalculus.eta c3 1) (fun r => physFn 0 0 1 r) =
      LocalCalculus.smulS (LocalCalculus.eta c3 1) (LocalCalculus.serG G (xOp (dv 0 0 0))) := by
    rw [hstart]
    funext r
    refine Fn.ext' fun y => ?_
    by_cases hy : y ∈ Sx
    · have h1 := congrArg (PowerSeries.coeff r) (Psi_zero_zero_one hy)
      have hL : evAt y (LocalCalculus.smulS (LocalCalculus.eta c3 1) (fun r => physFn 0 0 1 r) r) =
          if r = 0 then y else 0 := by
        rw [evAt_smulS]
        have : (fun s => evAt y (physFn 0 0 1 s)) = fun s => f3even 0 0 1 s y :=
          funext fun s => physFn_apply (M := 0) (σ := 0) 1 s hy
        rw [this, coeff_smulS_real, mk_f3even, eta_c3, h1, PowerSeries.coeff_C]
      change evAt y _ = _
      rw [hL]
      by_cases hr0 : r = 0
      · subst hr0
        simp only [ite_true]
        show y = y * (dv 0 0 0).1 y
        rw [dv_zero_scalar_apply hy, mul_one]
      · by_cases hr1 : r = 1
        · subst hr1
          simp
        · simp [hr0, hr1]
    · have h0 : ∀ (g : Fn), g.1 y = 0 := fun g => g.zero_off hy
      rw [h0, h0]
  have hstart1 : (fun r => physFn 0 0 1 r) = LocalCalculus.serG G (xOp (dv 0 0 0)) :=
    LocalCalculus.smulS_cancel _ (by
      rw [LocalCalculus.constantCoeff_eta c3 c3_zero]; exact one_ne_zero) hphys
  have hfwd : ∀ n : ℕ, (kz 0 0 + ((n + 1 : ℕ) : ℝ)) * Rn 0 0 (n + 2) ≠ 0 := by
    intro n
    have hR : 0 < Rn 0 0 (n + 2) := by
      unfold Rn
      refine Rk_pos 0 0 _ ?_
      have : (0 : ℚ) < ((n + 2 : ℕ) : ℚ) := by positivity
      simpa using this
    have : 0 < kz 0 0 + ((n + 1 : ℕ) : ℝ) := by rw [hk]; positivity
    exact (mul_pos this hR).ne'
  have hGκ : ∀ r, G r (dv 0 0 0) = kap hα hβ r (dv 0 0 0) := by
    intro r
    cases r with
    | zero => rw [hG0, kap_zero hα hβ]
    | succ r =>
      rw [hGz r]
      refine Fn.ext' fun y => ?_
      by_cases hy : y ∈ Sx
      · show (0 : Fn).1 y = f3even 0 0 0 (r + 1) y / (dv 0 0 0).1 y * (dv 0 0 0).1 y
        rw [f3even_zero_zero_pos (r + 1) (by omega), zero_div, zero_mul]; rfl
      · show (0 : Fn).1 y = f3even 0 0 0 (r + 1) y / (dv 0 0 0).1 y * (dv 0 0 0).1 y
        rw [Fn.zero_off (dv 0 0 0) hy, mul_zero]; rfl
  have hu := LocalCalculus.rank_unique_of_two_starts xOp (0 : Polynomial ℝ) c3 c3_zero (TauM 0 0) (kz 0 0)
    (Rn 0 0) hfwd (Φ := physFn 0 0) (Φ' := fun n => LocalCalculus.serG G (dv 0 0 n))
    (fun n => physFn_rankDefect hα hβ (n + 1))
    (fun n => LocalCalculus.local_calculus_ranks xOp _ (0 : Polynomial ℝ) c3 c3_zero G hG0 (TauM 0 0)
      (kz 0 0) (Rn 0 0) (dv 0 0) (Hop_dv 0 0) (dv_rec 0 0) hGB (n + 1))
    (by
      rw [physFn_zero_eq_kap hα hβ]
      funext r
      show kap hα hβ r (dv 0 0 0) = G r (dv 0 0 0)
      rw [hGκ r])
    (by
      show (fun r => physFn 0 0 1 r) = fun r => G r (dv 0 0 1)
      rw [hstart1, dv_one_scalar]; rfl)
  intro n r y hy
  have := congrFun (congrFun hu n) r
  rw [← physFn_apply (M := 0) (σ := 0) n r hy, this]
  rfl

/-- **`M = σ = 0`: the all-order operators with `ψ_{2r} = 0`** (`prop:localcalculus` (c), `eq:3jJoperator`,
`thm:3jallorderlocal`).  There are operators `𝒢_r` (`𝒢_0 = I`), left-normal with rational coefficients
(`LN DOp Crat`), `[x, 𝒢_{r+1}] = 𝖡_{r+1}` (`eq:3jB2r`, `q = 0`, `e_s = c_s`, `Σ = τ = 0`), such that for every
`r` the operator `𝖡_{r+1}` has a left-normal representation `∑_{j ≤ J} b_j ∂^j` with rational `b_j` and
`𝒢_{r+1} = -∑_j b_j ∂^{j+1}/(j+1)` (the paper's `𝒥(𝖡_{r+1})`, *no multiplier*), and
`𝒢_r d^n_{00} = f_{2r}^{(n)}` on `(-1,1)` at every rank `n`. -/
theorem allorder_operators_zero_psi :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Crat) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0) G r) ∧
      (∀ r, ∃ (J : ℕ) (b : ℕ → End ℝ Fn), (∀ j, b j ∈ Crat) ∧
        Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0) G r = leftNormal DOp b J ∧
        G (r + 1) = Jop DOp b J) ∧
      ∀ n r, ∀ y ∈ Sx, (G r (dv 0 0 n)).1 y = f3even 0 0 n r y := by
  obtain ⟨G, hG0, hGm, hGB, hGJ⟩ := exists_solution_canonical (D := DOp) (C := Crat) (x := xOp)
    DOp_xOp (fun c hc => comm_x_Crat hc) (fun c hc => comm_Crat hc) xOp_mem_Crat
    (Hop_mem_LN_rat (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0)
  have hGz : ∀ r, G (r + 1) (dv 0 0 0) = 0 := by
    intro r
    obtain ⟨J, b, -, -, hJ⟩ := hGJ r
    rw [hJ]
    unfold Jop
    rw [LinearMap.neg_apply, LinearMap.sum_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun j _ => ?_)
    rw [LinearMap.smul_apply, Module.End.mul_apply, pow_succ, Module.End.mul_apply, DOp_dv_scalar]
    simp
  exact ⟨G, hG0, hGm, hGB, hGJ, zero_ident G hG0 hGB hGz⟩

end FormalResearch.Racah.LocalCalculus.Fun

/-- info: 'FormalResearch.Racah.LocalCalculus.exists_solution_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.exists_solution_canonical

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.zero_ident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.zero_ident

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_zero_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_zero_psi

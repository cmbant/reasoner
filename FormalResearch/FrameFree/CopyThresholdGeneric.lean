import Mathlib
import FormalResearch.FrameFree.CopyThresholdMain

/-!
# The generic threshold: separation fails only on a closed nowhere dense set (Paper P, `thm:copythreshold` (b))

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (no hypothesis, no new axiom).

`BadSet π k` is the set of vectors `ψ` whose `K_π`-twirls of `ψ^{⊗k}` and `(Θψ)^{⊗k}` coincide.  By the
slot-permutation criterion it is the common zero set of the continuous functions `Im Tr(P_s ψ^{⊗k})`, hence
closed (`isClosed_badSet`).  If one vector `ψ₁` is not in it, its interior is empty (`interior_badSet_eq_empty`):
along the line `ψ₀ + t(ψ₁ - ψ₀)` the difference `Tr(P_s ·) - Tr(P_{s⁻¹} ·) = 2i Im Tr(P_s ·)` is a complex
polynomial in `t` (`wordPoly`), which cannot vanish on an interval and yet be non-zero at `t = 1`.

* `generic_threshold`: if `k₀ = k_*(π)` (`IsLeast (VisibleCopies π) k₀`), there is a closed nowhere dense set `N`
  of vectors such that every `ψ ∉ N` has `k_*(ψ, π) = k₀`: its twirls differ at `k₀` and coincide for all
  `j < k₀`.  (The "coincide for `j < k₀`" half holds for *every* `ψ`.)  Combined with
  `CopyThresholdMain`/`CopyThresholdThree` this gives the genericity clause for the cases `b ≥ 3` (`k₀ = 1`),
  `b = 2` (`k₀ = 2`) and independent frames with `n ≥ 4` (`k₀ = 3`).  The null-set statement ("measure zero")
  is not formalised.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate Polynomial

namespace FormalResearch.FrameFree.Twirls

variable {α κ γ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  [Fintype γ] [DecidableEq γ]

/-- The vectors whose twirls of `ψ^{⊗k}` and `(Θψ)^{⊗k}` coincide. -/
def BadSet (π : α → κ) (k : ℕ) : Set ((α → Fin 2) → ℂ) :=
  {ψ | TwirlsCoincide π (Fin k) (pureOp ψ)}

theorem continuous_wordVal (s : Equiv.Perm (α × γ)) :
    Continuous fun ψ : (α → Fin 2) → ℂ => wordVal γ s (pureOp ψ) := by
  have : (fun ψ : (α → Fin 2) → ℂ => wordVal γ s (pureOp ψ)) = fun ψ =>
      ∑ X : α × γ → Fin 2, ∏ c : γ, ψ (fun a => X (s (a, c))) * conj (ψ (col X c)) :=
    funext fun ψ => wordVal_pure s ψ
  rw [this]
  fun_prop

theorem isClosed_badSet (π : α → κ) (k : ℕ) : IsClosed (BadSet π k) := by
  have : BadSet π k = ⋂ s : Equiv.Perm (α × Fin k), ⋂ (_ : BlockPres π s),
      {ψ | (wordVal (Fin k) s (pureOp ψ)).im = 0} := by
    ext ψ
    simp only [BadSet, Set.mem_setOf_eq, twirlsCoincide_iff, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq (Complex.continuous_im.comp (continuous_wordVal s)) continuous_const

/-! ### The word value along a line is a polynomial -/

/-- The polynomial `t ↦ Tr(P_s (ψ₀ + tΔ)^{⊗k}-state)`. -/
noncomputable def wordPoly (s : Equiv.Perm (α × γ)) (ψ₀ Δ : (α → Fin 2) → ℂ) : ℂ[X] :=
  ∑ Y : α × γ → Fin 2, ∏ c : γ,
    (C (ψ₀ (fun a => Y (s (a, c)))) + X * C (Δ (fun a => Y (s (a, c))))) *
      (C (conj (ψ₀ (col Y c))) + X * C (conj (Δ (col Y c))))

theorem eval_wordPoly (s : Equiv.Perm (α × γ)) (ψ₀ Δ : (α → Fin 2) → ℂ) (t : ℝ) :
    (wordPoly s ψ₀ Δ).eval (t : ℂ) = wordVal γ s (pureOp fun x => ψ₀ x + (t : ℂ) * Δ x) := by
  rw [wordVal_pure, wordPoly, eval_finset_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [eval_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp [col, Complex.conj_ofReal]
  ring

theorem interior_badSet_eq_empty (π : α → κ) (k : ℕ) {ψ₁ : (α → Fin 2) → ℂ} (h : ψ₁ ∉ BadSet π k) :
    interior (BadSet π k) = ∅ := by
  by_contra hne
  obtain ⟨ψ₀, hψ₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  have h1 : ¬ ∀ s : Equiv.Perm (α × Fin k), BlockPres π s → (wordVal (Fin k) s (pureOp ψ₁)).im = 0 :=
    fun hh => h ((twirlsCoincide_iff π _).2 hh)
  push Not at h1
  obtain ⟨s, hs, him⟩ := h1
  set Δ : (α → Fin 2) → ℂ := ψ₁ - ψ₀ with hΔ
  have hcont : Continuous fun t : ℝ => (fun x => ψ₀ x + (t : ℂ) * Δ x : (α → Fin 2) → ℂ) := by
    fun_prop
  have hopen : IsOpen {t : ℝ | (fun x => ψ₀ x + (t : ℂ) * Δ x : (α → Fin 2) → ℂ) ∈
      interior (BadSet π k)} := isOpen_interior.preimage hcont
  have h0 : (0 : ℝ) ∈ {t : ℝ | (fun x => ψ₀ x + (t : ℂ) * Δ x : (α → Fin 2) → ℂ) ∈
      interior (BadSet π k)} := by simpa using hψ₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  set R : ℂ[X] := wordPoly s ψ₀ Δ - wordPoly s⁻¹ ψ₀ Δ with hR
  have hval : ∀ t : ℝ, R.eval (t : ℂ) = wordVal (Fin k) s (pureOp fun x => ψ₀ x + (t : ℂ) * Δ x) -
      conj (wordVal (Fin k) s (pureOp fun x => ψ₀ x + (t : ℂ) * Δ x)) := fun t => by
    rw [hR, eval_sub, eval_wordPoly, eval_wordPoly, conj_wordVal _ (pureOp_isHermitian _)]
  have hroot : ∀ t : ℝ, t ∈ Set.Ioo (-ε) ε → R.IsRoot (t : ℂ) := by
    intro t ht
    have hmem : (fun x => ψ₀ x + (t : ℂ) * Δ x : (α → Fin 2) → ℂ) ∈ interior (BadSet π k) :=
      hball (by simpa [abs_lt] using ht)
    have hbad := interior_subset hmem
    have := (twirlsCoincide_iff π _).1 hbad s hs
    show R.eval (t : ℂ) = 0
    rw [hval, Complex.sub_conj, this]
    simp
  have hR0 : R = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot R ?_
    have hinf : (Complex.ofReal '' Set.Ioo (-ε) ε).Infinite :=
      (Set.Ioo_infinite (by linarith)).image Complex.ofReal_injective.injOn
    refine hinf.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hroot t ht
  have h1' := hval 1
  rw [hR0, eval_zero] at h1'
  have hψ : (fun x => ψ₀ x + ((1 : ℝ) : ℂ) * Δ x : (α → Fin 2) → ℂ) = ψ₁ := by
    funext x
    simp [hΔ]
  rw [hψ, Complex.sub_conj] at h1'
  have : (2 * Complex.I * ((wordVal (Fin k) s (pureOp ψ₁)).im : ℂ)) = 0 := by simpa using h1'.symm
  have h2 : (wordVal (Fin k) s (pureOp ψ₁)).im = 0 := by
    have := mul_eq_zero.1 this
    rcases this with h | h
    · exact absurd h (by simp)
    · exact_mod_cast h
  exact him h2

/-- **The generic threshold.**  If `k₀` is the least copy number at which some state separates the twirls, then
off a closed nowhere dense set of vectors `ψ` the twirls differ at `k₀` and coincide below `k₀`. -/
theorem generic_threshold (π : α → κ) {k₀ : ℕ} (h : IsLeast (VisibleCopies π) k₀) :
    ∃ N : Set ((α → Fin 2) → ℂ), IsClosed N ∧ interior N = ∅ ∧ IsNowhereDense N ∧
      ∀ ψ, ψ ∉ N → ¬ TwirlsCoincide π (Fin k₀) (pureOp ψ) ∧
        ∀ j < k₀, TwirlsCoincide π (Fin j) (pureOp ψ) := by
  obtain ⟨ψ₁, -, hψ₁⟩ := h.1
  have hint : interior (BadSet π k₀) = ∅ := interior_badSet_eq_empty π k₀ hψ₁
  refine ⟨BadSet π k₀, isClosed_badSet π k₀, hint, (isClosed_badSet π k₀).isNowhereDense_iff.2 hint,
    fun ψ hψ => ⟨hψ, fun j hj => ?_⟩⟩
  by_contra hc
  obtain ⟨ψ', hn, hψ'⟩ := exists_unit_differ π ψ hc
  exact absurd (h.2 ⟨ψ', hn, hψ'⟩) (by omega)

end FormalResearch.FrameFree.Twirls

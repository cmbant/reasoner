module

public import FormalResearch.FourQubitEntropy.GOData.GOConst
public import FormalResearch.FourQubitEntropy.GOData.GOSpec
public import FormalResearch.FourQubitEntropy.GOGlue.Cons

/-!
# GO glue: the generated constraint matrices are the slice-side ones (data check)

`consCheck` (one `native_decide`, ordinary computable list functions) verifies, for each of the 64
generated matrices `cons[c]`, that `36 L_c · cons[c] = mapDen · S_c` entrywise as sorted sparse polynomials,
where `(k_c, L_c, S_c) = (consSpec[c]).mat` is the transcription of the slice-side matrix
(`GOGlue/Cons.lean`), and the rational side conditions `CSpec.ok` of the rays and lower frames.
`cons_psd`: at a slice point with `SliceConstraints`, every `cons[c]` is positive semidefinite.
Claim class: proved, modulo the `native_decide` step `consCheck_true` (one of the three data checks of the
global-overlap certificate: `GOProbe.check_all`, `identCheck_true`, `consCheck_true`).
-/

@[expose] public section


open Finset

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe

set_option maxRecDepth 100000

/-- `36 L · M = mapDen · S` entrywise (`mapDen = 36 · map_den`, the generated entries are `map_den` times the polynomial matrix) on the `k × k` block, `M` of height `k`. -/
def consMatch (M : List (List SP)) (k L : ℕ) (S : List (List SP)) : Bool :=
  (M.length == k) && (List.range k).all fun i => (List.range k).all fun j =>
    GOProbe.eqSP (scaleSP ((36 * L : ℕ) : ℤ) (entry M i j)) (scaleSP (GOProbe.mapDen : ℤ) (entry S i j))

def consCheck : Bool :=
  (consSpec.length == GOProbe.cons.length) && (List.range GOProbe.cons.length).all fun c =>
    consMatch (GOProbe.cons.getD c []) (consSpec.getD c CSpec.sos).mat.1 (consSpec.getD c CSpec.sos).mat.2.1
      (consSpec.getD c CSpec.sos).mat.2.2 && decide (consSpec.getD c CSpec.sos).ok

theorem consCheck_true : consCheck = true := by native_decide

theorem psd_of_match {M S : List (List SP)} {k L : ℕ} (hL : 0 < L) (h : consMatch M k L S = true)
    (y : ℕ → ℝ) (hS : ∀ w : ℕ → ℝ, 0 ≤ ∑ a ∈ range k, ∑ c ∈ range k, w a * ev y (entry S a c) * w c) :
    Psd y M := by
  unfold consMatch at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, h⟩ := h
  intro v
  unfold Bf
  rw [hlen]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hm : ∀ a ∈ range k, ∀ c ∈ range k, Mev y M a c = (GOProbe.mapDen : ℝ) / (36 * L) * ev y (entry S a c) := by
    intro a ha c hc
    have e := GOProbe.eqSP_sound _ _ (h a (Finset.mem_range.1 ha) c (Finset.mem_range.1 hc))
    have e2 := congrArg (ev y) e
    rw [ev_scaleSP, ev_scaleSP] at e2
    unfold Mev
    push_cast at e2
    field_simp
    linarith
  have : ∑ a ∈ range k, ∑ c ∈ range k, v a * Mev y M a c * v c =
      (GOProbe.mapDen : ℝ) / (36 * L) * ∑ a ∈ range k, ∑ c ∈ range k, v a * ev y (entry S a c) * v c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hm a ha c hc]; ring
  rw [this]
  exact mul_nonneg (by positivity) (hS v)

theorem cons_psd (h : consCheck = true) (y : ℕ → ℝ) (hc : SliceConstraints (restr y)) :
    ∀ c < GOProbe.cons.length, Psd y (GOProbe.cons.getD c []) := by
  unfold consCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro c hcl
  obtain ⟨-, h⟩ := h
  obtain ⟨hm, hok⟩ := h c hcl
  set cs := consSpec.getD c CSpec.sos
  exact psd_of_match cs.den_pos hm y (fun w => CSpec.psd y cs hok hc w)

end FormalResearch.FourQubitEntropy.GO

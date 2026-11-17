module

public import FormalResearch.Special.LatticeTail

/-!
# From data on `[-X, X]` to `LevelData`

The paper's `Θ` is only defined on `[-X, X]`.  `exists_levelData` extends `t = Θ/π` to all of `ℝ`
(by `t∘clamp + (t₀ - t₀∘clamp)`, which stays `ε`-close to `t₀`), so that it can be used with `LevelData`
(which asks for a continuous `t` and closeness on `[-X-1, X+1]`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex

lemma exists_levelData {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} (h : CalPhase τ0 X y0 m M K)
    (hglob : Continuous (realPhase τ0)) {t : ℝ → ℝ} (hc : ContinuousOn t (Icc (-X) X))
    (hmono : StrictMonoOn t (Icc (-X) X)) (hε : 0 ≤ ε)
    (hclose : ∀ s ∈ Icc (-X) X, |t s - realPhase τ0 s| ≤ ε) {S : Finset ℝ}
    (hS : ∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, t x = n) :
    ∃ t' : ℝ → ℝ, LevelData τ0 X y0 m M K ε t' S ∧ ∀ s ∈ Icc (-X) X, t' s = t s := by
  have hX := h.hX
  set cl : ℝ → ℝ := fun s => max (-X) (min s X) with hcl
  have hclc : Continuous cl := by simp only [hcl]; fun_prop
  have hclmem : ∀ s, cl s ∈ Icc (-X) X := fun s => by
    simp only [hcl]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  have hclid : ∀ s ∈ Icc (-X) X, cl s = s := fun s hs => by
    simp only [hcl]
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hclabs : ∀ s : ℝ, |s| ≤ X + 1 → |cl s| ≤ X + 1 := fun s _ => by
    have := hclmem s
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hid : ∀ s ∈ Icc (-X) X, t (cl s) + (realPhase τ0 s - realPhase τ0 (cl s)) = t s := fun s hs => by
    rw [hclid s hs]; ring
  refine ⟨fun s => t (cl s) + (realPhase τ0 s - realPhase τ0 (cl s)), ⟨h, hε, ?_, ?_, ?_, ?_⟩, hid⟩
  · exact (hc.comp_continuous hclc hclmem).add (hglob.sub (hglob.comp hclc))
  · intro x hx y hy hxy
    show t (cl x) + (realPhase τ0 x - realPhase τ0 (cl x)) < t (cl y) + (realPhase τ0 y - realPhase τ0 (cl y))
    rw [hid x hx, hid y hy]; exact hmono hx hy hxy
  · intro s _
    have := hclmem (s)
    have h2 := hclose (cl s) (hclmem s)
    have : t (cl s) + (realPhase τ0 s - realPhase τ0 (cl s)) - realPhase τ0 s =
        t (cl s) - realPhase τ0 (cl s) := by ring
    show |t (cl s) + (realPhase τ0 s - realPhase τ0 (cl s)) - realPhase τ0 s| ≤ ε
    rw [this]; exact h2
  · intro x
    rw [hS x]
    constructor
    · rintro ⟨hx, n, hn⟩; exact ⟨hx, n, by rw [hid x hx]; exact hn⟩
    · rintro ⟨hx, n, hn⟩; exact ⟨hx, n, by rw [← hid x hx]; exact hn⟩

end FormalResearch.Special.Lattice

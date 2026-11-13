module

public import FormalResearch.Wigner.Defs

/-!
# Shift ratios of the triangle coefficient

For `IsTri` triples, `triSq` changes by an explicit rational factor when the first argument is
shifted by one.  These are the identities behind the passage from the rational recurrence of the
Racah sum to DLMF 34.5.11–34.5.13, where `E(j₁)` absorbs the square roots.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma isNat_add_one {x : ℚ} (h : IsNat x) : IsNat (x + 1) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by push_cast; ring⟩

/-- Raising the first argument:
`Δ²(f+1,b,c) (b+c-f)(f+b+c+2) = (f+1+b-c)(f+1-b+c) Δ²(f,b,c)`. -/
lemma triSq_succ_mul {f b c : ℚ} (hf : IsTri f b c) (hf1 : IsTri (f + 1) b c) :
    triSq (f + 1) b c * (((b : ℝ) + c - f) * ((f : ℝ) + b + c + 2)) =
      (((f : ℝ) + 1 + b - c) * ((f : ℝ) + 1 - b + c)) * triSq f b c := by
  obtain ⟨h1, h2, -⟩ := hf
  obtain ⟨-, -, h3'⟩ := hf1
  have e1 : fq (f + 1 + b - c) = ((f : ℝ) + b - c + 1) * fq (f + b - c) := by
    have := fq_succ h1
    rw [show f + b - c + 1 = f + 1 + b - c by ring] at this
    rw [this]; push_cast; ring
  have e2 : fq (f + 1 - b + c) = ((f : ℝ) - b + c + 1) * fq (f - b + c) := by
    have := fq_succ h2
    rw [show f - b + c + 1 = f + 1 - b + c by ring] at this
    rw [this]; push_cast; ring
  have e3 : fq (-f + b + c) = (-(f : ℝ) + b + c) * fq (-(f + 1) + b + c) := by
    have := fq_succ h3'
    rw [show -(f + 1) + b + c + 1 = -f + b + c by ring] at this
    rw [this]; push_cast; ring
  have e4 : ifa (f + b + c + 1) = ((f : ℝ) + b + c + 2) * ifa (f + 1 + b + c + 1) := by
    have := ifa_shift (f + b + c + 1)
    rw [show f + b + c + 1 + 1 = f + 1 + b + c + 1 by ring] at this
    rw [← this]; push_cast; ring
  unfold triSq
  rw [e1, e2, e3, e4]
  ring

/-- Lowering the first argument:
`Δ²(f-1,b,c) (f+b-c)(f-b+c) = (b+c-f+1)(f+b+c+1) Δ²(f,b,c)`. -/
lemma triSq_pred_mul {f b c : ℚ} (hf : IsTri f b c) (hf1 : IsTri (f - 1) b c) :
    triSq (f - 1) b c * (((f : ℝ) + b - c) * ((f : ℝ) - b + c)) =
      (((b : ℝ) + c - f + 1) * ((f : ℝ) + b + c + 1)) * triSq f b c := by
  have h := triSq_succ_mul hf1 (by rw [sub_add_cancel]; exact hf)
  rw [sub_add_cancel] at h
  push_cast at h
  linarith

end FormalResearch.Wigner

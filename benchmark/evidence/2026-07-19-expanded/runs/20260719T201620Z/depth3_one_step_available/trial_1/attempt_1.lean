import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth3

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 3. -/
axiom provided_step (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {x | N x.1 < x.2}
      add_mem' := by
        intro x y hx hy
        exact lt_of_le_of_lt (N_add x.1 y.1) (add_lt_add hx hy)
      smul_mem' := by
        intro c hc x hx
        simpa [N_hom c hc, smul_eq_mul] using
          (mul_lt_mul_of_pos_left hx hc) }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toLinearMap :=
        { toFun := fun x => x.1.2 - f ⟨x.1.1, x.2.1⟩
          map_add' := by
            intro x y
            simp
            ring
          map_smul' := by
            intro c x
            simp [smul_eq_mul]
            ring } }
  have hF : ∀ x : F.domain, (x : E × ℝ) ∈ s → 0 ≤ F x := by
    intro x hx
    change N x.1.1 < x.1.2 at hx
    change 0 ≤ x.1.2 - f ⟨x.1.1, x.2.1⟩
    exact sub_nonneg.mpr (le_trans (hf ⟨x.1.1, x.2.1⟩) hx.le)
  obtain ⟨G, hFG, hG, hmax⟩ := LinearPMap.exists_maximal F hF
  have hDenseF : ∀ y, ∃ x : F.domain, (x : E × ℝ) + y ∈ s := by
    intro y
    refine ⟨⟨(0, N y.1 - y.2 + 1), ?_⟩, ?_⟩
    · simp [F]
    · change N (0 + y.1) < N y.1 - y.2 + 1 + y.2
      simp
  have hDenseG : ∀ y, ∃ x : G.domain, (x : E × ℝ) + y ∈ s := by
    intro y
    obtain ⟨x, hx⟩ := hDenseF y
    refine ⟨⟨x, hFG.1 x.2⟩, ?_⟩
    simpa using hx
  have htop : G.domain = ⊤ := by
    by_contra hne
    obtain ⟨G', hlt, hG'⟩ := provided_step s G hG hDenseG hne
    obtain ⟨x, hx⟩ := hmax G' hlt
    exact hx (hG' x)
  let incl : (E × ℝ) →ₗ[ℝ] G.domain :=
    { toFun := fun x => ⟨x, by rw [htop]; exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let L : (E × ℝ) →ₗ[ℝ] ℝ := G.toLinearMap.comp incl
  have hvertical (t : ℝ) : L (0, t) = t := by
    let z : F.domain := ⟨(0, t), by simp [F]⟩
    have hz := hFG.2 z
    simpa [L, incl, F] using hz
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -L (x, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp [smul_eq_mul] }
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : F.domain := ⟨(x, 0), by simp [F]⟩
    have hz := hFG.2 z
    have hz' : L (x, 0) = -f x := by
      simpa [L, incl, F] using hz
    simp [g, hz']
  · intro x
    by_contra hx
    have hx' : N x < g x := lt_of_not_ge hx
    let t : ℝ := (N x + g x) / 2
    have hNt : N x < t := by
      dsimp [t]
      linarith
    have htg : t < g x := by
      dsimp [t]
      linarith
    have hsxt : (x, t) ∈ s := hNt
    have hpos : 0 ≤ L (x, t) := by
      have hmem : (x, t) ∈ G.domain := by
        rw [htop]
        exact Submodule.mem_top
      simpa [L, incl] using hG ⟨(x, t), hmem⟩ hsxt
    have hsplit : L (x, t) = L (x, 0) + L (0, t) := by
      rw [show (x, t) = (x, 0) + (0, t) by ext <;> simp, map_add]
    rw [hsplit, hvertical] at hpos
    change g x = -L (x, 0) at *
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth3

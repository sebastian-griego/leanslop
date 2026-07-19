import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 1. -/
axiom provided_riesz_extension (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x

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
  let s : PointedCone ℝ (ℝ × E) :=
    { carrier := {p | N (-p.2) ≤ p.1}
      smul_mem' := by
        intro c hc p hp
        change N (-p.2) ≤ p.1 at hp
        change N (-(c • p.2)) ≤ c * p.1
        rw [← smul_neg, N_hom c hc]
        exact mul_le_mul_of_nonneg_left hp hc.le }
  let D : Submodule ℝ (ℝ × E) :=
    Submodule.prod (⊤ : Submodule ℝ ℝ) f.domain
  let F : (ℝ × E) →ₗ.[ℝ] ℝ :=
    { domain := D
      toLinearMap :=
        { toFun := fun p => p.1.1 + f ⟨p.1.2, p.2.2⟩
          map_add' := by
            intro x y
            change
              (x.1.1 + y.1.1) +
                  f (⟨x.1.2, x.2.2⟩ + ⟨y.1.2, y.2.2⟩) =
                (x.1.1 + f ⟨x.1.2, x.2.2⟩) +
                  (y.1.1 + f ⟨y.1.2, y.2.2⟩)
            rw [map_add]
            ring
          map_smul' := by
            intro c x
            change
              c * x.1.1 + f (c • ⟨x.1.2, x.2.2⟩) =
                c * (x.1.1 + f ⟨x.1.2, x.2.2⟩)
            rw [map_smul]
            change
              c * x.1.1 + c * f ⟨x.1.2, x.2.2⟩ =
                c * (x.1.1 + f ⟨x.1.2, x.2.2⟩)
            ring } }
  obtain ⟨G, hG, hpos⟩ :=
    provided_riesz_extension (E := ℝ × E) s F
      (by
        intro x hx
        change N (-x.1.2) ≤ x.1.1 at hx
        change 0 ≤ x.1.1 + f ⟨x.1.2, x.2.2⟩
        have hn := hf (-⟨x.1.2, x.2.2⟩)
        simp only [Submodule.coe_neg, map_neg] at hn
        linarith)
      (by
        intro y
        let z : F.domain :=
          ⟨(N (-y.2) - y.1, 0), by
            change (N (-y.2) - y.1, 0) ∈ D
            exact ⟨Submodule.mem_top, f.domain.zero_mem⟩⟩
        refine ⟨z, ?_⟩
        change N (-(z.1.2 + y.2)) ≤ z.1.1 + y.1
        dsimp [z]
        simpa using (le_refl (N (-y.2))))
  let ι : E →ₗ[ℝ] (ℝ × E) :=
    { toFun := fun x => (0, x)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  refine ⟨G.comp ι, ?_, ?_⟩
  · intro x
    let z : F.domain :=
      ⟨(0, (x : E)), by
        change (0, (x : E)) ∈ D
        exact ⟨Submodule.mem_top, x.2⟩⟩
    have hz := hG z
    change G (0, (x : E)) = 0 + f x at hz
    change G (0, (x : E)) = f x
    simpa using hz
  · intro x
    change G (0, x) ≤ N x
    have hs : (N x, -x) ∈ s := by
      change N (-(-x)) ≤ N x
      simp
    have hp := hpos (N x, -x) hs
    let z : F.domain :=
      ⟨(N x, (0 : E)), by
        change (N x, (0 : E)) ∈ D
        exact ⟨Submodule.mem_top, f.domain.zero_mem⟩⟩
    have hz := hG z
    have hscalar : G (N x, 0) = N x := by
      change G (N x, 0) = N x + f (0 : f.domain) at hz
      simpa using hz
    have hneg : G (0, -x) = -G (0, x) := by
      simpa using G.map_neg (0, x)
    have hsplit : (N x, -x) = (N x, 0) + (0, -x) := by
      simp
    rw [hsplit, map_add, hscalar, hneg] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth1

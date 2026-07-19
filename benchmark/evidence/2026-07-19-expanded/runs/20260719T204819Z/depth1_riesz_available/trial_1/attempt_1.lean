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
  have hN0 : N (0 : E) = 0 := by
    have h : N (0 : E) = 2 * N (0 : E) := by
      simpa using N_hom (2 : ℝ) (by norm_num) (0 : E)
    linarith
  let s : PointedCone ℝ (ℝ × E) :=
    { carrier := {p | N p.2 ≤ p.1}
      zero_mem' := by
        simpa using le_of_eq hN0
      add_mem' := by
        rintro ⟨a, x⟩ ⟨b, y⟩ hx hy
        exact (N_add x y).trans (add_le_add hx hy)
      smul_mem' := by
        intro c hc
        rintro ⟨a, x⟩ hx
        rcases hc.eq_or_lt with rfl | hc
        · simp [hN0]
        · simpa [N_hom c hc x] using mul_le_mul_of_nonneg_left hx hc }
  let F : (ℝ × E) →ₗ.[ℝ] ℝ :=
    { domain := (⊤ : Submodule ℝ ℝ).prod f.domain
      toLinearMap :=
        { toFun := fun x => x.1.1 - f ⟨x.1.2, x.2.2⟩
          map_add' := by
            intro x y
            simp
            ring
          map_smul' := by
            intro c x
            simp
            ring } }
  have hnonneg :
      ∀ x : F.domain, (x : ℝ × E) ∈ s → 0 ≤ F x := by
    intro x hx
    change N x.1.2 ≤ x.1.1 at hx
    change 0 ≤ x.1.1 - f ⟨x.1.2, x.2.2⟩
    have hfx := hf ⟨x.1.2, x.2.2⟩
    linarith
  have hdense :
      ∀ y, ∃ x : F.domain, (x : ℝ × E) + y ∈ s := by
    rintro ⟨a, y⟩
    refine ⟨⟨(N y - a, 0), by simp [F]⟩, ?_⟩
    change N ((0 : E) + y) ≤ (N y - a) + a
    simpa
  obtain ⟨G, hG, hpos⟩ :=
    provided_riesz_extension s F hnonneg hdense
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -G (0, x)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    change -G (0, (x : E)) = f x
    have h :=
      hG (⟨(0, (x : E)), by simp [F]⟩ : F.domain)
    simpa [F] using congrArg Neg.neg h
  · intro x
    change -G (0, x) ≤ N x
    have hp : 0 ≤ G (N x, x) :=
      hpos (N x, x) (by
        change N x ≤ N x
        exact le_rfl)
    have hbase :
        G (N x, 0) = N x := by
      have h :=
        hG (⟨(N x, 0), by simp [F]⟩ : F.domain)
      simpa [F] using h
    have hadd :
        G (N x, x) = G (N x, 0) + G (0, x) := by
      simpa using G.map_add (N x, 0) (0, x)
    rw [hadd, hbase] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth1

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

lemma sublinear_zero (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x) :
    N (0 : E) = 0 := by
  have h : N (0 : E) = (2 : ℝ) * N (0 : E) := by
    simpa using N_hom 2 (by positivity) (0 : E)
  linarith

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  have hN0 : N (0 : E) = 0 := sublinear_zero N N_hom
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {p : E × ℝ | N p.1 ≤ p.2}
      zero_mem' := by
        simpa [hN0]
      add_mem' := by
        intro a b ha hb
        exact le_trans (N_add a.1 b.1) (by linarith)
      smul_mem' := by
        intro c hc a ha
        rcases lt_or_eq_of_le hc with hlt | rfl
        · rw [N_hom c hlt a.1]
          nlinarith
        · simpa [hN0] }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toFun :=
        { toFun := fun u => u.1.2 - f ⟨u.1.1, u.2.1⟩
          map_add' := by
            intro a b
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          map_smul' := by
            intro c u
            simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] } }
  obtain ⟨G, hGext, hGnonneg⟩ :=
    provided_riesz_extension s F
      (by
        intro u hu
        have hfu : f ⟨u.1.1, u.2.1⟩ ≤ N u.1.1 := hf ⟨u.1.1, u.2.1⟩
        have : f ⟨u.1.1, u.2.1⟩ ≤ u.1.2 := le_trans hfu hu
        have hnon : 0 ≤ u.1.2 - f ⟨u.1.1, u.2.1⟩ := sub_nonneg.mpr this
        simpa [F] using hnon)
      (by
        intro y
        refine ⟨⟨((0 : E), N y.1 - y.2), by simp⟩, ?_⟩
        change N y.1 ≤ (N y.1 - y.2) + y.2
        linarith)
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -G (x, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp [mul_comm, mul_left_comm, mul_assoc] }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hx0 : G ((x : E), (0 : ℝ)) = -f x := by
      simpa [F] using hGext ⟨((x : E), (0 : ℝ)), by simp [x.property]⟩
    simpa [g, hx0]
  · intro x
    have h01 : G ((0 : E), (1 : ℝ)) = 1 := by
      simpa [F] using hGext ⟨((0 : E), (1 : ℝ)), by simp⟩
    have hpos : 0 ≤ G (x, N x) := by
      apply hGnonneg
      change N x ≤ N x
      exact le_rfl
    have hdecomp : G (x, N x) = G (x, 0) + N x := by
      calc
        G (x, N x) = G ((x, 0) + (0, N x)) := by rfl
        _ = G (x, 0) + G (0, N x) := by simp
        _ = G (x, 0) + N x * G (0, 1) := by
          rw [show ((0 : E), N x) = N x • ((0 : E), (1 : ℝ)) by ext <;> simp]
          simp
        _ = G (x, 0) + N x := by simpa [h01]
    have hle : -G (x, 0) ≤ N x := by
      have : 0 ≤ G (x, 0) + N x := by simpa [hdecomp] using hpos
      linarith
    simpa [g] using hle


#print axioms tested_hahn_banach

end Depth1

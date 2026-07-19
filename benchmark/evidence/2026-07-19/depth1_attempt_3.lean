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
  let s : PointedCone ℝ (E × ℝ) where
    carrier := {p : E × ℝ | N p.1 ≤ p.2}
    zero_mem' := by
      simpa [hN0]
    add_mem' := by
      intro a b ha hb
      change N (a.1 + b.1) ≤ a.2 + b.2
      exact le_trans (N_add a.1 b.1) (add_le_add ha hb)
    smul_mem' := by
      intro c x hx
      change N ((c : ℝ) • x.1) ≤ (c : ℝ) * x.2
      rcases eq_or_lt_of_le c.2 with hc0 | hcpos
      · simp [hc0, hN0]
      · rw [N_hom (c : ℝ) hcpos x.1]
        nlinarith [hx, c.2]
  let fstF : f.domain.prod ⊤ →ₗ[ℝ] f.domain where
    toFun := fun u => ⟨(u : E × ℝ).1, u.2.1⟩
    map_add' := by
      intro u v
      ext
      rfl
    map_smul' := by
      intro c u
      ext
      rfl
  let sndF : f.domain.prod ⊤ →ₗ[ℝ] ℝ where
    toFun := fun u => (u : E × ℝ).2
    map_add' := by
      intro u v
      rfl
    map_smul' := by
      intro c u
      rfl
  let F : (E × ℝ) →ₗ.[ℝ] ℝ where
    domain := f.domain.prod ⊤
    toFun := sndF - f.toFun.comp fstF
  obtain ⟨G, hGext, hGnonneg⟩ :=
    provided_riesz_extension s F
      (by
        intro u hu
        have hfu : f (fstF u) ≤ N ((u : E × ℝ).1) := hf (fstF u)
        have hub : N ((u : E × ℝ).1) ≤ (u : E × ℝ).2 := hu
        have hle : f (fstF u) ≤ (u : E × ℝ).2 := le_trans hfu hub
        have hnon : 0 ≤ (u : E × ℝ).2 - f (fstF u) := sub_nonneg.mpr hle
        simpa [F, sndF, fstF] using hnon)
      (by
        intro y
        refine ⟨⟨(0 : E, N y.1 - y.2), ?_⟩, ?_⟩
        · exact ⟨f.domain.zero_mem, by simp⟩
        · change N (0 + y.1) ≤ (N y.1 - y.2) + y.2
          simp
          linarith)
  let i : E →ₗ[ℝ] E × ℝ where
    toFun := fun x => (x, 0)
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro c x
      rfl
  let g : E →ₗ[ℝ] ℝ := -(G.comp i)
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hx0 : G ((x : E), (0 : ℝ)) = -f x := by
      have h := hGext ⟨((x : E), (0 : ℝ)), ⟨x.2, by simp⟩⟩
      simpa [F, sndF, fstF] using h
    have hneg := congrArg Neg.neg hx0
    simpa [g, i] using hneg
  · intro x
    have h01 : G ((0 : E), (1 : ℝ)) = 1 := by
      have h := hGext ⟨((0 : E), (1 : ℝ)), ⟨f.domain.zero_mem, by simp⟩⟩
      simpa [F, sndF, fstF] using h
    have hpos : 0 ≤ G (x, N x) := by
      apply hGnonneg
      change N x ≤ N x
      rfl
    have hsmul : G ((0 : E), N x) = N x * G ((0 : E), (1 : ℝ)) := by
      simpa using G.map_smul (N x) ((0 : E), (1 : ℝ))
    have hdecomp : G (x, N x) = G ((x : E), (0 : ℝ)) + N x := by
      calc
        G (x, N x) = G (((x : E), (0 : ℝ)) + ((0 : E), N x)) := by rfl
        _ = G ((x : E), (0 : ℝ)) + G ((0 : E), N x) := by rw [map_add]
        _ = G ((x : E), (0 : ℝ)) + N x * G ((0 : E), (1 : ℝ)) := by rw [hsmul]
        _ = G ((x : E), (0 : ℝ)) + N x := by rw [h01]; ring
    have hle : -G ((x : E), (0 : ℝ)) ≤ N x := by
      have : 0 ≤ G ((x : E), (0 : ℝ)) + N x := by
        simpa [hdecomp] using hpos
      linarith
    simpa [g, i] using hle


#print axioms tested_hahn_banach

end Depth1

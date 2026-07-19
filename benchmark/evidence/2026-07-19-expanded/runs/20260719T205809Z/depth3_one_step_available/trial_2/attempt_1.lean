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
  let V := E × ℝ
  let s : PointedCone ℝ V :=
    { carrier := {x | N x.1 ≤ x.2}
      smul_mem' := by
        intro c hc x hx
        change N (c • x.1) ≤ c * x.2
        rw [N_hom c hc]
        exact mul_le_mul_of_nonneg_left hx (le_of_lt hc) }
  let D : Submodule ℝ V := f.domain.prod ⊤
  let F : V →ₗ.[ℝ] ℝ :=
    { domain := D
      toLinearMap :=
        { toFun := fun x => x.1.2 - f ⟨x.1.1, x.2.1⟩
          map_add' := by
            intro x y
            simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add,
              map_add, sub_add_sub_comm]
          map_smul' := by
            intro c x
            simp only [Submodule.coe_smul_of_tower, Prod.fst_smul, Prod.snd_smul,
              map_smul, smul_eq_mul, mul_sub] } }
  have hFpos : ∀ x : F.domain, (x : V) ∈ s → 0 ≤ F x := by
    intro x hx
    have hfx : f ⟨x.1.1, x.2.1⟩ ≤ N x.1.1 := hf ⟨x.1.1, x.2.1⟩
    change N x.1.1 ≤ x.1.2 at hx
    change 0 ≤ x.1.2 - f ⟨x.1.1, x.2.1⟩
    linarith
  let P : Set (V →ₗ.[ℝ] ℝ) :=
    {g | F ≤ g ∧ ∀ x : g.domain, (x : V) ∈ s → 0 ≤ g x}
  obtain ⟨G, hGP, hGmax⟩ := zorn_le_nonempty₀ P ⟨F, le_rfl, hFpos⟩ (by
    intro c h₁ h₂
    have hc : IsChain (· ≤ ·) c := by
      first | exact h₁ | exact h₂
    have hsub : c ⊆ P := by
      first | exact h₁ | exact h₂
    by_cases hne : c.Nonempty
    · let u := LinearPMap.sup c hc
      have hu : ∀ g ∈ c, g ≤ u := by
        intro g hg
        exact LinearPMap.le_sup hc hg
      refine ⟨u, ?_, ?_⟩
      · rcases hne with ⟨g₀, hg₀⟩
        refine ⟨(hsub hg₀).1.trans (hu g₀ hg₀), ?_⟩
        intro x hx
        have hxmem : ∃ g ∈ c, x.1 ∈ g.domain := by
          simpa [u, LinearPMap.sup] using x.2
        rcases hxmem with ⟨g, hgc, hxg⟩
        rcases LinearPMap.le_def.mp (hu g hgc) with ⟨hdom, hval⟩
        have hp := (hsub hgc).2 ⟨x.1, hxg⟩ hx
        have he := hval ⟨x.1, hxg⟩
        simpa using he ▸ hp
      · intro g hg
        exact hu g hg
    · refine ⟨F, ⟨le_rfl, hFpos⟩, ?_⟩
      intro g hg
      exact False.elim (hne ⟨g, hg⟩))
  rcases hGP with ⟨hFG, hGpos⟩
  rcases LinearPMap.le_def.mp hFG with ⟨hFGdom, hFGval⟩
  have hGdense : ∀ y, ∃ x : G.domain, (x : V) + y ∈ s := by
    intro y
    let z : F.domain :=
      ⟨(0, N y.1 - y.2), ⟨Submodule.zero_mem _, Submodule.mem_top⟩⟩
    refine ⟨⟨z.1, hFGdom z.2⟩, ?_⟩
    change N (0 + y.1) ≤ (N y.1 - y.2) + y.2
    simp
  have hGtop : G.domain = ⊤ := by
    by_contra hne
    obtain ⟨H, hGH, hHpos⟩ := provided_step s G hGpos hGdense hne
    have hHP : H ∈ P := ⟨hFG.trans (le_of_lt hGH), hHpos⟩
    have hHG : H ≤ G := hGmax H hHP (le_of_lt hGH)
    exact (not_le_of_gt hGH) hHG
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => G ⟨x, by rw [hGtop]; exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        simpa using
          G.map_add
            ⟨x, by rw [hGtop]; exact Submodule.mem_top⟩
            ⟨y, by rw [hGtop]; exact Submodule.mem_top⟩
      map_smul' := by
        intro c x
        simpa using
          G.map_smul c ⟨x, by rw [hGtop]; exact Submodule.mem_top⟩ }
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -L (x, 0)
      map_add' := by
        intro x y
        simp [L]
      map_smul' := by
        intro c x
        simp [L] }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hv := hFGval
      ⟨(x.1, 0), ⟨x.2, Submodule.mem_top⟩⟩
    change (0 : ℝ) - f x =
      G ⟨(x.1, 0), hFGdom ⟨x.2, Submodule.mem_top⟩⟩ at hv
    change -L (x.1, 0) = f x
    change -(G ⟨(x.1, 0), by rw [hGtop]; exact Submodule.mem_top⟩) = f x
    have : G ⟨(x.1, 0), by rw [hGtop]; exact Submodule.mem_top⟩ = -f x := by
      simpa using hv.symm
    rw [this]
    simp
  · intro x
    have hp := hGpos
      ⟨(x, N x), by rw [hGtop]; exact Submodule.mem_top⟩
      (by change N x ≤ N x; exact le_rfl)
    have hv := hFGval
      ⟨(0, N x), ⟨Submodule.zero_mem _, Submodule.mem_top⟩⟩
    have hv' : L (0, N x) = N x := by
      change G ⟨(0, N x), by rw [hGtop]; exact Submodule.mem_top⟩ = N x
      simpa [F, D] using hv.symm
    have hadd : L (x, N x) = L (x, 0) + L (0, N x) := by
      convert L.map_add (x, 0) (0, N x) using 1 <;> simp
    change 0 ≤ L (x, N x) at hp
    change -L (x, 0) ≤ N x
    rw [hadd, hv'] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth3

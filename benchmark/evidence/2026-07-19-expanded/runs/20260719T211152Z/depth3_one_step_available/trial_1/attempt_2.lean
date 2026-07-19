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

lemma exists_maximal_positive (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (hf : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) :
    ∃ g, f ≤ g ∧
      (∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x) ∧
      ∀ h, g < h → ¬∀ x : h.domain, (x : E) ∈ s → 0 ≤ h x := by
  classical
  let P : Set (E →ₗ.[ℝ] ℝ) :=
    {g | f ≤ g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x}
  have hfP : f ∈ P := by
    exact ⟨le_rfl, hf⟩
  have chain_ub :
      ∀ (c : Set (E →ₗ.[ℝ] ℝ)), c.Nonempty →
        IsChain (· ≤ ·) c → c ⊆ P →
        ∃ u ∈ P, ∀ g ∈ c, g ≤ u := by
    intro c hc hchain hcP
    let D : Submodule ℝ E :=
      { carrier := {x | ∃ g ∈ c, x ∈ g.domain}
        zero_mem' := by
          rcases hc with ⟨g, hgc⟩
          exact ⟨g, hgc, g.domain.zero_mem⟩
        add_mem' := by
          rintro x y ⟨g, hgc, hx⟩ ⟨h, hhc, hy⟩
          rcases hchain.total hgc hhc with hgh | hhg
          · exact ⟨h, hhc, h.domain.add_mem (hgh.1 hx) hy⟩
          · exact ⟨g, hgc, g.domain.add_mem hx (hhg.1 hy)⟩
        smul_mem' := by
          rintro a x ⟨g, hgc, hx⟩
          exact ⟨g, hgc, g.domain.smul_mem a hx⟩ }
    let v : D → ℝ := fun x =>
      let g := Classical.choose x.property
      g ⟨x, (Classical.choose_spec x.property).2⟩
    have v_eq (x : D) (g : E →ₗ.[ℝ] ℝ) (hgc : g ∈ c)
        (hx : (x : E) ∈ g.domain) :
        v x = g ⟨x, hx⟩ := by
      let p := Classical.choose x.property
      have hpc : p ∈ c := (Classical.choose_spec x.property).1
      have hpx : (x : E) ∈ p.domain :=
        (Classical.choose_spec x.property).2
      rcases hchain.total hpc hgc with hpg | hgp
      · exact hpg.2 rfl
      · exact (hgp.2 rfl).symm
    let u : E →ₗ.[ℝ] ℝ :=
      { domain := D
        toFun := v
        map_add' := by
          intro x y
          let px := Classical.choose x.property
          let py := Classical.choose y.property
          have hpxc : px ∈ c := (Classical.choose_spec x.property).1
          have hpyc : py ∈ c := (Classical.choose_spec y.property).1
          have hpx : (x : E) ∈ px.domain :=
            (Classical.choose_spec x.property).2
          have hpy : (y : E) ∈ py.domain :=
            (Classical.choose_spec y.property).2
          change v (x + y) = v x + v y
          rcases hchain.total hpxc hpyc with hxy | hyx
          · have hxpy : (x : E) ∈ py.domain := hxy.1 hpx
            rw [v_eq (x + y) py hpyc (py.domain.add_mem hxpy hpy),
              v_eq x py hpyc hxpy, v_eq y py hpyc hpy]
            simpa using
              (py.map_add ⟨x, hxpy⟩ ⟨y, hpy⟩)
          · have hypx : (y : E) ∈ px.domain := hyx.1 hpy
            rw [v_eq (x + y) px hpxc (px.domain.add_mem hpx hypx),
              v_eq x px hpxc hpx, v_eq y px hpxc hypx]
            simpa using
              (px.map_add ⟨x, hpx⟩ ⟨y, hypx⟩)
        map_smul' := by
          intro a x
          let px := Classical.choose x.property
          have hpxc : px ∈ c := (Classical.choose_spec x.property).1
          have hpx : (x : E) ∈ px.domain :=
            (Classical.choose_spec x.property).2
          change v (a • x) = a • v x
          rw [v_eq (a • x) px hpxc (px.domain.smul_mem a hpx),
            v_eq x px hpxc hpx]
          simpa using (px.map_smul a ⟨x, hpx⟩) }
    have hub : ∀ g ∈ c, g ≤ u := by
      intro g hgc
      refine ⟨?_, ?_⟩
      · intro x hx
        exact ⟨g, hgc, hx⟩
      · intro x y hxy
        have hy : (y : E) ∈ g.domain := by
          rw [← hxy]
          exact x.property
        change g x = v y
        rw [v_eq y g hgc hy]
        congr 1
        exact Subtype.ext hxy
    refine ⟨u, ?_, hub⟩
    change f ≤ u ∧ ∀ x : u.domain, (x : E) ∈ s → 0 ≤ u x
    constructor
    · rcases hc with ⟨g, hgc⟩
      exact (hcP hgc).1.trans (hub g hgc)
    · intro x hxs
      rcases x.property with ⟨g, hgc, hxg⟩
      change 0 ≤ v x
      rw [v_eq x g hgc hxg]
      exact (hcP hgc).2 ⟨x, hxg⟩ hxs
  obtain ⟨g, hg, hmax⟩ :=
    zorn_le_nonempty (s := P) (by
      intro c a b d
      first
      | exact chain_ub c a b d
      | exact chain_ub c a d b
      | exact chain_ub c b a d
      | exact chain_ub c b d a
      | exact chain_ub c d a b
      | exact chain_ub c d b a) ⟨f, hfP⟩
  refine ⟨g, hg.1, hg.2, ?_⟩
  intro h hgh hh
  have hhP : h ∈ P := ⟨hg.1.trans hgh.le, hh⟩
  exact hgh.not_le (hmax h hhP hgh.le)

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  have N_zero : N (0 : E) = 0 := by
    have h := N_hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        simpa [N_zero]
      add_mem' := by
        rintro ⟨x, a⟩ ⟨y, b⟩ hx hy
        exact (N_add x y).trans (add_le_add hx hy)
      smul_mem' := by
        rintro ⟨x, a⟩ hx c hc
        change N (c • x) ≤ c * a
        rw [N_hom c hc x]
        exact mul_le_mul_of_nonneg_left hx hc.le }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
      map_add' := by
        intro x y
        simp
        ring
      map_smul' := by
        intro c x
        simp
        ring }
  have hF : ∀ z : F.domain, (z : E × ℝ) ∈ s → 0 ≤ F z := by
    rintro ⟨⟨x, a⟩, hx⟩ hz
    change N x ≤ a at hz
    change 0 ≤ a - f ⟨x, hx.1⟩
    exact sub_nonneg.mpr ((hf ⟨x, hx.1⟩).trans hz)
  obtain ⟨G, hFG, hG, hmax⟩ := exists_maximal_positive s F hF
  have hGtop : G.domain = ⊤ := by
    by_contra hne
    have hdense : ∀ y, ∃ x : G.domain, (x : E × ℝ) + y ∈ s := by
      rintro ⟨y, b⟩
      let z : F.domain :=
        ⟨(0, N y - b), by
          constructor
          · exact zero_mem f.domain
          · exact Submodule.mem_top⟩
      let x : G.domain := ⟨(z : E × ℝ), hFG.1 z.property⟩
      refine ⟨x, ?_⟩
      change N (0 + y) ≤ (N y - b) + b
      simpa using (le_rfl : N y ≤ N y)
    obtain ⟨H, hGH, hH⟩ := provided_step s G hG hdense hne
    exact (hmax H hGH) hH
  let L : (E × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z =>
        G ⟨z, by rw [hGtop]; exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  have hLF (z : F.domain) : L (z : E × ℝ) = F z := by
    change
      G ⟨(z : E × ℝ), by rw [hGtop]; exact Submodule.mem_top⟩ = F z
    exact (hFG.2 rfl).symm
  have hLone : L (0, 1) = 1 := by
    let z : F.domain :=
      ⟨(0, 1), by
        constructor
        · exact zero_mem f.domain
        · exact Submodule.mem_top⟩
    simpa [F] using hLF z
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -L (x, 0)
      map_add' := by
        intro x y
        change -L (x + y, 0) = -L (x, 0) + -L (y, 0)
        rw [show (x + y, 0) = (x, 0) + (y, 0) by ext <;> simp]
        simp
      map_smul' := by
        intro c x
        change -L (c • x, 0) = c • -L (x, 0)
        rw [show (c • x, 0) = c • (x, 0) by ext <;> simp]
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : F.domain :=
      ⟨((x : E), 0), by
        constructor
        · exact x.property
        · exact Submodule.mem_top⟩
    have hz := hLF z
    change -L ((x : E), 0) = f x
    simpa [F] using congrArg Neg.neg hz
  · intro x
    have hs : ((x, N x) : E × ℝ) ∈ s := by
      change N x ≤ N x
      exact le_rfl
    have hp : 0 ≤ L (x, N x) := by
      change
        0 ≤ G ⟨(x, N x), by rw [hGtop]; exact Submodule.mem_top⟩
      exact
        hG ⟨(x, N x), by rw [hGtop]; exact Submodule.mem_top⟩ hs
    have hsplit : L (x, N x) = L (x, 0) + N x := by
      rw [show (x, N x) = (x, 0) + N x • (0, 1) by ext <;> simp]
      simp [hLone]
    change -L (x, 0) ≤ N x
    rw [hsplit] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth3

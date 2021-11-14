import algebraic_geometry.sheafed_space
import algebraic_geometry.stalks
import topology.bases
import algebra.category.CommRing.colimits
import algebra.category.CommRing.filtered_colimits

open algebraic_geometry category_theory
  algebraic_geometry.PresheafedSpace topological_space opposite
  category_theory.limits Top.presheaf

variables (X : PresheafedSpace CommRing)

def Spe := Σ x, X.stalk x

variables {X}
def pr : Spe X → X := λ x, x.1

structure is_open_Spe_X_str (u : opens X) (V : set (Spe X)) : Prop :=
(fst_mem_u (z : V) : z.1.1 ∈ u.1)
(comes_from_section (z : V) : 
  ∃ (v : opens X) (h : v ≤ u) (h' : z.1.1 ∈ v) (s : X.presheaf.obj (op v)), z.1.2 = @germ _ _ _ X.1 X.2 v ⟨z.1.1, h'⟩ s)

def is_open_in_Spe_X (V : set (Spe X)) : Prop := ∃ (u : opens X), is_open_Spe_X_str u V

instance spe_X_top : topological_space (Spe X) :=
{ is_open := is_open_in_Spe_X,
  is_open_univ := begin
    unfold is_open_in_Spe_X,
    refine ⟨⟨set.univ, is_open_univ⟩, _, _⟩,
    { rintros z, refine set.mem_univ _, },
    { rintros ⟨⟨z, t⟩, h1⟩, 
      obtain ⟨u, z_mem, s, hs⟩ := germ_exist X.2 z t,
      refine ⟨u, le_top, z_mem, ⟨s, _⟩⟩, rw hs, }
  end,
  is_open_inter := λ V₁ V₂ hV₁ hV₂, begin
    unfold is_open_in_Spe_X at hV₁ hV₂ ⊢,
    obtain ⟨u₁, hu11, hu12⟩ := hV₁,
    obtain ⟨u₂, hu21, hu22⟩ := hV₂,
    use u₁ ⊓ u₂, fconstructor,
    { rintros ⟨⟨z, t⟩, h⟩,
      specialize hu11 (⟨⟨z, t⟩, set.inter_subset_left V₁ V₂ h⟩ : V₁),
      specialize hu21 (⟨⟨z, t⟩, set.inter_subset_right V₁ V₂ h⟩ : V₂),
      refine ⟨hu11, hu21⟩, },
    { rintros ⟨⟨z, t⟩, h⟩,
      specialize hu12 (⟨⟨z, t⟩, set.inter_subset_left V₁ V₂ h⟩ : V₁),
      specialize hu22 (⟨⟨z, t⟩, set.inter_subset_right V₁ V₂ h⟩ : V₂),
      obtain ⟨v₁, v₁_le, mem1, ⟨s1, hs1⟩⟩ := hu12,
      obtain ⟨v₂, v₂_le, mem2, ⟨s2, hs2⟩⟩ := hu22,
      use v₁ ⊓ v₂, split, refine inf_le_inf v₁_le v₂_le,
      use ⟨mem1, mem2⟩,
      use X.presheaf.map (quiver.hom.op (ulift.up (plift.up (show v₁ ⊓ v₂ ≤ v₁, from inf_le_left)))) s1,
      simp only [germ_res_apply], simp only at hs1, tidy, }
  end,
  is_open_sUnion := λ ℐ hℐ, begin
    unfold is_open_in_Spe_X at hℐ ⊢,
    set choice_function : ℐ → opens X := λ I : ℐ, (hℐ I.1 I.2).some with cf_eq,
    use Sup (set.range choice_function), split,
    { rintros ⟨⟨z, t⟩, h⟩,
      simp only [exists_prop, set.mem_Union, set.mem_range, 
        set_coe.exists, set.sUnion_image, exists_and_distrib_right, opens.mem_coe,
        set.Union_exists, opens.Sup_s, set.mem_set_of_eq, subtype.val_eq_coe] at h ⊢,
      obtain ⟨S, S_mem, zt_mem⟩ := h,
      use choice_function ⟨S, S_mem⟩, use S, use S_mem,
      specialize hℐ S S_mem,
      have h2 := hℐ.some_spec,
      rcases h2 with ⟨h21, h22⟩, convert h21 ⟨⟨z, t⟩, zt_mem⟩, },
    { rintros ⟨⟨z, t⟩, h⟩,
      simp only [exists_prop, set.mem_set_of_eq] at h ⊢,
      obtain ⟨S, S_mem, zt_mem⟩ := h,
      specialize hℐ S S_mem,
      have h2 := hℐ.some_spec,
      rcases h2 with ⟨h21, h22⟩,
      specialize h22 ⟨⟨z, t⟩, zt_mem⟩,
      
      obtain ⟨v, v_le, mem_v, s, hs⟩ := h22,
      use v, refine ⟨le_trans v_le (le_Sup _), mem_v, ⟨s, _⟩⟩,
      simp only [set.mem_range, set_coe.exists], use S, use S_mem,
      simp only at hs, rw ←hs,}
  end,
}

lemma continous_pr : continuous (@pr X) :=
begin
  rw continuous_def, rintros v v_open,
  have set_eq : pr ⁻¹' v = ⋃ (u : opens X) (h : u ≤ ⟨v, v_open⟩) (s : X.presheaf.obj (op u)), { z | z.1 ∈ u },
  { ext, rcases x with ⟨x, t⟩, unfold pr, simp only [exists_prop, set.mem_preimage, set.mem_Union, set.mem_set_of_eq, exists_const],
    split; intros h,
    { use ⟨v, v_open⟩, split, exact le_refl _, exact h, },
    { obtain ⟨u, h1, h2⟩ := h, tidy,} },
  rw set_eq,
  refine is_open_Union _, rintros w,
  refine is_open_Union _, intros hw,
  refine is_open_Union _, intros s,
  unfold is_open,
  use w, split,
  { rintros ⟨⟨z, t⟩, h⟩,
    exact h, },
  { rintros ⟨⟨z, t⟩, h⟩,
    obtain ⟨u, z_mem, s, hs⟩ := germ_exist X.2 z t,
    use w ⊓ u, split, exact inf_le_left, refine ⟨⟨h, z_mem⟩, ⟨ X.presheaf.map (quiver.hom.op (ulift.up (plift.up (show w ⊓ u ≤ u, from inf_le_right)))) s, _⟩⟩,
    simp only [germ_res_apply], tidy, }
end

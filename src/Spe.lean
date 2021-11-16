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

structure is_basic_open_prop (u : opens X) (s : X.presheaf.obj (op u)) (x : Spe X) : Prop :=
(pr_in : x.1 ∈ u)
(is_stalk : x.2 = germ X.2 ⟨x.1, pr_in⟩ s)

def basic_open (u : opens X) (s : X.presheaf.obj (op u)) : set (Spe X) := set_of (is_basic_open_prop u s)
-- #check is_basic_open
def Spe_basis : set (set (Spe X)) := { V : set (Spe X) | ∃ (u : opens X) (s : X.presheaf.obj (op u)), V = basic_open u s }

instance Spe_topology : topological_space (Spe X) := generate_from Spe_basis 

lemma Spe_basis_is_topology_basis : is_topological_basis (@Spe_basis X) :=
begin
  apply is_topological_basis_of_open_of_nhds,
  { intros V hV, apply generate_open.basic, exact hV },
  { rintros ⟨x, t⟩ V xt_mem Vo,
    induction Vo with W Wb W1 W2 W1o W2o h1 h2 𝒮 h𝒮 ih,
    
    { use W, refine ⟨Wb, xt_mem, λ _, id⟩, },
    { obtain ⟨u, x_mem, s, hs⟩ := germ_exist X.2 x t,
      use basic_open u s,
      refine ⟨⟨u, s, rfl⟩, ⟨x_mem, hs.symm⟩, λ _ _, set.mem_univ _⟩, },
      
    { specialize h1 (set.inter_subset_left _ _ xt_mem),
      specialize h2 (set.inter_subset_right _ _ xt_mem),
      obtain ⟨V1, V1b, xt_mem1, h1⟩ := h1,
      obtain ⟨V2, V2b, xt_mem2, h2⟩ := h2,
      obtain ⟨u1, s1, hu1⟩ := V1b,
      obtain ⟨u2, s2, hu2⟩ := V2b,
      rw hu1 at xt_mem1,
      rw hu2 at xt_mem2,
      rcases xt_mem1 with ⟨x_mem1, ht1⟩,
      rcases xt_mem2 with ⟨x_mem2, ht2⟩,
      have stalk_eq : X.presheaf.germ ⟨x, x_mem1⟩ s1= X.presheaf.germ ⟨x, x_mem2⟩ s2,
      rw [←ht1, ht2],
      obtain ⟨w, x_memw, subset1, subset2, res_eq⟩ := germ_eq X.2 x x_mem1 x_mem2 s1 s2 stalk_eq,
      use basic_open w (X.presheaf.map subset1.op s1),
      refine ⟨⟨w, _, rfl⟩, ⟨x_memw, _⟩, λ z hz, ⟨_, _⟩⟩, rw ht1, simp only [germ_res_apply], refl,
      rcases hz with ⟨hz1, hz2⟩, apply h1, rw hu1, refine ⟨subset1.le hz1, _⟩, rw [hz2, germ_res_apply], refl,
      rcases hz with ⟨hz1, hz2⟩, apply h2, rw hu2, refine ⟨subset2.le hz1, _⟩, rw [hz2, res_eq, germ_res_apply], refl, },
      
    { simp only [exists_prop, set.mem_set_of_eq] at xt_mem,
      obtain ⟨S, S_mem, xt_mem⟩ := xt_mem,
      specialize ih S S_mem xt_mem,
      obtain ⟨V, hV, xt_memV, subset1⟩ := ih,
      refine ⟨V, hV, xt_memV, _⟩,
      apply set.subset_sUnion_of_subset _ S subset1 S_mem, } }
end

-- #exit
-- structure is_open_Spe_X_str (u : opens X) (V : set (Spe X)) : Prop :=
-- (fst_mem_u (z : V) : z.1.1 ∈ u.1)
-- (comes_from_section (z : V) : 
--   ∃ (v : opens X) (h : v ≤ u) (h' : z.1.1 ∈ v) (s : X.presheaf.obj (op v)), z.1.2 = @germ _ _ _ X.1 X.2 v ⟨z.1.1, h'⟩ s)

-- def is_open_in_Spe_X (V : set (Spe X)) : Prop := ∃ (u : opens X), is_open_Spe_X_str u V

-- instance spe_X_top : topological_space (Spe X) :=
-- { is_open := is_open_in_Spe_X,
--   is_open_univ := begin
--     unfold is_open_in_Spe_X,
--     refine ⟨⟨set.univ, is_open_univ⟩, _, _⟩,
--     { rintros z, refine set.mem_univ _, },
--     { rintros ⟨⟨z, t⟩, h1⟩, 
--       obtain ⟨u, z_mem, s, hs⟩ := germ_exist X.2 z t,
--       refine ⟨u, le_top, z_mem, ⟨s, _⟩⟩, rw hs, }
--   end,
--   is_open_inter := λ V₁ V₂ hV₁ hV₂, begin
--     unfold is_open_in_Spe_X at hV₁ hV₂ ⊢,
--     obtain ⟨u₁, hu11, hu12⟩ := hV₁,
--     obtain ⟨u₂, hu21, hu22⟩ := hV₂,
--     use u₁ ⊓ u₂, fconstructor,
--     { rintros ⟨⟨z, t⟩, h⟩,
--       specialize hu11 (⟨⟨z, t⟩, set.inter_subset_left V₁ V₂ h⟩ : V₁),
--       specialize hu21 (⟨⟨z, t⟩, set.inter_subset_right V₁ V₂ h⟩ : V₂),
--       refine ⟨hu11, hu21⟩, },
--     { rintros ⟨⟨z, t⟩, h⟩,
--       specialize hu12 (⟨⟨z, t⟩, set.inter_subset_left V₁ V₂ h⟩ : V₁),
--       specialize hu22 (⟨⟨z, t⟩, set.inter_subset_right V₁ V₂ h⟩ : V₂),
--       obtain ⟨v₁, v₁_le, mem1, ⟨s1, hs1⟩⟩ := hu12,
--       obtain ⟨v₂, v₂_le, mem2, ⟨s2, hs2⟩⟩ := hu22,
--       use v₁ ⊓ v₂, split, refine inf_le_inf v₁_le v₂_le,
--       use ⟨mem1, mem2⟩,
--       use X.presheaf.map (quiver.hom.op (ulift.up (plift.up (show v₁ ⊓ v₂ ≤ v₁, from inf_le_left)))) s1,
--       simp only [germ_res_apply], simp only at hs1, tidy, }
--   end,
--   is_open_sUnion := λ ℐ hℐ, begin
--     unfold is_open_in_Spe_X at hℐ ⊢,
--     set choice_function : ℐ → opens X := λ I : ℐ, (hℐ I.1 I.2).some with cf_eq,
--     use Sup (set.range choice_function), split,
--     { rintros ⟨⟨z, t⟩, h⟩,
--       simp only [exists_prop, set.mem_Union, set.mem_range, 
--         set_coe.exists, set.sUnion_image, exists_and_distrib_right, opens.mem_coe,
--         set.Union_exists, opens.Sup_s, set.mem_set_of_eq, subtype.val_eq_coe] at h ⊢,
--       obtain ⟨S, S_mem, zt_mem⟩ := h,
--       use choice_function ⟨S, S_mem⟩, use S, use S_mem,
--       specialize hℐ S S_mem,
--       have h2 := hℐ.some_spec,
--       rcases h2 with ⟨h21, h22⟩, convert h21 ⟨⟨z, t⟩, zt_mem⟩, },
--     { rintros ⟨⟨z, t⟩, h⟩,
--       simp only [exists_prop, set.mem_set_of_eq] at h ⊢,
--       obtain ⟨S, S_mem, zt_mem⟩ := h,
--       specialize hℐ S S_mem,
--       have h2 := hℐ.some_spec,
--       rcases h2 with ⟨h21, h22⟩,
--       specialize h22 ⟨⟨z, t⟩, zt_mem⟩,
      
--       obtain ⟨v, v_le, mem_v, s, hs⟩ := h22,
--       use v, refine ⟨le_trans v_le (le_Sup _), mem_v, ⟨s, _⟩⟩,
--       simp only [set.mem_range, set_coe.exists], use S, use S_mem,
--       simp only at hs, rw ←hs,}
--   end,
-- }

-- lemma continous_pr : continuous (@pr X) :=
-- begin
--   rw continuous_def, rintros v v_open,
--   have set_eq : pr ⁻¹' v = ⋃ (u : opens X) (h : u ≤ ⟨v, v_open⟩) (s : X.presheaf.obj (op u)), { z | z.1 ∈ u },
--   { ext, rcases x with ⟨x, t⟩, unfold pr, simp only [exists_prop, set.mem_preimage, set.mem_Union, set.mem_set_of_eq, exists_const],
--     split; intros h,
--     { use ⟨v, v_open⟩, split, exact le_refl _, exact h, },
--     { obtain ⟨u, h1, h2⟩ := h, tidy,} },
--   rw set_eq,
--   refine is_open_Union _, rintros w,
--   refine is_open_Union _, intros hw,
--   refine is_open_Union _, intros s,
--   unfold is_open,
--   use w, split,
--   { rintros ⟨⟨z, t⟩, h⟩,
--     exact h, },
--   { rintros ⟨⟨z, t⟩, h⟩,
--     obtain ⟨u, z_mem, s, hs⟩ := germ_exist X.2 z t,
--     use w ⊓ u, split, exact inf_le_left, refine ⟨⟨h, z_mem⟩, ⟨ X.presheaf.map (quiver.hom.op (ulift.up (plift.up (show w ⊓ u ≤ u, from inf_le_right)))) s, _⟩⟩,
--     simp only [germ_res_apply], tidy, }
-- end

@[ext] structure continuous_sections (u : opens X) :=
(func : u → Spe X)
(is_cont : continuous func)
(is_section (x : u) : (func x).1 = x.1 )

@[ext] lemma cont_sec_eq_iff (u : opens X) (s t : continuous_sections u) : s = t ↔ s.func = t.func :=
⟨λ h, begin rw h end, λ h, begin ext1, exact h, end⟩


noncomputable instance has_zero_continuous_sections (u : opens X) : has_zero (continuous_sections u) :=
{ zero := ⟨λ x, ⟨x.1, 0⟩, sorry, λ x, by refl⟩ }

noncomputable instance has_add_continuous_sections (u : opens X) : has_add (continuous_sections u) :=
{ add := λ f g,
  { func := λ x : u, ⟨x.1, eq.rec (f.func x).2 (f.is_section x) + eq.rec (g.func x).2 (g.is_section x)⟩,
    is_cont := sorry,
    is_section := λ x, rfl } }

-- @[to_additive]
noncomputable instance has_mul_continuous_sections (u : opens X) : has_mul (continuous_sections u) :=
{ mul := λ f g,
  { func := λ x : u, ⟨x.1, eq.rec (f.func x).2 (f.is_section x) * eq.rec (g.func x).2 (g.is_section x)⟩,
    is_cont := begin
      apply is_topological_basis.continuous Spe_basis_is_topology_basis,
      rintros W ⟨w, s, hs⟩,
      rw hs,
      set w' : set (w.1.inter u.1) := { z | 
          germ X.2 ⟨z.1, set.inter_subset_left _ _ z.2⟩ s = 
          ((eq.rec (f.func ⟨z.1, set.inter_subset_right _ _ z.2⟩).2 (f.3 ⟨z.1, set.inter_subset_right _ _ z.2⟩)) : X.stalk z.1) *
          ((eq.rec (g.func ⟨z.1, set.inter_subset_right _ _ z.2⟩).2 (g.3 ⟨z.1, set.inter_subset_right _ _ z.2⟩)) : X.stalk z.1) },

      use (λ x : w.1.inter u.1, x.1) '' w',
      refine ⟨_, _⟩,

      { sorry },
      { sorry },

    end,
    is_section := λ x, rfl } }

noncomputable instance has_neg_continuous_sections (u : opens X) : has_neg (continuous_sections u) :=
{ neg := λ f,
  { func := λ x, ⟨x.1, -(eq.rec (f.func x).2 (f.is_section x))⟩,
    is_cont := sorry,
    is_section := λ x, rfl }
}

noncomputable instance add_monoid_continuous_sections (u : opens X) : add_monoid (continuous_sections u) :=
{ add_assoc := λ f g h, begin
    ext1, refine funext (λ x, _),
    refine sigma.eq rfl _, 
    simp only, 
    suffices H : (f + g + h).func x = (f + (g + h)).func x,
    injections_and_clear, dsimp at *, simp at *, assumption,

    unfold has_add.add,
    dsimp only, apply sigma.eq _ _, refl, 
    simp only,
    finish,
  end,
  zero_add := λ f, begin
    rcases f with ⟨f, fc, fs⟩, 
    unfold has_zero.zero,
    unfold has_add.add,
    simp only, refine funext (λ x, _),

    have eq1 := (fs x).symm,
    dsimp only,
    apply sigma.eq _ _, 
    refine eq1,

    dsimp only,
    have : ∀ t : X.stalk x.1, 0 + t = t,
    { intros t, rw zero_add },
    unfold has_add.add at this,
    unfold has_zero.zero at this,
    rw this, finish,
  end,
  add_zero := λ f, begin
    rcases f with ⟨f, fc, fs⟩, 
    unfold has_zero.zero,
    unfold has_add.add,
    simp only, refine funext (λ x, _),

    have eq1 := (fs x).symm,
    dsimp only,
    apply sigma.eq _ _, 
    refine eq1,

    dsimp only,
    have : ∀ t : X.stalk x.1, t + 0 = t,
    { intros t, rw add_zero },
    unfold has_add.add at this,
    unfold has_zero.zero at this,
    rw this, finish,
  end,
  ..(has_add_continuous_sections u),
  ..(has_zero_continuous_sections u)}

noncomputable instance add_comm_group_continuous_sections (u : opens X) : add_comm_group (continuous_sections u) :=
{ 
  add_comm := λ f g,
  begin
    ext1,
    refine funext (λ x, _), refine sigma.eq rfl _, 
    simp only, 
    suffices H : (f + g).func x = (g + f).func x,
    injections_and_clear, dsimp at *, simp at *, assumption,

    unfold has_add.add,
    dsimp only, apply sigma.eq _ _, refl, 
    simp only,
    finish,
  end,

  add_left_neg := λ f, begin
    ext1,
    unfold has_neg.neg,
    unfold sub_neg_monoid.neg,
    unfold has_neg.neg,

    unfold has_add.add,
    unfold add_zero_class.add,
    unfold add_monoid.add,
    unfold sub_neg_monoid.add,
    unfold add_monoid.add,
    unfold has_add.add,
    simp only,

    unfold has_zero.zero,
    unfold add_zero_class.zero,
    unfold add_monoid.zero,
    unfold sub_neg_monoid.zero,
    unfold add_monoid.zero,
    unfold has_zero.zero,
    simp only, refine funext (λ x, _),

    refine sigma.eq rfl _, 
    simp only,

    have : ∀ (t : X.stalk x), -t + t = 0,
    { intros t, rw add_left_neg, },
    unfold has_add.add at this,
    unfold has_neg.neg at this, rw this, refl,
  end,
  ..(add_monoid_continuous_sections u),
  ..(has_neg_continuous_sections u) }


-- noncomputable instance continuous_sections_commring (u : opens X) : comm_ring (continuous_sections u) :=
-- { add_assoc := _,
--   ..(add_comm_group_continuous_sections u)}



-- noncomputable def Spe_presheaf : Top.presheaf CommRing X.1 :=
-- { obj := λ u, ⟨continuous_sections (unop u),
--     { add := λ f g, ⟨⟨λ x, ⟨x.1, 
--       eq.rec_on (f.2 x) (f.1 x).2 + eq.rec_on (g.2 x) (g.1 x).2⟩, 
--       begin
--         rcases f with ⟨⟨f, fc⟩, hf⟩,
--         rcases g with ⟨⟨g, gc⟩, hg⟩,
--         simp only [auto_param_eq] at fc gc ⊢,
--         dsimp only,
--       end
--       ⟩, _⟩,
--       add_assoc := _,
--       add_comm := _,
      
--       zero := _,
--       zero_add := _,
--       add_zero := _,
      
--       neg := _,
--       add_left_neg := _,
      
--       mul := _,
--       mul_assoc := _,
--       mul_comm := _,

--       one := _,
--       one_mul := _,
      
--       left_distrib := _,
--       right_distrib := _ }
--   ⟩,
--   map := λ u v h f, 
--     ⟨⟨λ x, f.1 ⟨x, ((quiver.hom.unop h).le x.2)⟩, by continuity⟩,
--     λ x, begin
--       simp only [continuous_map.coe_mk, function.comp_app, subtype.val_eq_coe],
--       convert f.2 ⟨x, ((quiver.hom.unop h).le x.2)⟩,
--     end⟩ }

-- def Spe_Presheafed_Space : PresheafedSpace Type* :=
-- { carrier := Top.of X,
--   presheaf := Spe_presheaf }

-- lemma Spe_is_sheaf : is_sheaf (@Spe_presheaf X) := sorry

import algebraic_geometry.sheafed_space
import algebraic_geometry.stalks
import topology.bases
import algebra.category.CommRing.colimits
import algebra.category.CommRing.filtered_colimits
import topology.basic

open algebraic_geometry category_theory
  algebraic_geometry.PresheafedSpace topological_space opposite
  category_theory.limits Top.presheaf

variables (X : PresheafedSpace CommRing)

def Spe := Σ x, X.stalk x

variables {X}

structure is_basic_open_prop (u : opens X) (s : X.presheaf.obj (op u)) (x : Spe X) : Prop :=
(pr_in : x.1 ∈ u)
(is_stalk : x.2 = germ X.2 ⟨x.1, pr_in⟩ s)

-- #print is_basic_open_prop

def basic_open (u : opens X) (s : X.presheaf.obj (op u)) : set (Spe X) := set_of (is_basic_open_prop u s)
-- #check is_basic_open

def mem_basic_open (u : opens X) (s : X.2.obj (op u)) (x : Spe X) : x ∈ basic_open u s → Σ' (h : x.1 ∈ u), x.2 = germ X.2 ⟨x.1, h⟩ s := λ h,
begin
  refine ⟨h.1, h.2⟩,
end

def mem_basic_open' (u : opens X) (s : X.2.obj (op u)) (x : Spe X) : (Σ' (h : x.1 ∈ u), x.2 = germ X.2 ⟨x.1, h⟩ s) → x ∈ basic_open u s := λ ⟨h1, h2⟩,
begin
  refine ⟨h1, h2⟩,
end

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

@[ext] structure continuous_sections (u : opens X) :=
(func : u → Spe X)
(is_cont : continuous func)
(is_section (x : u) : (func x).1 = x.1 )

def pr : Spe X → X := sigma.fst

lemma pr_open_map : is_open_map (@pr X) := 
begin
  rw is_topological_basis.is_open_map_iff Spe_basis_is_topology_basis,
  rintros V ⟨v, s, hv⟩,
  rw hv,
  convert v.2,
  ext x, split; intros h, 
  simp only [set.mem_image] at h,
  obtain ⟨y, hy1, hy2⟩ := h,
  have h := mem_basic_open v s y hy1,
  cases h, unfold pr at hy2, rw hy2 at h_fst, exact h_fst,
  unfold pr, simp only [basic_open, set.mem_image, set.mem_set_of_eq],
  refine ⟨⟨x, germ X.2 ⟨x, h⟩ s⟩, _⟩, tidy,
end

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
      set Ffunc := λ (x : u), (eq.rec (f.func x).snd (f.is_section x) : X.stalk x.1) with Ffunc_eq,
      set Gfunc := λ (x : u), (eq.rec (g.func x).snd (g.is_section x) : X.stalk x.1) with Gfunc_eq,
      apply is_topological_basis.continuous Spe_basis_is_topology_basis,
      
      rintros W ⟨w, s, hs⟩,
      rw ←subset_interior_iff_open, 
      intros x hx,
      set t1 := Ffunc x with t1_eq,
      set t2 := Gfunc x with t2_eq,
      have t1_eq' : (eq.rec (f.func x).snd (f.3 x) : X.stalk x.1) = t1 := rfl,        
      have t2_eq' : (eq.rec (g.func x).snd (g.3 x) : X.stalk x.1) = t2 := rfl,
      rw hs at hx ⊢, simp only [set.mem_preimage] at hx ⊢,
      have hx' := mem_basic_open w s _ hx,
      rcases hx' with ⟨h1, h2⟩, dsimp only at h1 h2, rw [t1_eq', t2_eq'] at h2,

      obtain ⟨u_mul, xmemu_mul, s_mul, s_muleq⟩ := germ_exist X.2 x.1 (t1 * t2),
      obtain ⟨u1, xmemu1, s1, s1eq⟩ := germ_exist X.2 x.1 t1,
      obtain ⟨u2, xmemu2, s2, s2eq⟩ := germ_exist X.2 x.1 t2,

      set res_u1_u12 := X.2.map (quiver.hom.op (ulift.up (plift.up (inf_le_left : u1 ⊓ u2 ≤ u1)))) with res_u1_u12_eq,
      set res_u2_u12 := X.2.map (quiver.hom.op (ulift.up (plift.up (inf_le_right : u1 ⊓ u2 ≤ u2)))) with res_u2_u12_eq,
      set proj_12_x := @germ _ _ _ X.1 X.2 (u1 ⊓ u2) ⟨x.1, ⟨xmemu1, xmemu2⟩⟩ with proj_12_x_eq,
      have eq1 : t1 * t2 = proj_12_x (res_u1_u12 s1 * res_u2_u12 s2),
      { rw [proj_12_x_eq, res_u1_u12_eq, res_u2_u12_eq],
        simp only [ring_hom.map_mul, germ_res_apply],
        rw [←s1eq, ←s2eq], refl, },
      rw h2 at s_muleq,
        
      set res_w_uw := X.2.map (quiver.hom.op (ulift.up (plift.up (inf_le_right : u ⊓ w ≤ w)))) with res_w_uw_eq,
      have smul_eq' : X.presheaf.germ ⟨x.val, _⟩ (res_w_uw s) = (X.presheaf.germ ⟨x.val, xmemu_mul⟩) s_mul,
      { simp only [germ_res_apply], rw s_muleq, refl, },
      obtain ⟨o, xmemo, iw, iu_mul, res_eq⟩ := @germ_eq _ _ _ _ _ _ X.2 (u ⊓ w) u_mul x.1 ⟨x.2, h1⟩ xmemu_mul (res_w_uw s) s_mul smul_eq',
      rw mem_interior, refine ⟨{z : u | z.1 ∈ o.1 }, _, _, by assumption⟩,
      { rintros ⟨z, zmemu⟩ hz, 
        simp only [set.mem_preimage, opens.mem_coe, set.mem_set_of_eq, subtype.coe_mk, subtype.val_eq_coe] at hz ⊢,
        apply mem_basic_open', refine ⟨_, _⟩, simp only,
        suffices : u ⊓ w ≤ w, apply this, exact iw.le hz, exact inf_le_right,
        
        simp only [germ_res_apply, eq_self_iff_true, ring_hom.map_mul, subtype.val_eq_coe] at *,
        sorry },
      { rw is_open_induced_iff, refine ⟨o.1, o.2, _⟩, ext x, split; intros hx;
        simp only [set.mem_preimage, opens.mem_coe, set.mem_set_of_eq, subtype.val_eq_coe] at hx ⊢; exact hx, },
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


import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators


set_option maxHeartbeats 0

theorem exercise_3_8 {F V W : Type*} [AddCommGroup V]
  [AddCommGroup W] [Field F] [Module F V] [FiniteDimensional F V] [Module F W]
  (L : V →ₗ[F] W) :
  ∃ U : Submodule F V, U ⊓ (ker L) = ⊥ ∧
  (range L = range (domRestrict L U)):= by
  -- Step 1: Define the kernel of L
  let K := ker L
  -- Step 2: There exists a basis for K
  -- Since V is finite dimensional, K is also finite dimensional.
  -- have h_exists_basis_K : ∃ (b : Basis (Fin (FiniteDimensional.finrank F K)) F K), True := by
    -- prove_with[]

  -- Let's fix such a basis and extract it.
  -- We use classical choice to get a complement submodule U.
  -- A standard result in linear algebra states that for any subspace K, there exists a subspace U such that V = K ⊕ U.
  -- This implies U ∩ K = {0} (i.e., U ⊓ K = ⊥) and every v ∈ V can be uniquely written as k + u with k ∈ K, u ∈ U.
  -- Let U be a complementary submodule to K.
  have h_complement : ∃ U : Submodule F V, K ⊔ U = ⊤ ∧ K ⊓ U = ⊥ := by
    clear * -
    rcases K.exists_isCompl with ⟨L', h₁, h₂⟩
    use L'
    constructor
    · exact codisjoint_iff.1 h₂
    · exact disjoint_iff.1 h₁

  obtain ⟨U, h_sup_eq_top, h_inf_eq_bot⟩ := h_complement
  -- Step 6 from informal proof: U ∩ K = {0}, which corresponds to U ⊓ K = ⊥
  have h_intersect_bot : U ⊓ K = ⊥ := by
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 0 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by exfalso))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [Submodule.comap_bot]))
      (add norm 0 (by grind only [Submodule.eq_bot_iff]))
      (add norm 0 (by grind only [Submodule.orthogonal_eq_bot_iff]))
      (add norm 0 (by grind only [Submodule.map_bot]))
      (add norm 0 (by grind only [Submodule.fst_inf_snd]))
      (add norm 0 (by grind only [eq_bot_iff]))
      (add norm 0 (by grind only [Submodule.inf_orthogonal_eq_bot]))
      (add norm 0 (by grind only [Submodule.dualAnnihilator_bot]))
      (add norm 0 (by grind only [Submodule.ker_liftQ_eq_bot]))
      (add norm 0 (by grind only [Submodule.triorthogonal_eq_orthogonal]))
      (add norm 0 (by grind only [LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace]))
      (add norm 0 (by grind only [le_bot_iff]))
      (add norm 0 (by grind only [CompleteSublattice.coe_bot]))
      (add norm 0 (by grind only [LieSubmodule.ker_incl]))
      (add norm 0 (by grind only [LieSubmodule.bot_coeSubmodule]))
      (add norm 0 (by grind only [Module.eval_ker]))
      (add norm 0 (by grind only [Submodule.dualAnnihilator_top]))
      (add norm 0 (by grind only [LieModuleHom.ker]))
      (add norm 0 (by grind only [Submodule.orthogonal_orthogonal]))
      (add norm 0 (by grind only [LinearMap.ker]))
      (add norm 0 (by grind only [Subspace.dualAnnihilator_inf_eq]))
      (add norm 0 (by grind only [isSMulRegular_iff_ker_lsmul_eq_bot]))
      (add norm 0 (by grind only [Submodule.top_orthogonal_eq_bot]))
      (add norm 0 (by grind only [ker_orthogonalProjection]))
      (add norm 0 (by grind only [isSMulRegular_iff_torsionBy_eq_bot]))
      (add norm 0 (by grind only [LieSubmodule.map_bot]))
      (add norm 0 (by grind only [Submodule.ker_mkQ]))
      (add norm 0 (by grind only [LinearMap.IsRefl.ker_eq_bot_iff_ker_flip_eq_bot]))
      (add norm 0 (by grind only [LinearMap.IsRefl.ker_flip_eq_bot]))
      (add norm 0 (by grind only [Submodule.ker_liftQ_eq_bot']))
      (add norm 0 (by grind only [LieAlgebra.IsKilling.iInf_ker_weight_eq_bot]))
      (add norm 0 (by grind only [Subspace.dualAnnihilator_le_dualAnnihilator_iff]))

  -- Now we need to prove that range L = range (domRestrict L U)
  -- Step 7-12 logic:
  -- For any w in range L, there exists v in V such that L v = w.
  -- Since K ⊔ U = ⊤, v can be written as k + u with k ∈ K, u ∈ U.
  -- L v = L (k + u) = L k + L u = 0 + L u = L u.
  -- So w = L u where u ∈ U. Thus w is in the range of domRestrict L U.
  -- Conversely, if w is in range (domRestrict L U), then w = L u for some u ∈ U.
  -- Since U ≤ V, u ∈ V, so w = L u is in range L.
  -- Step 11: range L ⊆ range (domRestrict L U)
  have h_range_subset : range L ≤ range (domRestrict L U) := by
    intro w hw
    obtain ⟨v, hv⟩ := hw
    have h_v_decomp : ∃ (k : K) (u : U), ↑(k : V) + ↑(u : V) = v := by
      -- Since K ⊔ U = ⊤, v ∈ K ⊔ U
      have h_v_in_sup : v ∈ K ⊔ U := by
        aesop (config := {
          maxRuleApplications := 1600
          maxRuleApplicationDepth := 10
          maxNormIterations := 320
          })
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by omega))
          (add norm 0 (by bound))
          (add norm 0 (by ring_nf))
          (add norm 1 (by field_simp [*] at *))
          (add safe 100 (by ring))
          (add safe 100 (by field_simp))
          (add safe 100 (by norm_num))
          (add safe 0 (by positivity))
          (add safe 100 (by interval_cases))
          (add safe 0 (by ext))
          (add safe 0 (by split))
          (add safe 100 (by exfalso))
          (add safe 100 (by rfl))
          (add safe 100 (by decide))
          (add safe 100 (by assumption_mod_cast))
          (add norm 0 (by grind only [Submodule.mem_sup]))
          (add norm 0 (by grind only [LieSubmodule.mem_sup]))
          (add norm 0 (by grind only [Submodule.mem_sup_right]))
          (add norm 0 (by grind only [Submodule.mem_sup']))
          (add norm 0 (by grind only [Submodule.FG.sup]))
          (add norm 0 (by grind only [Submodule.mem_comap]))
          (add norm 0 (by grind only [Submodule.mem_sup_left]))
          (add norm 0 (by grind only [Order.Ideal.mem_sup]))
          (add norm 0 (by grind only [Order.Ideal.sup_mem]))
          (add norm 0 (by grind only [Ideal.mem_sup_right]))
          (add norm 0 (by grind only [Order.Ideal.sup_mem_iff]))
          (add norm 0 (by grind only [LinearMap.mem_range]))
          (add norm 0 (by grind only [Module.AEval.mem_comapSubmodule]))
          (add norm 0 (by grind only [Submodule.mem_orthogonalBilin_iff]))
          (add norm 0 (by grind only [Ideal.Filtration.mem_submodule]))
          (add norm 0 (by grind only [Submodule.add_eq_sup]))
          (add norm 0 (by grind only [LinearMap.BilinForm.mem_orthogonal_iff]))
          (add norm 0 (by grind only [Submodule.sup_orthogonal_of_completeSpace]))
          (add norm 0 (by grind only [Submodule.mem_dualAnnihilator]))
          (add norm 0 (by grind only [Submodule.fst]))
          (add norm 0 (by grind only [le_sup_right]))
          (add norm 0 (by grind only [Projectivization.submodule_mk]))
          (add norm 0 (by grind only [Submodule.eq_top_of_disjoint]))
          (add norm 0 (by grind only [Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson]))
          (add norm 0 (by grind only [le_sup_left]))
          (add norm 0 (by grind only [Submodule.snd]))
          (add norm 0 (by grind only [Submodule.mem_iInf]))
          (add norm 0 (by grind only [Submodule.add_mem_sup]))
          (add norm 0 (by grind only [Ideal.mem_toCotangent_ker]))
          (add norm 0 (by grind only [Submodule.mem_traceDual]))
          (add norm 0 (by grind only [LinearPMap.domain_supSpanSingleton]))
          (add norm 0 (by grind only [Submodule.mem_map]))

      -- Definition of sup of submodules: x ∈ K ⊔ U iff ∃ k ∈ K, u ∈ U, x = k + u
      -- We need to extract k and u from the fact that v is in K ⊔ U
      rw [Submodule.mem_sup] at h_v_in_sup
      obtain ⟨y, hy, z, hz, rfl⟩ := h_v_in_sup
      use ⟨y, hy⟩, ⟨z, hz⟩

    rcases h_v_decomp with ⟨k, u, h_decomp⟩
    have h_L_k_zero : L (↑k) = 0 := by
      have hk_in_K : ↑k ∈ K := by exact k.property
      have hk_in_ker : ↑k ∈ ker L := by
        aesop (config := {
          maxRuleApplications := 100
          maxRuleApplicationDepth := 10
          maxNormIterations := 320
          })
          (add norm 100 (by norm_cast))
          (add norm 0 (by linarith))
          (add norm 0 (by nlinarith))
          (add norm 0 (by positivity))
          (add norm 0 (by bound))
          (add norm 0 (by ring_nf))
          (add norm 1 (by field_simp [*] at *))
          (add safe 100 (by ring))
          (add safe 100 (by field_simp))
          (add safe 100 (by norm_num))
          (add safe 100 (by omega))
          (add safe 100 (by interval_cases))
          (add safe 0 (by ext))
          (add safe 0 (by split))
          (add safe 100 (by decide))
          (add safe 0 (by push_cast))
          (add safe 100 (by assumption_mod_cast))
          (add norm 0 (by grind only [LinearMap.mem_ker]))
          (add norm 0 (by grind only [LinearMap.mem_range]))
          (add norm 0 (by grind only [Ideal.mem_toCotangent_ker]))
          (add norm 0 (by grind only [LieModuleHom.mem_ker]))
          (add norm 0 (by grind only [Submodule.mem_orthogonal']))
          (add norm 0 (by grind only [Submodule.mem_orthogonal]))
          (add norm 0 (by grind only [Submodule.mem_comap]))
          (add norm 0 (by grind only [LinearMap.BilinForm.mem_orthogonal_iff]))
          (add norm 0 (by grind only [Representation.mem_invariants]))
          (add norm 0 (by grind only [Submodule.mem_orthogonalBilin_iff]))
          (add norm 0 (by grind only [LieModule.mem_ker]))
          (add norm 0 (by grind only [Submodule.mem_dualAnnihilator]))
          (add norm 0 (by grind only [orthogonalProjection_eq_zero_iff]))
          (add norm 0 (by grind only [Submodule.mem_dualCoannihilator]))
          (add norm 0 (by grind only [Module.AEval.mem_comapSubmodule]))
          (add norm 0 (by grind only [Module.End.mem_genEigenspace]))
          (add norm 0 (by grind only [LieDerivation.IsKilling.ad_mem_ker_killingForm_ad_range_of_mem_orthogonal]))
          (add norm 0 (by grind only [Module.AEval.mem_mapSubmodule]))
          (add norm 0 (by grind only [LieIdeal.mem_killingCompl]))
          (add norm 0 (by grind only [LieModule.traceForm_comm]))
          (add norm 0 (by grind only [LinearPMap.mem_adjoint_domain_iff]))
          (add norm 0 (by grind only [inv_mem_iff]))
          (add norm 0 (by grind only [LinearMap.BilinForm.isOrtho_def]))
          (add norm 0 (by grind only [Submodule.mem_bot]))
          (add norm 0 (by grind only [LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg]))
          (add norm 0 (by grind only [LinearMap.mem_range_self]))
          (add norm 0 (by grind only [Ideal.Filtration.mem_submodule]))
          (add norm 0 (by grind only [Submodule.coe_mem]))
          (add norm 0 (by grind only [LinearMap.sub_apply]))
          (add norm 0 (by grind only [LieHom.mem_ker]))
          (add norm 0 (by grind only [Projectivization.submodule_mk]))
          (add norm 0 (by grind only [Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]))

      simp_all

    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 0 (by omega))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by ring))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by interval_cases))
      (add safe 0 (by ext))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add norm 0 (by grind only [LinearMap.mem_ker]))
      (add norm 0 (by grind only [LinearMap.mem_range]))
      (add norm 0 (by grind only [LieModuleHom.mem_ker]))
      (add norm 0 (by grind only [Representation.mem_invariants]))
      (add norm 0 (by grind only [orthogonalProjection_eq_zero_iff]))
      (add norm 0 (by grind only [Ideal.mem_toCotangent_ker]))
      (add norm 0 (by grind only [LinearMap.BilinForm.isOrtho_def]))
      (add norm 0 (by grind only [Submodule.mem_orthogonal]))
      (add norm 0 (by grind only [Submodule.mem_dualCoannihilator]))
      (add norm 0 (by grind only [Submodule.mem_bot]))
      (add norm 0 (by grind only [LinearMap.BilinForm.mem_orthogonal_iff]))
      (add norm 0 (by grind only [Submodule.mem_orthogonal']))
      (add norm 0 (by grind only [LieModule.mem_ker]))
      (add norm 0 (by grind only [Submodule.mem_dualAnnihilator]))
      (add norm 0 (by grind only [Submodule.mem_comap]))
      (add norm 0 (by grind only [Module.End.mem_genEigenspace]))
      (add norm 0 (by grind only [NormedAddGroupHom.mem_ker]))
      (add norm 0 (by grind only [LieModule.traceForm_comm]))
      (add norm 0 (by grind only [LinearMap.isOrtho_def]))
      (add norm 0 (by grind only [LinearMap.BilinForm.IsOrtho]))
      (add norm 0 (by grind only [LinearMap.restrict_apply]))
      (add norm 0 (by grind only [Submodule.mem_orthogonalBilin_iff]))
      (add norm 0 (by grind only [LieHom.mem_ker]))
      (add norm 0 (by grind only [inv_mem_iff]))
      (add norm 0 (by grind only [Submodule.mk_eq_zero]))
      (add norm 0 (by grind only [LieSubmodule.Quotient.mk_eq_zero]))
      (add norm 0 (by grind only [Submodule.dualCopairing_apply]))
      (add norm 0 (by grind only [LieIdeal.mem_killingCompl]))
      (add norm 0 (by grind only [Module.AEval.mem_mapSubmodule]))
      (add norm 0 (by grind only [Submodule.Quotient.mk_eq_zero]))
      (add norm 0 (by grind only [LinearMap.sub_apply]))
      (add norm 0 (by grind only [Module.Baer.extensionOfMax]))

  -- Step 12: range (domRestrict L U) ⊆ range L
  have h_subset_range : range (domRestrict L U) ≤ range L := by
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have h_w_eq_L_u : w = L (↑u) := by
      simp_all [LinearMap.coe_domRestrict]

    -- Since u : U, ↑u : V.
    -- So w = L (↑u) means w is in the image of L from V.
    have h_u_in_V : ↑u ∈ Set.univ := by trivial
    have h_range_L_def : w ∈ Set.range L := by
      refine' ⟨↑u, _⟩
      simp_all

    -- Set.range L is not exactly LinearMap.range L, but they are equivalent.
    -- LinearMap.range L is a Submodule, defined as the submodule generated by the image.
    -- Actually, LinearMap.range L is exactly the image of L as a submodule.
    -- w ∈ (range L : Set W) iff ∃ v, L v = w.
    -- We have ∃ v, L v = w.
    exact h_range_L_def

  -- Step 13: range L = range (domRestrict L U)
  have h_range_eq : range L = range (domRestrict L U) := by
    apply Submodule.ext
    aesop (config := {
      maxRuleApplications := 1600
      maxRuleApplicationDepth := 10
      maxNormIterations := 320
      })
      (add norm 100 (by norm_cast))
      (add norm 0 (by linarith))
      (add norm 0 (by nlinarith))
      (add norm 1 (by push_neg))
      (add norm 0 (by bound))
      (add norm 0 (by ring_nf))
      (add norm 1 (by ext))
      (add norm 100 (by exfalso))
      (add norm 1 (by field_simp [*] at *))
      (add safe 100 (by field_simp))
      (add safe 100 (by norm_num))
      (add safe 100 (by positivity))
      (add safe 100 (by omega))
      (add safe 100 (by interval_cases))
      (add safe 0 (by split))
      (add safe 100 (by decide))
      (add safe 0 (by push_cast))
      (add safe 100 (by assumption_mod_cast))
      (add unsafe 90% (by norm_num [*] at *))
      (add norm 0 (by grind only [LinearMap.mem_range]))
      (add norm 0 (by grind only [Submodule.mem_comap]))
      (add norm 0 (by grind only [Submodule.mem_iInf]))
      (add norm 0 (by grind only [Submodule.mem_dualAnnihilator]))
      (add norm 0 (by grind only [Submodule.mem_orthogonalBilin_iff]))
      (add norm 0 (by grind only [LinearMap.mem_range_self]))
      (add norm 0 (by grind only [Module.AEval.mem_comapSubmodule]))
      (add norm 0 (by grind only [Ideal.Filtration.mem_submodule]))
      (add norm 0 (by grind only [Submodule.mem_traceDual]))
      (add norm 0 (by grind only [LinearMap.BilinForm.mem_orthogonal_iff]))
      (add norm 0 (by grind only [Submodule.mem_one]))
      (add norm 0 (by grind only [Submodule.mem_colon]))
      (add norm 0 (by grind only [Ideal.mem_iInf_smul_pow_eq_bot_iff]))
      (add norm 0 (by grind only [Submodule.mem_inf]))
      (add norm 0 (by grind only [Submodule.mem_carrier]))
      (add norm 0 (by grind only [Representation.mem_invariants]))
      (add norm 0 (by grind only [Submodule.mem_dualCoannihilator]))
      (add norm 0 (by grind only [LinearPMap.mem_adjoint_domain_iff]))
      (add norm 0 (by grind only [ProperCone.mem_coe]))
      (add norm 0 (by grind only [Submodule.mem_orthogonal]))
      (add norm 0 (by grind only [Submodule.mem_orthogonal']))
      (add norm 0 (by grind only [LinearMap.BilinForm.mem_dualSubmodule]))
      (add norm 0 (by grind only [LinearMap.mem_ker]))
      (add norm 0 (by grind only [Submodule.mem_annihilator]))
      (add norm 0 (by grind only [FractionalIdeal.mem_coe]))
      (add norm 0 (by grind only [Submodule.restrictScalars_mem]))
      (add norm 0 (by grind only [Submodule.mem_bot]))
      (add norm 0 (by grind only [Sublattice.mem_carrier]))
      (add norm 0 (by grind only [Module.AEval.mem_mapSubmodule]))
      (add norm 0 (by grind only [Ideal.mem_toCotangent_ker]))
      (add norm 0 (by grind only [Submodule.mem_toConvexCone]))
      (add norm 0 (by grind only [mem_innerDualCone]))

  -- Combine results
  refine' ⟨U, _⟩
  constructor
  · -- Prove U ⊓ K = ⊥
    rw [h_intersect_bot]

  · -- Prove range L = range (domRestrict L U)
    exact h_range_eq

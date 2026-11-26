import DLMST

/-- Audit: every machine-checked paper claim must depend only on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`. -/
theorem audit : True := trivial

#print axioms DLMST.kruskal_exists
#print axioms DLMST.boruvka_round
#print axioms DLMST.IsForest.trail_eq
#print axioms DLMST.maxima_vectors_card
#print axioms DLMST.filter_preserves_msf
#print axioms DLMST.IsMSFOf.below_span
#print axioms DLMST.IsMSFOf.supported_of
#print axioms DLMST.portal_bound
#print axioms DLMST.declared_card
#print axioms DLMST.incidence
#print axioms DLMST.bad_card_le
#print axioms DLMST.badProject_card_le_one
#print axioms DLMST.Greedy.card_le
#print axioms DLMST.exists_greedy_maximal
#print axioms DLMST.reps_below_of_not_lower
#print axioms DLMST.IsRep.of_lower
#print axioms DLMST.log_one_add_le_two_sqrt
#print axioms DLMST.test_budget
#print axioms DLMST.tests_le_sqrt
#print axioms DLMST.sum_fiber_card
#print axioms DLMST.sum_degree
#print axioms DLMST.batch_supported_or_project
#print axioms DLMST.batch_at_vertex
#print axioms DLMST.supported_of_declared
#print axioms DLMST.exists_rep
#print axioms DLMST.card_Sv
#print axioms DLMST.exists_cnd
#print axioms DLMST.card_Dcl_le
#print axioms DLMST.wOrd_weight
#print axioms DLMST.lemma33_comparisons
#print axioms DLMST.comparisons_main
#print axioms DLMST.halving_sum_le
#print axioms DLMST.halving_zero
#print axioms DLMST.halving_le_div_pow
#print axioms DLMST.sum_card_disjoint_le
#print axioms DLMST.tests_main
#print axioms DLMST.tests_quota1
#print axioms DLMST.tests_total
#print axioms DLMST.natLog_le_realLog
#print axioms DLMST.tests_budget_real
#print axioms DLMST.monoRow_of_connImproves
#print axioms DLMST.connImproves_of_grow
#print axioms DLMST.good_project_succ
#print axioms DLMST.admOut_admissible
#print axioms DLMST.admOut_spokes
#print axioms DLMST.LiftsLe.walk
#print axioms DLMST.conn_portal_eq
#print axioms DLMST.claim_3_6
#print axioms DLMST.claim_3_6_supported
#print axioms DLMST.lemma37_last
#print axioms DLMST.lemma37_project_step
#print axioms DLMST.lemma37_rejected_error
#print axioms DLMST.lemma37
#print axioms DLMST.History.badFor_card_le
#print axioms DLMST.History.monoRow_of_grow
#print axioms DLMST.History.genEdge_le
#print axioms DLMST.History.weighted_sum_le
#print axioms DLMST.exists_le_average
#print axioms DLMST.lemma311
#print axioms DLMST.card_agreeTuples
#print axioms DLMST.card_bad_le
#print axioms DLMST.sample_budget
#print axioms DLMST.claim312
#print axioms DLMST.log_one_add_le_two_sqrt
#print axioms DLMST.one_div_sqrt_le_two_mul_sub
#print axioms DLMST.sum_range_one_div_sqrt_succ_le
#print axioms DLMST.choose_eq_prod_range
#print axioms DLMST.log_choose_le
#print axioms DLMST.sum_degV_le_two_mul
#print axioms DLMST.sum_log_degV_le
#print axioms DLMST.card_spokeOK_le
#print axioms DLMST.card_filter_forall
#print axioms DLMST.card_spokeSeqs_le
#print axioms DLMST.sum_range_choose_le
#print axioms DLMST.card_finsets_le_choose
#print axioms DLMST.card_forestSeqs_le
#print axioms DLMST.pref_vectors_le
#print axioms DLMST.card_histories_le
#print axioms DLMST.log_card_histories_le
#print axioms DLMST.children_vertices_le
#print axioms DLMST.level_edges_le
#print axioms DLMST.sum_inv_cube_le_two
#print axioms DLMST.pow6_ratio
#print axioms DLMST.geom_sum_le
#print axioms DLMST.sum_pow6_div_two_pow_le
#print axioms DLMST.sqrt_four_pow
#print axioms DLMST.claim_3_13
#print axioms DLMST.errors_levels
#print axioms DLMST.lemma12_bound
#print axioms DLMST.unsupp_msf_eq_empty
#print axioms DLMST.card_le_two_mul_of_no_isolated
#print axioms DLMST.lemma12_bound_card
#print axioms DLMST.compCount_insert
#print axioms DLMST.card_add_compCount
#print axioms DLMST.card_le_card_of_isForest
#print axioms DLMST.card_le_card_sub_one_of_isForest
#print axioms DLMST.lemma12_bound_of_forest
#print axioms DLMST.card_partition_eq
#print axioms DLMST.card_partition_le
#print axioms DLMST.certificate_partition_le
#print axioms DLMST.round_budget_sum
#print axioms DLMST.round_budget_sum_paper
#print axioms DLMST.sum_rEdges_card
#print axioms DLMST.disjoint_of_rEdges_subset
#print axioms DLMST.driver_partition
#print axioms DLMST.driver_comparisons
#print axioms DLMST.exists_batchSpec
#print axioms DLMST.exists_spokeSpec
#print axioms DLMST.nonempty_edge_of_no_isolated
#print axioms DLMST.exists_incident_map
#print axioms DLMST.prefFind_iff_trail_weight
#print axioms DLMST.projGraph
#print axioms DLMST.belowLe_projGraph
#print axioms DLMST.conn_projEdge
#print axioms DLMST.conn_of_projGraph
#print axioms DLMST.conn_lift
#print axioms DLMST.certificate_of_display
#print axioms DLMST.linear_of_display
#print axioms DLMST.exists_schedule_lost_le
#print axioms DLMST.exists_schedule_lost_paper
#print axioms DLMST.misestimate_total_le
#print axioms DLMST.compCount_halves
#print axioms DLMST.pow_two_mul_le_of_le
#print axioms DLMST.compCount_pow_halves
#print axioms DLMST.compCount_le_div_pow
#print axioms DLMST.compCount_le_real
#print axioms DLMST.compCount_le_real_of_empty
#print axioms DLMST.log_one_add_le_sqrt
#print axioms DLMST.log_choose_le_two
#print axioms DLMST.exists_wOrd_min
#print axioms DLMST.exists_min_leaving
#print axioms DLMST.leaveSet_congr
#print axioms DLMST.BorPhase.toAt
#print axioms DLMST.BorPhaseAt.not_mem
#print axioms DLMST.mem_boruvkaPhase
#print axioms DLMST.boruvkaPhase_borPhaseAt
#print axioms DLMST.boruvkaPhase_cover
#print axioms DLMST.crossing_phase_edge
#print axioms DLMST.boruvka_forest_at
#print axioms DLMST.compCount_halves_of_forest
#print axioms DLMST.boruvkaPhase_halves
#print axioms DLMST.boruvkaRun_forest
#print axioms DLMST.boruvkaRun_pow_halves
#print axioms DLMST.boruvkaRun_le_real
#print axioms DLMST.exists_trail_crossing
#print axioms DLMST.boruvka_round_at
#print axioms DLMST.boruvkaPhase_round
#print axioms DLMST.boruvkaRun_extendable
#print axioms DLMST.CallOut.U
#print axioms DLMST.CallOut.FU_disjoint
#print axioms DLMST.CallOut.partition_eq
#print axioms DLMST.CallOut.sum_kidE_le
#print axioms DLMST.CallOut.kidV_card
#print axioms DLMST.Level.verts
#print axioms DLMST.Level.edges
#print axioms DLMST.Step.edges_le
#print axioms DLMST.LevelChain.verts
#print axioms DLMST.LevelChain.edges
#print axioms DLMST.errors_gather
#print axioms DLMST.inputs_gather
#print axioms DLMST.hrest_of_levels
#print axioms DLMST.display_of_callout
#print axioms DLMST.display_of_callout_full
#print axioms DLMST.comparisons_of_levels
#print axioms DLMST.comp_ne_univ_of_two_le
#print axioms DLMST.leaveSet_nonempty_of_conn
#print axioms DLMST.hact_of_conn
#print axioms DLMST.boruvkaPhase_halves_of_conn
#print axioms DLMST.boruvkaRun_step
#print axioms DLMST.boruvkaRun_halves_of_conn
#print axioms DLMST.boruvkaRun_le_one_add
#print axioms DLMST.sum_image_le_sum
#print axioms DLMST.Level.root
#print axioms DLMST.Level.ofCallOut
#print axioms DLMST.Step.ofCallOut
#print axioms DLMST.CallOut.ofClass
#print axioms DLMST.CallOut.ofForest
#print axioms DLMST.CallOut.nonempty_of_isForest
#print axioms DLMST.portals_shrink
#print axioms DLMST.sum_union_le
#print axioms DLMST.sum_biUnion_le
#print axioms DLMST.Level.allChildren
#print axioms DLMST.Step.ofCalls
#print axioms DLMST.Strategy.Wf
#print axioms DLMST.Level.next
#print axioms DLMST.Level.chain
#print axioms DLMST.Step.next
#print axioms DLMST.LevelChain.chain_step
#print axioms DLMST.LevelChain.chain_verts
#print axioms DLMST.LevelChain.chain_edges
#print axioms DLMST.display_of_strategy
#print axioms DLMST.Strategy.Strict
#print axioms DLMST.Strategy.Leaf
#print axioms DLMST.LevelChain.chain_edges_le_card
#print axioms DLMST.LevelChain.chain_edges_empty
#print axioms DLMST.LevelChain.chain_insts_succ_empty
#print axioms DLMST.LevelChain.chain_insts_empty_at
#print axioms DLMST.LevelChain.chain_insts_empty_of_le
#print axioms DLMST.CallOut.nonempty_of_subforest
#print axioms DLMST.CallOut.kidE_card_lt
#print axioms DLMST.CallOut.ofClass_kidE_not_mem
#print axioms DLMST.Strategy.Drops
#print axioms DLMST.Strategy.strict_of_drops
#print axioms DLMST.Strategy.leafOut
#print axioms DLMST.Strategy.wf_strict_leaf
#print axioms DLMST.Strategy.ofInterior
#print axioms DLMST.Strategy.ofInterior_wf
#print axioms DLMST.Strategy.ofInterior_leaf
#print axioms DLMST.Strategy.ofInterior_strict
#print axioms DLMST.Strategy.exists_strategy_of_interior
#print axioms DLMST.supported_of_loop
#print axioms DLMST.IsForest.src_ne_dst
#print axioms DLMST.unsupp_empty_of_loopfree
#print axioms DLMST.Strategy.not_strict_of_loop
#print axioms DLMST.Strategy.emptyClassCall
#print axioms DLMST.Strategy.exists_strict_of_loopfree
#print axioms DLMST.Level.errors_le
#print axioms DLMST.Level.inputs_le
#print axioms DLMST.display_of_strategy_of_uniform
#print axioms DLMST.display_of_strategy_of_calls
#print axioms DLMST.LevelChain.chain_edges_succ
#print axioms DLMST.LevelChain.kept_telescope
#print axioms DLMST.LevelChain.kept_telescope_full
#print axioms DLMST.LevelChain.kept_le
#print axioms DLMST.card_partition_eq_of_subset
#print axioms DLMST.isForest_of_forall_not_conn_below
#print axioms DLMST.sum_rEdgesIn_card
#print axioms DLMST.driver_partition_in
#print axioms DLMST.driver_comparisons_in
#print axioms DLMST.CallOut.RoundData.kidE_subset_input
#print axioms DLMST.CallOut.RoundData.sum_kidE_le_sum_input
#print axioms DLMST.CallOut.RoundData.partition
#print axioms DLMST.CallOut.RoundData.U_add_kids
#print axioms DLMST.CallOut.RoundData.isForest_F
#print axioms DLMST.CallOut.reindex
#print axioms DLMST.Strategy.ofRoundData
#print axioms DLMST.Strategy.ofRoundData_wf
#print axioms DLMST.isForest_K
#print axioms DLMST.mem_K_or
#print axioms DLMST.preF_mono
#print axioms DLMST.isForest_preF
#print axioms DLMST.preF_subset_of_scan
#print axioms DLMST.biUnion_preF
#print axioms DLMST.CallOut.RoundData.ofScan
#print axioms DLMST.sum_pow6_div_four_pow_le
#print axioms DLMST.sum_cubic_le
#print axioms DLMST.errors_levels_rest
#print axioms DLMST.lemma12_bound_gen
#print axioms DLMST.Level.inputs_le_err
#print axioms DLMST.hrest_of_levels_rest
#print axioms DLMST.hrest_of_instances_rest
#print axioms DLMST.display_of_callout_rest
#print axioms DLMST.display_of_strategy_of_calls_rest
#print axioms DLMST.pow21_le_two_pow
#print axioms DLMST.sum_pow21_div_four_pow_le
#print axioms DLMST.sum_pow21_mul_le
#print axioms DLMST.errors_levels_poly
#print axioms DLMST.lemma12_bound_extra
#print axioms DLMST.Level.inputs_le_coef
#print axioms DLMST.hrest_of_levels_poly
#print axioms DLMST.hrest_of_instances_poly
#print axioms DLMST.display_of_callout_poly
#print axioms DLMST.display_of_strategy_of_calls_poly
#print axioms DLMST.msf_input_count
#print axioms DLMST.msf_input_le_poly
#print axioms DLMST.hinF_of_rounds
#print axioms DLMST.display_of_strategy_of_calls_paper
#print axioms DLMST.error_count_le
#print axioms DLMST.claim_3_13_coef
#print axioms DLMST.errors_levels_poly_coef
#print axioms DLMST.errors_gather_coef
#print axioms DLMST.Level.errors_le_coef
#print axioms DLMST.hrest_of_levels_poly_coef
#print axioms DLMST.hrest_of_instances_poly_coef
#print axioms DLMST.display_of_callout_poly_coef
#print axioms DLMST.display_of_strategy_of_calls_poly_coef
#print axioms DLMST.display_of_strategy_of_calls_count

#print axioms DLMST.card_le_card_of_isForest_of_ends
#print axioms DLMST.conn_nonempty
#print axioms DLMST.preF_nonempty_of_mem
#print axioms DLMST.CallOut.RoundData.toCall_kidE_card_lt
#print axioms DLMST.Strategy.roundData
#print axioms DLMST.Strategy.roundData_F
#print axioms DLMST.Strategy.ofScan
#print axioms DLMST.Strategy.ofScan_wf
#print axioms DLMST.Strategy.ofScan_strict
#print axioms DLMST.display_of_strategy_of_counts
#print axioms DLMST.card_le_two_mul_card_of_subset_ends
#print axioms DLMST.Strategy.ofScan_hnm
#print axioms DLMST.Strategy.clsOf
#print axioms DLMST.Strategy.ofBatches
#print axioms DLMST.Strategy.ofBatches_wf
#print axioms DLMST.Strategy.ofBatches_strict
#print axioms DLMST.Strategy.ofBatches_hnm
#print axioms DLMST.lemma37_project_error
#print axioms DLMST.CallOut.RoundData.card_U_le_error_slot
#print axioms DLMST.CallOut.RoundData.card_U_le_sum_slot
#print axioms DLMST.History.card_unsupp_le_lost
#print axioms DLMST.CallOut.RoundData.card_U_le_lost
#print axioms DLMST.error_count_le_of_U
#print axioms DLMST.lemma37_error
#print axioms DLMST.CallOut.RoundData.sum_kidE
#print axioms DLMST.CallPart.cover_eq
#print axioms DLMST.CallPart.partition
#print axioms DLMST.CallPart.lhs_le
#print axioms DLMST.CallPart.lhs_eq_of_no_drop
#print axioms DLMST.card_filter_or_le
#print axioms DLMST.CallOut.RoundData.card_U_le_pred
#print axioms DLMST.CallOut.RoundData.card_U_le_errOf
#print axioms DLMST.CallOut.RoundData.card_U_le_bad_add_mis
#print axioms DLMST.CallOut.RoundData.card_filter_bad_le_lost
#print axioms DLMST.CallOut.RoundData.card_U_le_lost_add_mis
#print axioms DLMST.error_count_le_of_U_add
#print axioms DLMST.sum_card_kid_le_inputs
#print axioms DLMST.card_mis_le
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound
#print axioms DLMST.CallOut.RoundData.sum_kidE_le_inputs
#print axioms DLMST.ProcChain.hpref
#print axioms DLMST.ProcChain.haction
#print axioms DLMST.ProcChain.level_error
#print axioms DLMST.ProcChain.errorOr_unsupp
#print axioms DLMST.ProcChain.supp_or_error
#print axioms DLMST.ProcChain.rejected_error
#print axioms DLMST.ProcChain.errOf_of_rejected_root
#print axioms DLMST.ProcChain.lemma37_error_proc
#print axioms DLMST.ProcChain.errOf_or_unsupp_child
#print axioms DLMST.ProcChain.errOf_of_supp_child
#print axioms DLMST.ProcChain.unSupp_errOf
#print axioms DLMST.ProcChain.card_U_le_number_bound_of_chains
#print axioms DLMST.ProcChain.card_U_le_lost_add_mis_add_child_fail
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound_of_all_mis
#print axioms DLMST.claim312_mis
#print axioms DLMST.mis_fiber_hper
#print axioms DLMST.card_mis_le_of_claim312
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound_of_sampling
#print axioms DLMST.ProcChain.card_U_le_number_bound_of_sampling_chains
#print axioms DLMST.ProcChain.conn
#print axioms DLMST.Strategy.clsOf_eq_some
#print axioms DLMST.Strategy.roundData_inp_subset
#print axioms DLMST.Strategy.sum_kidE_le_batches
#print axioms DLMST.CallOut.RoundData.card_filter_errOf_le
#print axioms DLMST.CallOut.RoundData.card_U_le_sum_levels
#print axioms DLMST.CallOut.RoundData.card_U_le_mul_of_sum_levels
#print axioms DLMST.ProcChain.exists_level_error
#print axioms DLMST.Witness.not_prefFind
#print axioms DLMST.Witness.msf
#print axioms DLMST.Witness.nonempty
#print axioms DLMST.CallOut.reindex_F
#print axioms DLMST.CallOut.sum_kidE_reindex
#print axioms DLMST.Strategy.display_of_counts
#print axioms DLMST.Strategy.ofRoundDataT
#print axioms DLMST.Strategy.ofRoundDataT_wf
#print axioms DLMST.Strategy.counts_of_roundDataT
#print axioms DLMST.CallOut.RoundData.card_U_le_display_form
#print axioms DLMST.CallOut.RoundData.sum_kidE_le_display_form
#print axioms DLMST.Strategy.display_of_roundData_sampling
#print axioms DLMST.Strategy.sum_kidE_le_paper_bound
#print axioms DLMST.Strategy.children_shrink
#print axioms DLMST.Strategy.cost_linear
#print axioms DLMST.Strategy.cost_linear_of_display
#print axioms DLMST.LevelChain.edges_halve
#print axioms DLMST.LevelChain.edges_pow_two_le
#print axioms DLMST.LevelChain.instance_card_mul_pow_le
#print axioms DLMST.LevelChain.pow_two_le_of_mem
#print axioms DLMST.LevelChain.level_lt_card
#print axioms DLMST.LevelChain.level_le_log2
#print axioms DLMST.LevelChain.t_level_le
#print axioms DLMST.Strategy.Cpaper
#print axioms DLMST.Strategy.Cpaper_nonneg
#print axioms DLMST.Strategy.display_of_roundData_nodes
#print axioms DLMST.Strategy.cost_linear_of_nodes
#print axioms DLMST.Strategy.cost_linear_of_nodes_exists
#print axioms DLMST.Strategy.htd_all_roots_impossible
#print axioms DLMST.LevelChain.card_le_two_mul_div_pow
#print axioms DLMST.Strategy.hnm_at
#print axioms DLMST.sampleSets_card
#print axioms DLMST.sampleSets_sep
#print axioms DLMST.per_round_mis
#print axioms DLMST.mis_count_of_sample
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound_of_queries
#print axioms DLMST.CallOut.RoundData.card_U_le_display_form_of_queries
#print axioms DLMST.card_le_card_sub_one_of_isForest_of_ends
#print axioms DLMST.card_roundIn_le
#print axioms DLMST.card_blkIn_le
#print axioms DLMST.CallOut.RoundData.sum_kidE_le_display_form_of_forests
#print axioms DLMST.schedToSlot
#print axioms DLMST.scanOfSlot_slot
#print axioms DLMST.scanOfSlot_cover
#print axioms DLMST.Strategy.ofSlot_wf
#print axioms DLMST.Strategy.ofSlot_strict
#print axioms DLMST.Strategy.ofSlot_hnm
#print axioms DLMST.Strategy.ofSlotLeaf_wf
#print axioms DLMST.Strategy.ofSlotLeaf_strict
#print axioms DLMST.Strategy.ofSlotLeaf_leaf
#print axioms DLMST.Strategy.ofSlotLeaf_hnm
#print axioms DLMST.Strategy.exists_ofSlot
#print axioms DLMST.Strategy.exists_ofSlot_noPortal
#print axioms DLMST.Strategy.exists_schedule_strategy
#print axioms DLMST.portalsOf_sub
#print axioms DLMST.portalsOf_budget
#print axioms DLMST.Strategy.exists_ofSlot_ofPortals
#print axioms DLMST.spokeOf
#print axioms DLMST.spokeOf_mem
#print axioms DLMST.spokeOf_incident
#print axioms DLMST.spokeOf_weight_le
#print axioms DLMST.selAt_nonempty
#print axioms DLMST.selAt_nonempty_of_adm
#print axioms DLMST.spokeSpec_selAt
#print axioms DLMST.spokeTable
#print axioms DLMST.spokeTable_mem
#print axioms DLMST.spokeTable_incident
#print axioms DLMST.spokeSpec_table
#print axioms DLMST.batchSpec_selAt
#print axioms DLMST.exists_batchSpec
#print axioms DLMST.keyOf
#print axioms DLMST.keyOf_injective
#print axioms DLMST.maxima_vector_determined_nat
#print axioms DLMST.argmaxFamily
#print axioms DLMST.toSymMap
#print axioms DLMST.argmaxFamily_card_le
#print axioms DLMST.candFamily
#print axioms DLMST.candFamily_card_le
#print axioms DLMST.log_candFamily_le
#print axioms DLMST.rOf
#print axioms DLMST.exists_key_dominator_iff
#print axioms DLMST.mem_candFamily_of_trail_form
#print axioms DLMST.spokePair
#print axioms DLMST.pathSet
#print axioms DLMST.mem_pathSet_of_trail
#print axioms DLMST.geoPref
#print axioms DLMST.prefFind_iff_conn_of_bothSpokes
#print axioms DLMST.actOf_eq_geoPref
#print axioms DLMST.actOf_eq_geoPref_keyOf
#print axioms DLMST.groundSet
#print axioms DLMST.groundSet_card_le
#print axioms DLMST.roundS
#print axioms DLMST.mem_roundS
#print axioms DLMST.roundCand
#print axioms DLMST.truth_mem_roundCand
#print axioms DLMST.roundCand_card_le
#print axioms DLMST.log_roundCand_le
#print axioms DLMST.geomFamily
#print axioms DLMST.truth_of_history
#print axioms DLMST.geomFamily_nonempty
#print axioms DLMST.est_of_choice
#print axioms DLMST.geomFamily_card_le
#print axioms DLMST.log_geomFamily_le
#print axioms DLMST.truth_of_history_slot
#print axioms DLMST.card_U_le_display_form_of_geometry
#print axioms DLMST.IsForest.subset
#print axioms DLMST.roundIdx
#print axioms DLMST.roundIdx_le_of_le
#print axioms DLMST.History.ofData
#print axioms DLMST.History.ofData_consistent
#print axioms DLMST.forestUpTo
#print axioms DLMST.forestUpTo_sub
#print axioms DLMST.isForest_forestUpTo
#print axioms DLMST.forestUpTo_grow
#print axioms DLMST.historyOfRoundData
#print axioms DLMST.historyOfRoundData_consistent
#print axioms DLMST.isForest_historyOfRoundData
#print axioms DLMST.monoRow_historyOfRoundData
#print axioms DLMST.historyOfTable
#print axioms DLMST.historyOfTable_spoke_incident
#print axioms DLMST.prefAct
#print axioms DLMST.badOf
#print axioms DLMST.lostOf
#print axioms DLMST.historyOfRoundData_lost
#print axioms DLMST.historyOfRoundData_errOf
#print axioms DLMST.card_U_le_display_form_of_roundData
#print axioms DLMST.card_U_le_display_form_of_roundData_actOf
#print axioms DLMST.geomFamily_log_ceil_le
#print axioms DLMST.sum_sqrt_card_fibre_le
#print axioms DLMST.sampleSets_geomFamily_card_le
#print axioms DLMST.sampleSets_geomFamily_sum_le
#print axioms DLMST.sampleSets_geomFamily_sum_le_sqrt
#print axioms DLMST.selAt_adm
#print axioms DLMST.selAt_notMem
#print axioms DLMST.spokeTable_notMem
#print axioms DLMST.historyOfTable_spoke
#print axioms DLMST.historyOfTable_forest
#print axioms DLMST.historyOfTable_pref
#print axioms DLMST.hFsp_of_spokes_notMem
#print axioms DLMST.hFsp_historyOfTable
#print axioms DLMST.card_U_le_display_form_of_table
#print axioms DLMST.card_U_le_number_bound_of_table
#print axioms DLMST.DriverCall.sc
#print axioms DLMST.DriverCall.sc_sub
#print axioms DLMST.DriverCall.sc_cover
#print axioms DLMST.DriverCall.cls
#print axioms DLMST.DriverCall.cls_total
#print axioms DLMST.DriverCall.roundData
#print axioms DLMST.DriverCall.roundData_F
#print axioms DLMST.DriverCall.roundData_F_sub
#print axioms DLMST.DriverCall.roundData_U_sub
#print axioms DLMST.DriverCall.sched
#print axioms DLMST.DriverCall.sched_slot
#print axioms DLMST.DriverCall.history
#print axioms DLMST.DriverCall.history_consistent
#print axioms DLMST.DriverCall.history_isForest
#print axioms DLMST.DriverCall.history_hFsp
#print axioms DLMST.DriverCall.eN
#print axioms DLMST.DriverCall.Evidence.card_U_le_number_bound
#print axioms DLMST.DriverCall.Evidence.card_U_le_root
#print axioms DLMST.DriverCall.driverRoundData
#print axioms DLMST.DriverCall.driverHistory
#print axioms DLMST.DriverCall.driverStrategy
#print axioms DLMST.DriverCall.driverStrategy_wf
#print axioms DLMST.DriverCall.driverStrategy_call
#print axioms DLMST.DriverCall.driverStrategy_F
#print axioms DLMST.DriverCall.driverStrategy_U
#print axioms DLMST.DriverCall.driverScheme_herrU
#print axioms DLMST.DriverCall.driverScheme_herrU_root
#print axioms DLMST.DriverCall.driverScheme_counts
#print axioms DLMST.DriverCall.display_of_driver
#print axioms DLMST.DriverCall.F_nonempty
#print axioms DLMST.DriverCall.kidE_card_lt
#print axioms DLMST.DriverCall.kidE_card_lt_of_nonempty
#print axioms DLMST.DriverCall.slotFirst
#print axioms DLMST.DriverCall.ofSlot
#print axioms DLMST.DriverCall.ofSlot_noPortal
#print axioms DLMST.DriverCall.ofSlot_portals
#print axioms DLMST.DriverCall.firstCall
#print axioms DLMST.DriverCall.driverCallFirst
#print axioms DLMST.DriverCall.driverStrategy_strict
#print axioms DLMST.DriverCall.driverStrategyLeaf
#print axioms DLMST.DriverCall.driverStrategyLeaf_wf
#print axioms DLMST.DriverCall.driverStrategyLeaf_strict
#print axioms DLMST.DriverCall.driverStrategyLeaf_leaf
#print axioms DLMST.DriverCall.driverStrategyLeaf_eq
#print axioms DLMST.DriverCall.driverScheme_terminates
#print axioms DLMST.DriverCall.driverScheme_chain_empty
#print axioms DLMST.DriverCall.ofSchedule
#print axioms DLMST.DriverCall.sched_ofSchedule
#print axioms DLMST.History.lostOn
#print axioms DLMST.History.lostOn_le_lost
#print axioms DLMST.History.weighted_sum_le_on
#print axioms DLMST.History.lemma311_on
#print axioms DLMST.card_mis_leOn
#print axioms DLMST.sampleSetsOn
#print axioms DLMST.sampleSetsOn_card
#print axioms DLMST.sampleSetsOn_sep
#print axioms DLMST.per_round_misOn
#print axioms DLMST.mis_count_of_sampleOn
#print axioms DLMST.estOfOn
#print axioms DLMST.estOfOn_of_mem
#print axioms DLMST.geomFamilyOn
#print axioms DLMST.truth_of_historyOn
#print axioms DLMST.est_of_choiceOn
#print axioms DLMST.truth_of_history_slotOn
#print axioms DLMST.CallOut.RoundData.card_U_le_lost_add_misOn
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound_of_all_misOn
#print axioms DLMST.CallOut.RoundData.card_U_le_number_bound_of_queriesOn
#print axioms DLMST.card_U_le_number_bound_of_tableOn
#print axioms DLMST.DriverCall.EvidenceOn
#print axioms DLMST.DriverCall.EvidenceOn.card_U_le_number_bound
#print axioms DLMST.DriverCall.driverScheme_herrU_on

#print axioms DLMST.Strategy.hn_root_of_phases
#print axioms DLMST.Strategy.hn_root_of_phases_le
#print axioms DLMST.Strategy.cost_linear_of_contraction
#print axioms DLMST.Strategy.cost_linear_of_contraction_exists

#print axioms DLMST.compOn
#print axioms DLMST.mem_compOn
#print axioms DLMST.compOn_subset
#print axioms DLMST.compCountOn
#print axioms DLMST.mem_conn_iff
#print axioms DLMST.eq_of_conn_of_notMem
#print axioms DLMST.compOn_eq_comp
#print axioms DLMST.comp_eq_singleton_of_notMem
#print axioms DLMST.compCount_eq_sdiff_add_compCountOn
#print axioms DLMST.card_add_compCountOn
#print axioms DLMST.compCountOn_insert
#print axioms DLMST.compOn_empty_eq
#print axioms DLMST.compOn_empty_of_notMem
#print axioms DLMST.compCountOn_empty
#print axioms DLMST.compCountOn_halves
#print axioms DLMST.compCountOn_pow_halves
#print axioms DLMST.compCountOn_le_div_pow
#print axioms DLMST.compCountOn_le_real
#print axioms DLMST.compCountOn_le_real_of_card_le
#print axioms DLMST.four_le_pow_two_two_mul
#print axioms DLMST.four_mul_compCountOn_le
#print axioms DLMST.card_le_compCountOn_of_pairwise_not_conn
#print axioms DLMST.four_mul_card_le_of_phases
#print axioms DLMST.hcontract_of_phases
#print axioms DLMST.cover_on_of_cover
#print axioms DLMST.compCountOn_halves_of_cover
#print axioms DLMST.BorPhaseIn
#print axioms DLMST.BorPhase.toIn
#print axioms DLMST.BorPhaseIn.erase
#print axioms DLMST.BorPhaseIn.not_mem
#print axioms DLMST.BorPhaseIn.nloop
#print axioms DLMST.boruvka_forest_in
#print axioms DLMST.compCountOn_halves_in
#print axioms DLMST.compCountOn_pow_halves_in
#print axioms DLMST.compCountOn_le_div_pow_in
#print axioms DLMST.compCountOn_le_real_in
#print axioms DLMST.compCountOn_le_real_in_of_card_le
#print axioms DLMST.compCountOn_halves_of
#print axioms DLMST.BorPhaseInAt
#print axioms DLMST.BorPhaseIn.toAt
#print axioms DLMST.BorPhaseInAt.erase
#print axioms DLMST.BorPhaseInAt.not_mem
#print axioms DLMST.BorPhaseInAt.nloop
#print axioms DLMST.boruvka_forest_in_at
#print axioms DLMST.compCountOn_halves_in_at
#print axioms DLMST.compCountOn_pow_halves_in_at
#print axioms DLMST.compCountOn_le_real_in_at
#print axioms DLMST.compOn_congr
#print axioms DLMST.phaseIn
#print axioms DLMST.mem_phaseIn
#print axioms DLMST.phaseIn_subset
#print axioms DLMST.phaseIn_borPhaseInAt
#print axioms DLMST.phaseIn_cover
#print axioms DLMST.compCountOn_halves_phaseIn
#print axioms DLMST.compCountOn_le_real_phaseIn
#print axioms DLMST.compCountOn_le_real_phaseIn_of_card_le
#print axioms DLMST.exists_reps
#print axioms DLMST.hcontract_of_phaseIn
#print axioms DLMST.compOn_eq_of_mem_inter
#print axioms DLMST.disjoint_compOn
#print axioms DLMST.pairwise_disjoint_compOn
#print axioms DLMST.biUnion_compOn
#print axioms DLMST.exists_reps_conn

/-! 第三十八批：收缩骨架（`Contract.lean`） -/
#print axioms DLMST.compOn_nonempty
#print axioms DLMST.repOf
#print axioms DLMST.repOf_of_mem
#print axioms DLMST.repOf_mem
#print axioms DLMST.conn_repOf
#print axioms DLMST.compOn_repOf
#print axioms DLMST.repOf_eq_of_compOn_eq
#print axioms DLMST.repOf_idem
#print axioms DLMST.crossE
#print axioms DLMST.cGraph
#print axioms DLMST.mem_crossE
#print axioms DLMST.crossE_subset
#print axioms DLMST.disjoint_crossE_F
#print axioms DLMST.conn_contract

/-! 第三十九批：收缩的完备性 -/
#print axioms DLMST.conn_cGraph_of_conn
#print axioms DLMST.repOf_ne_of_crossE

/-! 第四十批：收缩保持连通性与代表点集 -/
#print axioms DLMST.repSet
#print axioms DLMST.mem_repSet
#print axioms DLMST.repOf_mem_repSet
#print axioms DLMST.repSet_subset
#print axioms DLMST.image_subtype_crossE
#print axioms DLMST.conn_iff_conn_cGraph

/-! 第四十一批：代表点集的基数 = 实例分量数 -/
#print axioms DLMST.repOf_repSet
#print axioms DLMST.image_compOn_eq_repSet_image
#print axioms DLMST.card_image_compOn_repSet
#print axioms DLMST.repSet_card

/-! 第四十二–四十三批：分量像的收缩对应与分量计数不变性 -/
#print axioms DLMST.compOn_image_repOf
#print axioms DLMST.image_image_repOf
#print axioms DLMST.image_repOf_injOn
#print axioms DLMST.compCountOn_eq_cGraph

/-! 第四十四批：收缩图接口与生成性质上提升 -/
#print axioms DLMST.crossE_nloop
#print axioms DLMST.cGraph_src
#print axioms DLMST.cGraph_dst
#print axioms DLMST.cGraph_weight
#print axioms DLMST.conn_union_span_cGraph
#print axioms DLMST.conn_edge_span_cGraph
#print axioms DLMST.wsum_cGraph

/-! 第四十五批：孩子森林向上提升 -/
#print axioms DLMST.isForest_union_cGraph

/-! 第四十六批：收缩孩子的规模递推 -/
#print axioms DLMST.repSet_card_halves_phaseIn
#print axioms DLMST.repSet_card_le
#print axioms DLMST.repSet_card_le_of_card_le

/-! 第四十七批：收缩边的计数拆分与单孩子的门户预算形状 -/
#print axioms DLMST.disjoint_F_of_subset_crossE
#print axioms DLMST.card_union_of_subset_crossE
#print axioms DLMST.four_mul_repSet_card_le

/-! 第四十八批：孩子森林的规模界 -/
#print axioms DLMST.child_forest_card_le
#print axioms DLMST.four_mul_child_forest_card_le

/-! 第四十九批：收缩边就是 §1.2 的不支持边 -/
#print axioms DLMST.conn_of_supported
#print axioms DLMST.crossE_subset_unsupp
#print axioms DLMST.crossE_card_le
#print axioms DLMST.repSet_card_le_card

/-! 第五十批：一层递归是可靠的 -/
#print axioms DLMST.isForest_span_of_child

/-! 第五十一批：孩子实例的形状保持与权重的可加性 -/
#print axioms DLMST.cGraph_src_mem_repSet
#print axioms DLMST.cGraph_dst_mem_repSet
#print axioms DLMST.cGraph_hP
#print axioms DLMST.wsum_union_of_subset_crossE
#print axioms DLMST.wsum_union_eq_child_wsum

/-! 第五十二批：孩子的优化就是父亲的优化 -/
#print axioms DLMST.wsum_splice_le_iff

/-! 第五十三批：收缩反向保持森林性 -/
#print axioms DLMST.isForest_cGraph_of_union

/-! 第五十四批：生成性双向对应与最小性下移 -/
#print axioms DLMST.span_cGraph_of_span
#print axioms DLMST.span_iff_span_cGraph
#print axioms DLMST.splice_minimal

/-! 第五十五批：§4 收缩递归一步的记录 -/
#print axioms DLMST.ContractStep.forest_span
#print axioms DLMST.ContractStep.child_shape
#print axioms DLMST.ContractStep.wsum_splice
#print axioms DLMST.ContractStep.optimal

/-! 第五十六批：森林 = 保留边 + 收缩边 -/
#print axioms DLMST.mem_crossE_of_mem_of_not_mem
#print axioms DLMST.eq_union_inter_crossE
#print axioms DLMST.wsum_eq_add_inter_crossE

/-! 第五十七批：含 F 的生成森林投影为收缩实例的生成森林 -/
#print axioms DLMST.isSpanningForest_cGraph_of_union

/-! 第五十八批：收缩保持最优性（交换论证） -/
#print axioms DLMST.isMSF_union_cGraph

/-! 第五十九批：交换论证的实例形式（`IsMSFOf G E₀`） -/
#print axioms DLMST.isMSFOf_union_cGraph
#print axioms DLMST.ContractStep.isMSFOf_union

/-! 第六十批：孩子返回 MSF ⟹ 拼接返回 MSF -/
#print axioms DLMST.isMSFOf_union_cGraph_child

/-! 第六十一批：§4 一步「既正确又小」 -/
#print axioms DLMST.contract_step_sound_and_small

/-! 第六十二批：实例层的交换与蓝规则 -/
#print axioms DLMST.IsMSFOf.exchange
#print axioms DLMST.boruvka_blue_rule_of

/-! 第六十三批：实例上的多切蓝规则 -/
#print axioms DLMST.exists_trail_crossing_of
#print axioms DLMST.boruvka_round_of

/-! 第六十四批：相位链在实例内始终安全 -/
#print axioms DLMST.phaseIn_round_of
#print axioms DLMST.phaseChain_safe

/-! 第六十五批：§4 一步无需 MSF 假设 -/
#print axioms DLMST.contract_step_sound_and_small'

/-! 第六十六批：§4 递归下沉两层 -/
#print axioms DLMST.repSet_card_pos
#print axioms DLMST.contract_two_levels

/-! 第六十七批：§4 一步只需相位数据（森林免费） -/
#print axioms DLMST.isForest_phaseChain
#print axioms DLMST.contract_step_sound_and_small''
#print axioms DLMST.contract_two_levels''

/-! 第六十八批：两层的成本账 -/
#print axioms DLMST.subtype_image_subtype
#print axioms DLMST.wsum_union_image_eq_add_child
#print axioms DLMST.wsum_two_levels

/-! 第六十九批：激活假设由连通性推出 -/
#print axioms DLMST.leaves_of_conn_E₀
#print axioms DLMST.hact_of_conn_E₀
#print axioms DLMST.contract_step_sound_and_small_conn

/-! 第七十批：§4 的调用记录 `ContractCall` -/
#print axioms DLMST.ContractCall.kidV
#print axioms DLMST.ContractCall.kidE
#print axioms DLMST.ContractCall.forest
#print axioms DLMST.ContractCall.subset
#print axioms DLMST.ContractCall.spanning
#print axioms DLMST.ContractCall.kidV_pos
#print axioms DLMST.ContractCall.card_le_kidV
#print axioms DLMST.contractCall_of_phases
#print axioms DLMST.contractCall_of_conn
#print axioms DLMST.contractCall_of_two_levels

/-! 第七十一批：§4 任意深度的收缩塔（扁平化） -/
#print axioms DLMST.phaseChain
#print axioms DLMST.cGraphFlat
#print axioms DLMST.lvlData
#print axioms DLMST.lvlGraph
#print axioms DLMST.lvlVerts
#print axioms DLMST.lvlE
#print axioms DLMST.lvlForest
#print axioms DLMST.lvlGraph_succ
#print axioms DLMST.lvlVerts_succ
#print axioms DLMST.lvlE_succ
#print axioms DLMST.lvlGraph_src_succ
#print axioms DLMST.lvlGraph_dst_succ
#print axioms DLMST.lvlForest_eq_chain
#print axioms DLMST.lvlVerts_succ_chain
#print axioms DLMST.lvl_hPE
#print axioms DLMST.lvlVerts_pos
#print axioms DLMST.four_pow_mul_lvlVerts_le
#print axioms DLMST.conn_cGraphFlat_iff
#print axioms DLMST.isForest_image_of_cGraph
#print axioms DLMST.isForest_cGraph_of_image
#print axioms DLMST.wsum_cGraphFlat_image
#print axioms DLMST.isMSFOf_cGraph_of_flat
#print axioms DLMST.answer
#print axioms DLMST.tower_sound
#print axioms DLMST.tower_small

/-! 第七十二批：权重与规模望远镜（`Tower.lean`） -/
#print axioms DLMST.lvlGraph_weight
#print axioms DLMST.wsum_lvlGraph
#print axioms DLMST.phaseChain_subset
#print axioms DLMST.lvlForest_succ
#print axioms DLMST.lvlForest_subset_lvlE
#print axioms DLMST.lvlE_succ_subset
#print axioms DLMST.disjoint_lvlForest_lvlE_succ
#print axioms DLMST.disjoint_lvlForest_of_subset
#print axioms DLMST.tower_wsum
#print axioms DLMST.tower_wsum_lvl
#print axioms DLMST.tower_card

/-! 第七十三批：塔的逐层激活（`Tower.lean`） -/
#print axioms DLMST.tower_hact_of_lvl_conn
#print axioms DLMST.tower_sound_conn
#print axioms DLMST.tower_small_conn

/-! 第七十四批：§4 的策略记录（`ContractStrategy.lean`） -/
#print axioms DLMST.contractOut
#print axioms DLMST.contractOut_P
#print axioms DLMST.contractOut_E₀
#print axioms DLMST.ContractWf
#print axioms DLMST.contractStrategy
#print axioms DLMST.contractStrategy_wf
#print axioms DLMST.contractStrategy_answer_isMSF
#print axioms DLMST.contractStrategy_smallV
#print axioms DLMST.contractStrategy_smallE

/-! 第七十五批：§4 在平凡底部终止（`Tower.lean`） -/
#print axioms DLMST.lvlE_subset
#print axioms DLMST.isMSFOf_empty_of_card_le_one
#print axioms DLMST.lvlVerts_card_le_one
#print axioms DLMST.tower_terminates
#print axioms DLMST.tower_terminates_card

/-! 第七十六批：§4 策略的孩子答案改为选取（`ContractStrategy.lean`） -/
#print axioms DLMST.contractStrategyAuto
#print axioms DLMST.contractStrategyAuto_wf
#print axioms DLMST.contractStrategyAuto_answer
#print axioms DLMST.contractStrategyConn
#print axioms DLMST.contractStrategyConn_wf
#print axioms DLMST.contractStrategyConn_answer

/-! 第七十七批：塔的平移——孩子实例就是下一层（`Tower.lean`） -/
#print axioms DLMST.lvlData_shift
#print axioms DLMST.lvlGraph_shift
#print axioms DLMST.lvlVerts_shift
#print axioms DLMST.lvlE_shift
#print axioms DLMST.lvlForest_shift
#print axioms DLMST.hact_shift
#print axioms DLMST.answer_splice
#print axioms DLMST.tower_sound_child
#print axioms DLMST.tower_terminates_child

/-! 第七十八批：§4 的自调用——孩子就是递归自己的输出（`ContractStrategy.lean`） -/
#print axioms DLMST.lvlForest_zero
#print axioms DLMST.lvlGraph_one
#print axioms DLMST.lvlVerts_one
#print axioms DLMST.lvlE_one
#print axioms DLMST.childAnswer
#print axioms DLMST.crossChild
#print axioms DLMST.childAnswer_subset
#print axioms DLMST.crossChild_image
#print axioms DLMST.isMSFOf_crossChild
#print axioms DLMST.contractOutOfTower
#print axioms DLMST.contractOutOfTower_answer
#print axioms DLMST.contractOutOfTower_splice
#print axioms DLMST.four_mul_lvlVerts_succ_le
#print axioms DLMST.childBd
#print axioms DLMST.contractOutOfTower_rec
#print axioms DLMST.contractStrategyTower
#print axioms DLMST.contractStrategyTower_wf
#print axioms DLMST.contractStrategyTower_answer

/-! 第七十九批：§4 的显示——塔的总规模是线性的（`ContractStrategy.lean`） -/
#print axioms DLMST.three_mul_sum_lvlVerts_le
#print axioms DLMST.lvlForest_card_le_lvlVerts
#print axioms DLMST.three_mul_sum_lvlForest_le
#print axioms DLMST.answer_card_le_third
#print axioms DLMST.contractDisplay

-- 第八十批：节点/孩子的成本（ContractStrategy.lean）
#print axioms DLMST.crossChild_card
#print axioms DLMST.contractOutOfTower_smallE
#print axioms DLMST.childAnswer_card_le_third
#print axioms DLMST.contractStrategy_answer_card_le

-- 第八十一批：塔的工作量测度（ContractStrategy.lean）
#print axioms DLMST.lvlE_card_le
#print axioms DLMST.sum_lvlE_le
#print axioms DLMST.levelWork
#print axioms DLMST.tower_work_le
#print axioms DLMST.phase_card_add_cross_le
#print axioms DLMST.contractStrategy_answer_card_le_edges
#print axioms DLMST.contractStrategyTower_display

-- 第八十二批：深度索引的递归树（ContractStrategy.lean）
#print axioms DLMST.ContractTree
#print axioms DLMST.treeOfBd
#print axioms DLMST.treeOfBd_fst
#print axioms DLMST.treeOfBd_answer
#print axioms DLMST.treeOfBd_splice
#print axioms DLMST.treeOfBd_wsum
#print axioms DLMST.treeOfBd_sound
#print axioms DLMST.treeOfBd_card_le

-- 第八十三批：条件线性（ContractStrategy.lean）
-- 第九十四批已删除（边减半前提被 G8 反驳）

-- 第八十四批：打包主定理（Main.lean）
#print axioms DLMST.TowerInputs
#print axioms DLMST.mst_main
#print axioms DLMST.mst_main_weight

-- 第八十五批：无参数深度（ContractStrategy.lean + Main.lean）
#print axioms DLMST.card_le_pow_log
#print axioms DLMST.tower_terminates_log
#print axioms DLMST.tower_terminates_log_card
#print axioms DLMST.contractDisplay_log
#print axioms DLMST.mst_main_log

-- 第八十六批：无参数递归树（ContractStrategy.lean）
#print axioms DLMST.lvlVerts_one_card_le
#print axioms DLMST.lvlVerts_one_card_le_pow
#print axioms DLMST.treeOfLog
#print axioms DLMST.treeOfLog_sound
#print axioms DLMST.treeOfLog_card_le

-- 第八十七批：无参数工作量（ContractStrategy.lean）
#print axioms DLMST.tower_work_log
-- 第九十四批已删除：tower_work_log_of_halving（边减半前提被 G8 反驳）

-- 第八十八批：森林界的锐化（ContractStrategy.lean）
#print axioms DLMST.answer_card_le_sub_one
#print axioms DLMST.tower_terminates_log_card_sub_one
#print axioms DLMST.contractStrategy_answer_card_le_sub_one

-- 第八十九批：根连通推出逐层激活（Tower.lean + InstancePhase.lean）
#print axioms DLMST.hact_of_connOn_E₀
#print axioms DLMST.lvlVerts_subset
#print axioms DLMST.lvlVerts_card_le
#print axioms DLMST.conn_union_crossE_of_conn
#print axioms DLMST.conn_cGraphFlat_of_conn
#print axioms DLMST.lvl_conn_succ
#print axioms DLMST.lvl_connOn_of_root_conn
#print axioms DLMST.tower_hact_of_lvl_connOn
#print axioms DLMST.tower_sound_connOn
#print axioms DLMST.tower_hact_of_root_conn

-- 第九十批：根连通终止与主定理（ContractStrategy.lean + Main.lean）
#print axioms DLMST.tower_terminates_log_root_conn
#print axioms DLMST.mst_main_root_conn

-- 第九十一批：激活前提的真实边界与停机接口（Tower.lean + ContractStrategy.lean + Main.lean）
#print axioms DLMST.tower_sound_bd
#print axioms DLMST.tower_msf_of_stop
#print axioms DLMST.tower_msf_of_stop_card
#print axioms DLMST.not_activated_of_card_le_one
#print axioms DLMST.activated_false_of_pos
#print axioms DLMST.root_conn_false_of_pos
#print axioms DLMST.towerInputs_false
#print axioms DLMST.mst_main_log_hypotheses_false
#print axioms DLMST.mst_main_root_conn_hypotheses_false
#print axioms DLMST.mst_main_stop

-- 第九十二批：4 顶点实例的非空洞见证（StopWitness.lean）
#print axioms DLMST.phaseIn_one
#print axioms DLMST.conn_pair_iff
#print axioms DLMST.phaseIn_two
#print axioms DLMST.phaseChain_one
#print axioms DLMST.phaseChain_two
#print axioms DLMST.conn_final
#print axioms DLMST.compOn_final
#print axioms DLMST.compCount_final
#print axioms DLMST.stop_hstop
#print axioms DLMST.stop_hact
#print axioms DLMST.stop_witness_answer
#print axioms DLMST.stop_witness_value
#print axioms DLMST.stop_witness

-- 第九十三批：线性口径与边减半反例（LinearTime.lean）
#print axioms DLMST.four_pow_mul_lvlVerts_le_bd
#print axioms DLMST.three_mul_sum_lvlVerts_le_bd
#print axioms DLMST.tower_work_le_bd
#print axioms DLMST.counting_log_stop
#print axioms DLMST.mst_main_stop_log
#print axioms DLMST.wOrd_G8
#print axioms DLMST.leaves_matchE
#print axioms DLMST.src_intra
#print axioms DLMST.pairC_match
#print axioms DLMST.half_match
#print axioms DLMST.half_cross
#print axioms DLMST.conn_pairC
#print axioms DLMST.conn_half
#print axioms DLMST.F1_subset
#print axioms DLMST.phaseChain1_G8
#print axioms DLMST.not_conn_intra
#print axioms DLMST.leaves_of_endpoints
#print axioms DLMST.leaves_intra
#print axioms DLMST.F2_le
#print axioms DLMST.phaseChain_two_le
#print axioms DLMST.phaseChain_two_half
#print axioms DLMST.cross_not_conn
#print axioms DLMST.crossE_card_ge
#print axioms DLMST.lvlE0_G8
#print axioms DLMST.lvlE1_G8
#print axioms DLMST.not_halving_zero
#print axioms DLMST.hshr_refuted
#print axioms DLMST.hshr_refuted_stop

-- 第九十四批：删去边减半条件定理，改用论文路线（LinearTime.lean）
-- 已删除：sum_halving_le_two_mul / tower_work_le_of_halving / tower_work_log_of_halving
--         sum_halving_le_two_mul_bd / tower_work_le_bd_of_halving / counting_linear_stop_of_halving
#print axioms DLMST.counting_linear_of_display

-- 第九十五批：LevelLinear.lean —— §3.6 层模型总工作量线性（不用边减半）
#print axioms DLMST.level_edges_summable
#print axioms DLMST.level_verts_summable
#print axioms DLMST.level_work_linear
#print axioms DLMST.chain_verts_cast_le
#print axioms DLMST.chain_edges_cast_le
#print axioms DLMST.chain_work_linear
#print axioms DLMST.chain_display_of_calls
#print axioms DLMST.chain_work_linear_of_calls

-- 第九十六批：LevelWork.lean —— §3.6 逐调用计数（t_d = γ(d+1)³）⟹ 层链总工作量线性
-- chain_edges_display：一层边总数由各调用自身的计数给出（Level.errors_le_coef +
--   (n_a−1) ≤ n_a 放宽 + (8t³)² = 64t⁶）
-- level_work_poly：算术核心 —— 层级系数 γ²(d+1)⁶、γ⁷(d+1)²¹ 由顶点 4^{-d} 衰减吸收
--   （Section36 的 sum_pow6_div_two_pow_le / sum_pow6_div_four_pow_le / sum_pow21_div_four_pow_le）
-- chain_work_linear_counts：两者合体（同一 γ、无统一 C、无边减半、无 htd）
#print axioms DLMST.chain_edges_display
#print axioms DLMST.level_work_poly
#print axioms DLMST.chain_work_linear_counts

-- 第九十七批：接口对齐 —— 减半 ⟹ 严格递减；逐调用计数只需断言到深度 |E₀|
-- CostLinear.strict_of_shrink：Σ|kidE| ≤ |E₀|/2 ⟹ 每个孩子严格更小（Strategy.Strict 成为结论）
-- CostLinear.cost_linear_of_shrink：cost_linear 去掉 hstr 前提
-- LevelWork.forall_chain_of_le_card：d ≤ |E₀| 上的逐调用断言推广到所有层（深层为空）
-- LevelWork.chain_work_linear_of_counts_bounded：总工作量线性只吃「深度 ≤ |E₀|」形式的两个计数
#print axioms DLMST.Strategy.strict_of_shrink
#print axioms DLMST.Strategy.cost_linear_of_shrink
#print axioms DLMST.forall_chain_of_le_card
#print axioms DLMST.chain_work_linear_of_counts_bounded

-- 第九十八批：§3.6 的两个结论共用同一组前提（一次调用的两个数值输出 + 深度 ≤ |E₀|）
-- strategy_display_and_work：显示式（常数 √2+γ²·800000+√2(2γ²+γ+64γ⁷)·202²¹·2）
--   ∧ 各层总工作量线性，前提完全相同，不再需要逐实例非空
#print axioms DLMST.strategy_display_and_work

-- 第九十九批：p. 24 输入计数的自然数减法形式（退化 (∅,∅) 实例上可满足）
-- input_poly_of_nat：2t²(n−1)⁺ + t((n−1)⁺+r²n) ≤ (2γ²+γ+64γ⁷)(d+1)²¹n（d+1 ≥ 1）
-- display_of_strategy_of_nat_counts：显示式从 ((n−1:ℕ):ℝ) 形式出发，同一常数、无 hpos
#print axioms DLMST.input_poly_of_nat
#print axioms DLMST.display_of_strategy_of_nat_counts

-- 第一百批：§4 收缩递归无法填入 `CallOut`（边界 B1）——冲突本身机检
-- 第三十一批起的文档一直把这个缺口写在注释里；本批把它变成定理：
-- CallOut.supported_of_mem_kidE：hUkid 使每个孩子边都被 F 支持（§4 的跨边恰恰不被支持）
-- CallOut.disjoint_crossE_kidE：crossE ⊆ unsupp ∩ E₀ ⟹ 孩子边集与整个 crossE 不交
-- CallOut.not_subset_kidE_of_crossE：非空的跨边子集不能是任何孩子输入（no-go）
-- CallOut.not_mem_kidE_of_phase：§4 相位里 M ⊇ F 的差集边必是跨边，故确实收不到——非空洞
#print axioms DLMST.CallOut.supported_of_mem_kidE
#print axioms DLMST.CallOut.disjoint_crossE_kidE
#print axioms DLMST.CallOut.not_subset_kidE_of_crossE
#print axioms DLMST.CallOut.not_mem_kidE_of_phase

-- 第一百零一批：§4 塔的**可满足**显示包（B3 的非空洞对应物）
-- tower_stop_display：停机形式（激活只在 d < D、|lvlVerts D| ≤ 1）下同时给出
--   MSF（tower_msf_of_stop）+ 权重望远镜（tower_wsum）
--   + |answer| ≤ |P|−1（tower_msf_of_stop_card，越过 4/3 预算）
--   + 逐层 1/4 顶点收缩 + 计数工作量 3·totalWork ≤ 4|P| + 3D|E₀|（tower_work_le_bd）
#print axioms DLMST.tower_stop_display

/-! ## 第一百零二批：`tower_stop_display` 在 4 顶点实例上的非空洞实例化 -/

#print axioms DLMST.stop_display_witness
#print axioms DLMST.stop_display_witness_values

/-! ## 第一百零三批：§4 塔作为 §3.6 计数层链，显示式在 §4 节点上成立 -/

#print axioms DLMST.towerLevel
#print axioms DLMST.towerLevel_step
#print axioms DLMST.tower_partition
#print axioms DLMST.tower_forest_add_kid_le
#print axioms DLMST.towerKidE_subset_unsupp
#print axioms DLMST.tower_display_rest

/-! ## 第一百零四–一百零六批：有界激活的层链、多项式显示、端到端组装及其非空洞见证 -/

#print axioms DLMST.emptyLevel
#print axioms DLMST.towerLevelChain
#print axioms DLMST.towerLevelChain_step
#print axioms DLMST.tower_display_poly
#print axioms DLMST.tower_e2e
#print axioms DLMST.tower_e2e_witness

/-! ## 第一百零七批：B2 分支递归（§3.6 的逐实例计数 ⟹ 逐实例线性） -/

-- displayC：§3.6 的常数 C_ε（= √2 + γ²·800000 + √2·((2γ²+γ+64γ⁷)·202²¹·2)）
-- kidE_le_of_display：F+U+Σ|孩子| ≤ … ⟹ 仅孩子的显示式（F、U 非负）
-- kidE_display_of_counts：逐节点计数（hU、轮次、n≤2m）⟹ 每个实例的孩子显示 Σ|Eᵢ| ≤ εm + C√(mn)
-- child_shrink_of_counts：再加 ε ≤ 1/8、C·2/2^j ≤ 3/8、n ≤ 2m/2^{2j} ⟹ Σ|Eᵢ| ≤ m/2
-- cost_linear_of_counts：任意计数代价 T 沿策略递归 T ≤ ΣT(kid) + c|E₀| ⟹ 每个实例 T ≤ 2c|E₀|
-- exists_displayC_phase：对任意 γ、任意 C 都存在相位 j 使 C·2/2^j ≤ 3/8（相位数不预设）
#print axioms DLMST.displayC
#print axioms DLMST.displayC_nonneg
#print axioms DLMST.Strategy.kidE_le_of_display
#print axioms DLMST.Strategy.kidE_display_of_counts
#print axioms DLMST.Strategy.child_shrink_of_counts
#print axioms DLMST.Strategy.cost_linear_of_counts
#print axioms DLMST.exists_displayC_phase

/-! ## 第一百零八批：B4 概率层（有限均匀分布、Markov、尾界、Claim 3.12 的成功概率） -/

-- unifProb/unifExpect：有限型上的均匀概率与期望（事件取 Finset，语句里不出现可判定性）
-- unifProb_mono/compl/exists_of_unifProb_pos：单调、互补（=1）、正概率 ⟹ 事件非空
-- markov：f ≥ 0、a > 0 ⟹ P[a ≤ f] ≤ E[f]/a
-- unifExpect_two_pow_lost_le：论文的 E[2^{X_H}] ≤ (1+2/t)^m（由 weighted_sum_le 除以 (t²)^m）
-- lost_tail_prob：Lemma 3.11 的尾概率形式 P[X_H ≥ s] ≤ e^{2m/t}/2^s
-- sample_budget_exp：N²(1−1/t)^{2t(⌈log N⌉+1)} ≤ e^{−2}
-- bad_prob_le：Claim 3.12 的并集界 P[Bad] ≤ |A|²(1−1/t)^k
-- claim312_success_prob：论文的 k 之下好样本概率 ≥ 1 − e^{−2}
-- claim312_exists_via_prob：由正概率重新得到分离样本的存在性
#print axioms DLMST.unifProb
#print axioms DLMST.unifExpect
#print axioms DLMST.unifProb_nonneg
#print axioms DLMST.unifProb_mono
#print axioms DLMST.unifProb_compl
#print axioms DLMST.exists_of_unifProb_pos
#print axioms DLMST.markov
#print axioms DLMST.History.unifExpect_two_pow_lost_le
#print axioms DLMST.History.lost_tail_prob
#print axioms DLMST.sample_budget_exp
#print axioms DLMST.bad_prob_le
#print axioms DLMST.claim312_success_prob
#print axioms DLMST.claim312_exists_via_prob

/-! ## 第一百零九批：B4 矩母函数族与 Chernoff 尾界 -/

-- unifExpect_mono：逐点 f ≤ g ⟹ E[f] ≤ E[g]
-- genEdge_le_real：每个弧度 lam ≥ 1 的生成函数 Σ_r lam^{[r 对 e 坏]} ≤ t² + 2t(lam−1)
-- weighted_sum_le_real：Σ_ρ lam^{X_H(ρ)} = ∏_e Σ_r lam^{[r 对 e 坏]} ≤ (t² + 2t(lam−1))^m
-- unifExpect_mgf_le：除以 (t²)^m ⟹ E[lam^{X_H}] ≤ (1 + 2(lam−1)/t)^m
-- chernoff_tail：Markov ⟹ P[X_H ≥ s] ≤ (1 + 2(lam−1)/t)^m / lam^s
-- unifExpect_lost_le：X ≤ 2^X ⟹ E[X_H] ≤ (1 + 2/t)^m
-- half_schedules_good：至少一半的调度满足 X_H < 2(1+2/t)^m
-- lost_tail_prob_paper：P[X_H ≥ ⌈(log|Hs| + 2m/t)/log 2⌉] ≤ 1/|Hs|
#print axioms DLMST.unifExpect_mono
#print axioms DLMST.History.genEdge_le_real
#print axioms DLMST.History.weighted_sum_le_real
#print axioms DLMST.History.unifExpect_mgf_le
#print axioms DLMST.History.chernoff_tail
#print axioms DLMST.History.unifExpect_lost_le
#print axioms DLMST.History.half_schedules_good
#print axioms DLMST.History.lost_tail_prob_paper

/-! ## 第一百一十批：B4 并集界、Bonferroni、独立性 -/

-- unifProb_union_le / unifProb_biUnion_le：并集界（两个 / 有限族）
-- unifProb_all_good_ge：Bonferroni，P[所有坏事件都不发生] ≥ 1 − Σδᵢ
-- unifProb_indep：乘积空间的概率相乘（独立性的精确形式）
-- unifProb_prod_two_good：两个独立的好事件同时成立的概率 ≥ 1 − (δ+ε)
-- claim312_four_fifths：1 − e^{−2} ≥ 4/5
#print axioms DLMST.unifProb_union_le
#print axioms DLMST.unifProb_biUnion_le
#print axioms DLMST.unifProb_all_good_ge
#print axioms DLMST.unifProb_indep
#print axioms DLMST.unifProb_prod_two_good
#print axioms DLMST.claim312_four_fifths

/-! ## 第一百一十一批：Claim 3.12 经独立性与并集界（概率版） -/

-- unifProb_agreeTuples：P[k 元组在每个坐标上都一致] = (单坐标一致率)^k
-- unifProb_agreeTuples_le：相差超过 q = M/t 个坐标的一对，一致率 ≤ (1 − 1/t)^k
-- bad_prob_le_via_union：坏元组事件 ⊆ 各坏对一致事件之并，用并集界
-- bad_prob_le_union：P[Bad] ≤ |A|²(1 − 1/t)^k（与 Sampling.bad_prob_le 的计数版互为印证）
#print axioms DLMST.unifProb_agreeTuples
#print axioms DLMST.unifProb_agreeTuples_le
#print axioms DLMST.bad_prob_le_via_union
#print axioms DLMST.bad_prob_le_union


/-! ## 第一百一十二批：§4 在自选停止深度（有界激活、停止条件由测度推出） -/

-- four_pow_mul_lvlVerts_le_of_lt：4^d·|verts| ≤ |P| 对 d ≤ D，激活只在 D 以下消费
-- lvlVerts_card_le_one_of_le_pow：|P| ≤ 4^D 强制 |verts at D| ≤ 1（mst_main_stop 的 hstop 不再是假设）
-- mst_stop_depth / _three_fourths：D = log₄|P|+1 处的答案是最小生成森林，|F| ≤ |P|−1，3|F| ≤ 4|P|
-- mst_stop_depth_weight：同一深度的层森林权重望远镜
-- mst_stop_depth_package：正确的 MSF + 边数界 + 4/3 界 + 测度 + 望远镜，一个陈述
#print axioms DLMST.four_pow_mul_lvlVerts_le_of_lt
#print axioms DLMST.lvlVerts_card_le_one_of_le_pow
#print axioms DLMST.mst_stop_depth
#print axioms DLMST.mst_stop_depth_three_fourths
#print axioms DLMST.mst_stop_depth_weight
#print axioms DLMST.mst_stop_depth_package

/-! ## 第一百一十三批：§4 塔无条件正确（无激活假设，停止深度由连通性推出） -/

-- contract_step_sound_nohact：phaseChain_safe + isMSFOf_union_cGraph_child，拼接不需要激活
-- tower_sound_nohact：逐层拼接给出根实例的 MSF（除 hPE 外无假设）
-- tower_msf_at_stop_nohact / _card：|verts D| ≤ 1 处底部调用可省，答案是最小生成森林且 |F| ≤ |P|−1
-- lvlVerts_step_le：层顶点集逐层不增
-- lvlVerts_succ_lt：层顶点数 ≥ 2 时严格减少（第一阶段激活由连通性 + 计数推出）
-- lvlVerts_le_one_or_card_add_le：|V_d| ≤ 1 或 |V_d| + d ≤ |P|（停止二分）
-- lvlVerts_card_le_one_at_card / exists_lvlVerts_card_le_one：深度 |P| 必停
-- mst_main_connected / _three_fourths / _weight / _package：连通实例上 §4 无条件正确，
--   |F| ≤ |P|−1，3|F| ≤ 4|P|，权重望远镜
-- activated_iff_two_le_compCountOn：激活 ⇔ 未塌缩（解释 tower_sound 的双阶段接口为何只在层边界可满足）
#print axioms DLMST.contract_step_sound_nohact
#print axioms DLMST.tower_sound_nohact
#print axioms DLMST.tower_msf_at_stop_nohact
#print axioms DLMST.tower_msf_at_stop_nohact_card
#print axioms DLMST.lvlVerts_step_le
#print axioms DLMST.lvlVerts_succ_lt
#print axioms DLMST.lvlVerts_le_one_or_card_add_le
#print axioms DLMST.lvlVerts_card_le_one_at_card
#print axioms DLMST.exists_lvlVerts_card_le_one
#print axioms DLMST.mst_main_connected
#print axioms DLMST.mst_main_connected_three_fourths
#print axioms DLMST.mst_main_connected_weight
#print axioms DLMST.mst_main_connected_package
#print axioms DLMST.activated_iff_two_le_compCountOn

/-! ## 第一百一十四批：逐调用数值界 hU / hrnd 从驱动数据推出（非假设） -/

-- KidBoundCall：p.24 输入数据（roundIn/blkIn 的归派与大小）
-- KidBoundCall.ofForests：用「旧森林 + 新森林」「旧森林 + 门边」推出两个大小（card_roundIn_le/card_blkIn_le）
-- KidBoundCall.hrnd：Σ|kidE| ≤ |U| + 2t²(n−1) + t(n−1+r²n)，r = 8t³
-- hrnd_cast + hrnd_level：实数形与层形 t = γ(d+1)³（逐调用，非空真）
-- level_t_of_nat：γ = 16 时层 t 可取自然数，层形前提可满足
-- EvidenceOn.herrU / herrU_level：§3.5 界 |U| ≤ 10t²√(mn)+4m/t 的逐调用/层形
-- sum_kidE_driverStrategy / U_driverStrategy：合成策略经 Fin(t²) 重标号的搬运
-- hrnd_strategy / herrU_strategy：合成策略在自身 t 上的两个界
-- herrU_chain / hrnd_chain：沿水平链、按 t_d 盖章（前提是逐调用识别 htd）
-- display_of_driver_derived / work_linear_of_driver_derived / driver_display_and_work_derived：
--   §3.6 的显示界与线性工作量，两个逐调用数值不再作为前提
#print axioms DLMST.DriverCall.KidBoundCall.hrnd
#print axioms DLMST.DriverCall.KidBoundCall.ofForests
#print axioms DLMST.DriverCall.KidBoundCall.hrnd_cast
#print axioms DLMST.DriverCall.KidBoundCall.hrnd_level
#print axioms DLMST.DriverCall.level_t_of_nat
#print axioms DLMST.DriverCall.EvidenceOn.herrU
#print axioms DLMST.DriverCall.EvidenceOn.herrU_level
#print axioms DLMST.DriverCall.sum_kidE_driverStrategy
#print axioms DLMST.DriverCall.U_driverStrategy
#print axioms DLMST.DriverCall.hrnd_strategy
#print axioms DLMST.DriverCall.hrnd_strategy_cast
#print axioms DLMST.DriverCall.herrU_strategy
#print axioms DLMST.DriverCall.herrU_chain
#print axioms DLMST.DriverCall.hrnd_chain
#print axioms DLMST.DriverCall.display_of_driver_derived
#print axioms DLMST.DriverCall.work_linear_of_driver_derived
#print axioms DLMST.DriverCall.driver_display_and_work_derived

/-! ## 第一百一十五批：实例局部的 Lemma 3.10/3.11 与真值证据（`InstanceHistory` / `DriverEvidence`） -/

#print axioms DLMST.sum_degOn_le
#print axioms DLMST.sum_log_degOn_le
#print axioms DLMST.card_spokeOKOn_le
#print axioms DLMST.card_spokeSeqsOn_le
#print axioms DLMST.card_subsetsOn_le_choose
#print axioms DLMST.card_forestSeqsOn_le
#print axioms DLMST.card_historiesOn_le
#print axioms DLMST.log_card_historiesOn_le
#print axioms DLMST.exists_schedule_lostOn_paper
#print axioms DLMST.legalOn_canonical
#print axioms DLMST.exists_good_scheduleOn
#print axioms DLMST.DriverCall.history_legalOn
#print axioms DLMST.DriverCall.evidenceOn_of_good_schedule
#print axioms DLMST.DriverCall.agree_truthOn
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_truth
#print axioms DLMST.DriverCall.exists_good_schedule

/-! ## 第一百一十六批：`DriverCall` 的非空性见证（`DriverWitness`） -/

#print axioms DLMST.DriverWitness.incident_all
#print axioms DLMST.DriverWitness.preF_par_card_le
#print axioms DLMST.DriverWitness.callPar
#print axioms DLMST.DriverWitness.callPar_nonempty
#print axioms DLMST.DriverWitness.callPar_legalOn

/-! ## 第一百一十七批：停机接口的 `4/3`（`StopFourThirds`） -/

#print axioms DLMST.answer_three_fourths
#print axioms DLMST.mst_main_stop_three_fourths
#print axioms DLMST.stop_witness_three_fourths

/-! ## 第一百一十八批：小实例上「好调度」前提自动成立（`SmallInstance`） -/

#print axioms DLMST.History.lostOn_le_card
#print axioms DLMST.lostOn_log_le_of_bound
#print axioms DLMST.DriverWitness.preF_par_card_le_t
#print axioms DLMST.DriverWitness.callPar2
#print axioms DLMST.DriverWitness.callPar2_hbig
#print axioms DLMST.DriverWitness.callPar2_good
#print axioms DLMST.DriverWitness.callPar2_evidence
#print axioms DLMST.DriverWitness.callPar2_card_U

/-! ## 第一百一十九批：Lemma 3.7 的 `bad` 形式（`Lemma37Bad`） -/

#print axioms DLMST.DriverCall.errOf_truth_iff
#print axioms DLMST.DriverCall.evidenceOn_of_good_schedule_badFor
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_badFor

/-! ## 第一百二十批：平行边见证的每条边都被支持（`WitnessSupported`） -/

#print axioms DLMST.DriverWitness.scan_zero_eq
#print axioms DLMST.DriverWitness.sort_univ_ne_nil
#print axioms DLMST.DriverWitness.weight_le_of_fin_le
#print axioms DLMST.DriverWitness.eq_of_conn_empty
#print axioms DLMST.DriverWitness.head_kept
#print axioms DLMST.DriverWitness.all_supported
#print axioms DLMST.DriverWitness.badFor_vacuous
#print axioms DLMST.DriverWitness.callPar2_unsupp_empty
#print axioms DLMST.DriverWitness.callPar2_U_eq_empty
#print axioms DLMST.DriverWitness.callPar2_card_U_uncond

/-! ## 第一百二十一批：`badFor` 过程侧的 t=1 自证与层级链合成（`ProcDriver`） -/

#print axioms DLMST.History.badFor_one
#print axioms DLMST.DriverCall.badFor_of_unsupp_one
#print axioms DLMST.DriverCall.evidenceOn_of_good_schedule_one
#print axioms DLMST.DriverCall.history_spoke_incident
#print axioms DLMST.DriverCall.badFor_of_procChains
#print axioms DLMST.DriverCall.evidenceOn_of_procChains
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_procChains
#print axioms DLMST.DriverWitness.callPar_one_hbig
#print axioms DLMST.DriverWitness.callPar_one_good
#print axioms DLMST.DriverWitness.callPar_evidence_uncond

/-! ## 第一百二十二批：链接口收紧（实例边上的链 + 驱动侧派生字段，`ChainDriver`） -/

#print axioms DLMST.ProcChain.unSupp_errOf_on
#print axioms DLMST.DriverCall.history_spoke_frozen
#print axioms DLMST.DriverCall.badFor_of_procChainsOn
#print axioms DLMST.ProcChain.ofDriver
#print axioms DLMST.DriverCall.badFor_of_driverChains

/-! ## 第一百二十三批：链接口形状（无穷链、不会终止；驱动形态接 §3.5，`ChainShape`） -/

#print axioms DLMST.ProcChain.childF_nonempty
#print axioms DLMST.ProcChain.not_chain_of_empty_child
#print axioms DLMST.ProcChain.not_chain_of_eventually_empty
#print axioms DLMST.DriverCall.evidenceOn_of_driverChains
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_driverChains

/-! ## 第一百二十四批：单层步骤接口（去掉无穷链与多余的 `hchild`，`OneStep`） -/

#print axioms DLMST.StepData.step_error
#print axioms DLMST.StepData.badFor
#print axioms DLMST.ProcChain.stepData
#print axioms DLMST.DriverCall.badFor_of_stepsOn
#print axioms DLMST.DriverCall.badFor_of_procChains_noChild
#print axioms DLMST.DriverCall.evidenceOn_of_steps
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_steps

/-! ## 第一百二十五批：投影判据（不支持 + 轻辐条 + 门户相异 ⟹ project，`ProjectRule`） -/

#print axioms DLMST.supported_mono
#print axioms DLMST.not_prefFind_of_unsupp
#print axioms DLMST.DriverCall.pref_project_of_unsupp
#print axioms DLMST.DriverCall.StepData.ofDriver
#print axioms DLMST.DriverCall.badFor_of_stepObligations
#print axioms DLMST.DriverCall.evidenceOn_of_stepObligations
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_stepObligations

/-! ## 第一百二十六批：辐条属于本轮批次（`hσS` 推导）与几何化每边义务（`SpokeInst`） -/

#print axioms DLMST.DriverCall.history_spoke_mem_B
#print axioms DLMST.DriverCall.history_spoke_mem_of_batch
#print axioms DLMST.DriverCall.badFor_of_geomObligations
#print axioms DLMST.DriverCall.evidenceOn_of_geomObligations
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_geomObligations

/-! ## 第一百二十七批：森林随轮次单调，`hret`／`hsub` 消去（`ForestMono`） -/

#print axioms DLMST.CallOut.forestUpTo_mono
#print axioms DLMST.DriverCall.history_forest_mono
#print axioms DLMST.DriverCall.history_forest_sub_F
#print axioms DLMST.DriverCall.nextForest_sub
#print axioms DLMST.DriverCall.hret_nextForest
#print axioms DLMST.DriverCall.badFor_of_geomObligations_next
#print axioms DLMST.DriverCall.evidenceOn_of_geomObligations_next
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_geomObligations_next

/-! ## 第一百二十八批：辐条不重于边（选择集成员，`SpokeLe`） -/

#print axioms DLMST.DriverCall.history_spoke_weight_le_of_mem
#print axioms DLMST.DriverCall.badFor_of_selObligations
#print axioms DLMST.DriverCall.evidenceOn_of_selObligations
#print axioms DLMST.DriverCall.card_U_le_number_bound_of_selObligations

/-! ## 第一百二十九批：轻辐条与子实例支持互斥，更正第 126／128 批的空真封装（`LightVacuous`） -/

#print axioms DLMST.DriverCall.supported_of_light_and_child
#print axioms DLMST.DriverCall.unsupp_false_of_light_and_child
#print axioms DLMST.DriverCall.pE_gt_of_unsupp

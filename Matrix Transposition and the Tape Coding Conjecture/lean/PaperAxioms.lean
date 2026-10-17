import Transpose.Basic
import Transpose.Eventually
import Transpose.Frames.Gadget
import Transpose.Frames.GadgetCargo
import Transpose.Frames.GadgetCoarse
import Transpose.Frames.GadgetItinerary
import Transpose.Frames.GadgetItineraryC
import Transpose.Frames.GadgetMixing
import Transpose.Frames.GadgetMod2
import Transpose.Frames.GadgetOneSided
import Transpose.Frames.GadgetProjection
import Transpose.Frames.GadgetRuns
import Transpose.Frames.GadgetTwoSided
import Transpose.Frames.GroupAlgebraRuns
import Transpose.Frames.RankMod
import Transpose.Sanity
import Transpose.Statement
import Transpose.Tape.Blocks
import Transpose.Tape.BufTM
import Transpose.Tape.CECode
import Transpose.Tape.CECount
import Transpose.Tape.CECut
import Transpose.Tape.CEEquiv
import Transpose.Tape.CEForms
import Transpose.Tape.CEHint
import Transpose.Tape.CEMain
import Transpose.Tape.CENet
import Transpose.Tape.CEProfile
import Transpose.Tape.CERungs
import Transpose.Tape.CESweep
import Transpose.Tape.CoarseTrace
import Transpose.Tape.Corollaries
import Transpose.Tape.Counting
import Transpose.Tape.Coverage
import Transpose.Tape.CutTrace
import Transpose.Tape.Defs
import Transpose.Tape.DefsCE
import Transpose.Tape.DefsM
import Transpose.Tape.DefsP
import Transpose.Tape.DefsPP
import Transpose.Tape.DefsTrace
import Transpose.Tape.Encode
import Transpose.Tape.Forest
import Transpose.Tape.Lemma3
import Transpose.Tape.LemmaOnePrime
import Transpose.Tape.Locality
import Transpose.Tape.MStar
import Transpose.Tape.MStarAdaptive
import Transpose.Tape.MStarAnalysis
import Transpose.Tape.MStarClass
import Transpose.Tape.MStarCoding
import Transpose.Tape.MStarDiagram
import Transpose.Tape.MStarDiscrete
import Transpose.Tape.MStarExcess
import Transpose.Tape.MStarLevel
import Transpose.Tape.MStarRobust
import Transpose.Tape.MStarTM
import Transpose.Tape.MStarWalk
import Transpose.Tape.OffsetsCounterexample
import Transpose.Tape.PPrime
import Transpose.Tape.PPrimeExamples
import Transpose.Tape.PPrimeLocal
import Transpose.Tape.Passes
import Transpose.Tape.PlainRobust.CEColCover
import Transpose.Tape.PlainRobust.CEConcat
import Transpose.Tape.PlainRobust.CEConcatNet
import Transpose.Tape.PlainRobust.CEDecomp
import Transpose.Tape.PlainRobust.CEDegree
import Transpose.Tape.PlainRobust.CELinear
import Transpose.Tape.PlainRobust.CENonlin
import Transpose.Tape.PlainRobust.CEPrefix
import Transpose.Tape.PlainRobust.CESelect
import Transpose.Tape.PlainRobust.CESelectNet
import Transpose.Tape.PlainRobust.CESyndrome
import Transpose.Tape.PlainRobust.CEVote
import Transpose.Tape.PopularTrace
import Transpose.Tape.Run
import Transpose.Tape.Statements.Adaptive
import Transpose.Tape.Statements.Coding
import Transpose.Tape.Statements.Core
import Transpose.Tape.Statements.PlainRobust
import Transpose.Tape.TheoremP
import Transpose.Tape.Witness
import Transpose.Tape.WitnessDD
import Transpose.Tape.WitnessGap
import Transpose.Tape.Witnesses

/-!
# Axioms of the declarations cited in the paper

Generated from the LaTeX sources of the paper (`\lean` and `\formal` macros). Run from the `lean/`
directory, after `lake build`:

    lake env lean PaperAxioms.lean

Every declaration should depend on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms Transpose.ComputesWithin
#print axioms Transpose.LinearTimeTransposable
#print axioms Transpose.ShearFrame.Cfg
#print axioms Transpose.ShearFrame.Event
#print axioms Transpose.ShearFrame.Gadget
#print axioms Transpose.ShearFrame.Gadget.cost
#print axioms Transpose.ShearFrame.Gadget.cost_ge_m
#print axioms Transpose.ShearFrame.Gadget.cost_ge_of_invariant_family
#print axioms Transpose.ShearFrame.Gadget.invariant_cost_ge
#print axioms Transpose.ShearFrame.GroupAlgebra.changes_ge_W
#print axioms Transpose.ShearFrame.GroupAlgebra.cost_ge_W
#print axioms Transpose.ShearFrame.PGadget.two_mul_cost_ge
#print axioms Transpose.ShearFrame.cargo_rule
#print axioms Transpose.ShearFrame.cargo_rule_bool
#print axioms Transpose.ShearFrame.carrying_move_on_admissible_chain
#print axioms Transpose.ShearFrame.carrying_move_on_chain
#print axioms Transpose.ShearFrame.chain_itinerary
#print axioms Transpose.ShearFrame.chain_itinerary_matrix
#print axioms Transpose.ShearFrame.cost_ge_W
#print axioms Transpose.ShearFrame.det_ne_zero_of_moves_le
#print axioms Transpose.ShearFrame.itinerary_condition
#print axioms Transpose.ShearFrame.itinerary_condition_matrix
#print axioms Transpose.ShearFrame.mixed_move_forces_extra_hop
#print axioms Transpose.ShearFrame.mixing_lemma
#print axioms Transpose.ShearFrame.mixing_lemma_matrix
#print axioms Transpose.ShearFrame.moves
#print axioms Transpose.ShearFrame.moves_ge_W
#print axioms Transpose.ShearFrame.moves_ge_W_matrix
#print axioms Transpose.ShearFrame.one_sided_bound
#print axioms Transpose.ShearFrame.rank_sum_of_moves_le
#print axioms Transpose.ShearFrame.tight_potentials
#print axioms Transpose.ShearFrame.tight_sigma_split
#print axioms Transpose.ShearFrame.two_mul_le_rank_sum
#print axioms Transpose.ShearFrame.two_sided_bound
#print axioms Transpose.ShearFrame.visible_ge_W_of_coarse
#print axioms Transpose.ShearFrame.visible_move_on_admissible_chain
#print axioms Transpose.ShearFrame.vmoves_ge_W
#print axioms Transpose.Tape.AdmissibleRes
#print axioms Transpose.Tape.AllMono
#print axioms Transpose.Tape.ConsecIn
#print axioms Transpose.Tape.CutIneq
#print axioms Transpose.Tape.FinUnionIcc
#print axioms Transpose.Tape.HaltsAt
#print axioms Transpose.Tape.Impl.bufTM
#print axioms Transpose.Tape.IsChord
#print axioms Transpose.Tape.IsLastVisit
#print axioms Transpose.Tape.IsWalk
#print axioms Transpose.Tape.MonoOn
#print axioms Transpose.Tape.NetCode
#print axioms Transpose.Tape.NetCode.edgeVal
#print axioms Transpose.Tape.NetCode.inVals
#print axioms Transpose.Tape.NetCode.outVal
#print axioms Transpose.Tape.NoCode_TM
#print axioms Transpose.Tape.NoCode_TM_coent
#print axioms Transpose.Tape.NoCode_TM_hintBits
#print axioms Transpose.Tape.ObliviousLinearTimeTransposable
#print axioms Transpose.Tape.ObliviousOn
#print axioms Transpose.Tape.PassPartition
#print axioms Transpose.Tape.PiecewiseConstOn
#print axioms Transpose.Tape.PlainRobust.noCode_additiveCover_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_additive_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_affine_exc_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_affine_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_colAggregate_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_colCover_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_cosmall_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_crossQuad_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_decomp_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_fewErrorsCover_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_fewErrors_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_hintConst_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_iff_hintConst
#print axioms Transpose.Tape.PlainRobust.noCode_linearExcept_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_linearPlusImage_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_linearPlus_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_linear_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_lowDegree_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_netCover_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_netHint_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_of_affine_subset
#print axioms Transpose.Tape.PlainRobust.noCode_quadForm_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_rowMapCover_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_sparseEntryErrors_of_noCode
#print axioms Transpose.Tape.PlainRobust.noCode_sparseErrors_of_noCode
#print axioms Transpose.Tape.RobustCE_TM
#print axioms Transpose.Tape.RobustCE_TM_dist
#print axioms Transpose.Tape.RobustNoCode_TM
#print axioms Transpose.Tape.Routing
#print axioms Transpose.Tape.SameTrace
#print axioms Transpose.Tape.TSDiagram
#print axioms Transpose.Tape.TSDiagram.CapProfile
#print axioms Transpose.Tape.TSDiagram.RoutesAt
#print axioms Transpose.Tape.TSDiagram.Solves
#print axioms Transpose.Tape.TSDiagram.Valid
#print axioms Transpose.Tape.TSDiagram.blockCap
#print axioms Transpose.Tape.TSDiagram.blockSize
#print axioms Transpose.Tape.TSDiagram.chordEdges
#print axioms Transpose.Tape.TSDiagram.edges
#print axioms Transpose.Tape.TSDiagram.memEdges
#print axioms Transpose.Tape.TSDiagram.nodes
#print axioms Transpose.Tape.TSDiagram.outNode
#print axioms Transpose.Tape.TSDiagram.profileCap
#print axioms Transpose.Tape.TSDiagram.rowDist
#print axioms Transpose.Tape.TSDiagram.rowsAt
#print axioms Transpose.Tape.TSDiagram.visible
#print axioms Transpose.Tape.TraceClass
#print axioms Transpose.Tape.Transposes
#print axioms Transpose.Tape.Witness.tr2
#print axioms Transpose.Tape.Witness.tr2dd
#print axioms Transpose.Tape.Witness.tr2k
#print axioms Transpose.Tape.adaptive_hyps_of_linearTime
#print axioms Transpose.Tape.addrCount
#print axioms Transpose.Tape.addrCount_mul
#print axioms Transpose.Tape.addresses
#print axioms Transpose.Tape.addrsBelow
#print axioms Transpose.Tape.ae_finite_levelSet
#print axioms Transpose.Tape.ball
#print axioms Transpose.Tape.blockOf
#print axioms Transpose.Tape.blockTrace
#print axioms Transpose.Tape.blockTraj
#print axioms Transpose.Tape.blockTraj_limit_lipschitz
#print axioms Transpose.Tape.block_locality
#print axioms Transpose.Tape.block_locality_offsets_counterexample
#print axioms Transpose.Tape.bufTM_run
#print axioms Transpose.Tape.card_addresses_le
#print axioms Transpose.Tape.card_chordEdges_le
#print axioms Transpose.Tape.card_le_entryData
#print axioms Transpose.Tape.card_le_of_solves
#print axioms Transpose.Tape.ce_TM_dist_iff_noCode
#print axioms Transpose.Tape.ce_TM_dist_of_robustCE_TM_dist
#print axioms Transpose.Tape.ce_TM_iff_noCode
#print axioms Transpose.Tape.ce_TM_of_robustCE_TM
#print axioms Transpose.Tape.cellBits
#print axioms Transpose.Tape.charging_bound
#print axioms Transpose.Tape.childNode
#print axioms Transpose.Tape.chordsInto
#print axioms Transpose.Tape.code_gap
#print axioms Transpose.Tape.code_of_hint
#print axioms Transpose.Tape.codes_coentLinear_of_linearTimeTransposable
#print axioms Transpose.Tape.codes_of_fastOn
#print axioms Transpose.Tape.codes_of_fastOn_bits
#print axioms Transpose.Tape.codes_of_linearTimeTransposable
#print axioms Transpose.Tape.codes_of_obliviousLinearTimeTransposable
#print axioms Transpose.Tape.coentLinear_io_iff_exists_coent_io
#print axioms Transpose.Tape.coentLinear_io_of_robustNoCode_io
#print axioms Transpose.Tape.coentLinear_of_robustCE_TM_lin
#print axioms Transpose.Tape.coentLinear_of_robustNoCode
#print axioms Transpose.Tape.coent_io_nw_of_robustNoCode_io
#print axioms Transpose.Tape.coent_io_of_coent
#print axioms Transpose.Tape.coent_mono
#print axioms Transpose.Tape.coent_of_hintBits
#print axioms Transpose.Tape.combSet
#print axioms Transpose.Tape.computesWithin_iff
#print axioms Transpose.Tape.copyTM_obliviousOn
#print axioms Transpose.Tape.copyTM_transposes
#print axioms Transpose.Tape.countable_localExtr_values
#print axioms Transpose.Tape.coverage_grouped
#print axioms Transpose.Tape.coverage_per_address
#print axioms Transpose.Tape.crossChords_split
#print axioms Transpose.Tape.crossPairs
#print axioms Transpose.Tape.curBlock
#print axioms Transpose.Tape.cutIneq_of_solves
#print axioms Transpose.Tape.cutPairs
#print axioms Transpose.Tape.cutPairs_card_mul_le
#print axioms Transpose.Tape.cutSet
#print axioms Transpose.Tape.cut_bound
#print axioms Transpose.Tape.cut_bound_bits
#print axioms Transpose.Tape.cut_bound_on
#print axioms Transpose.Tape.cut_bound_on_coentropy
#print axioms Transpose.Tape.cut_bound_pairs
#print axioms Transpose.Tape.cut_bound_sum
#print axioms Transpose.Tape.cut_bound_sum_bits
#print axioms Transpose.Tape.cut_bound_sum_on
#print axioms Transpose.Tape.cut_bound_trace
#print axioms Transpose.Tape.cut_bound_trace_bits
#print axioms Transpose.Tape.cut_bound_trace_bits_on
#print axioms Transpose.Tape.cut_bound_trace_on
#print axioms Transpose.Tape.cutset_bits_bitwise
#print axioms Transpose.Tape.cutset_bound
#print axioms Transpose.Tape.cutset_bound_bitwise
#print axioms Transpose.Tape.entryCells
#print axioms Transpose.Tape.entryCells_slotSteps_card
#print axioms Transpose.Tape.entryPoints
#print axioms Transpose.Tape.entryPoints_slotSteps_card
#print axioms Transpose.Tape.entryTimes_card_le
#print axioms Transpose.Tape.entryTimes_charged
#print axioms Transpose.Tape.excess_add_range_le
#print axioms Transpose.Tape.exists_popular_traceClass
#print axioms Transpose.Tape.exists_popular_traceClass_on
#print axioms Transpose.Tape.exists_shift_cover
#print axioms Transpose.Tape.exists_shift_iff_unbounded
#print axioms Transpose.Tape.exists_slot_block_eq
#print axioms Transpose.Tape.exists_subseq_blockTraj
#print axioms Transpose.Tape.exists_subseq_tendstoUniformlyOn
#print axioms Transpose.Tape.flow_rate_lt
#print axioms Transpose.Tape.forest
#print axioms Transpose.Tape.forestNode
#print axioms Transpose.Tape.forestNode_disjoint
#print axioms Transpose.Tape.forest_agree
#print axioms Transpose.Tape.forest_comb_agree
#print axioms Transpose.Tape.forest_comb_agree_on
#print axioms Transpose.Tape.forest_entryCells_card_le
#print axioms Transpose.Tape.forest_entryCells_subset
#print axioms Transpose.Tape.forest_entryPoints_card_le
#print axioms Transpose.Tape.forest_entryPoints_subset
#print axioms Transpose.Tape.forest_info
#print axioms Transpose.Tape.forest_subset
#print axioms Transpose.Tape.frozen_V2
#print axioms Transpose.Tape.greedyBound
#print axioms Transpose.Tape.greedyPasses
#print axioms Transpose.Tape.greedyPasses_indep
#print axioms Transpose.Tape.greedyPasses_le
#print axioms Transpose.Tape.greedy_passPartition
#print axioms Transpose.Tape.haltsAt_unique
#print axioms Transpose.Tape.hintBits_of_coent
#print axioms Transpose.Tape.hintCodes_linear_of_linearTimeTransposable
#print axioms Transpose.Tape.hintCodes_of_linearTimeTransposable
#print axioms Transpose.Tape.hintLinear_iff_coentLinear
#print axioms Transpose.Tape.hint_of_code
#print axioms Transpose.Tape.horizon
#print axioms Transpose.Tape.isoperimetry
#print axioms Transpose.Tape.isoperimetry_code
#print axioms Transpose.Tape.isoperimetry_res
#print axioms Transpose.Tape.isoperimetry_res_on
#print axioms Transpose.Tape.isoperimetry_touch
#print axioms Transpose.Tape.isoperimetry_trace
#print axioms Transpose.Tape.isoperimetry_trace_on
#print axioms Transpose.Tape.kraft_group
#print axioms Transpose.Tape.kraft_group_on
#print axioms Transpose.Tape.levelChords_limsup_le
#print axioms Transpose.Tape.levelCross
#print axioms Transpose.Tape.levelCross_le_levelExcess
#print axioms Transpose.Tape.levelExcess
#print axioms Transpose.Tape.levelSet
#print axioms Transpose.Tape.levelSet_encard_majorant
#print axioms Transpose.Tape.linearTimeTransposable_popular_limits
#print axioms Transpose.Tape.linearTime_fails_of_coentLinear
#print axioms Transpose.Tape.linearTime_fails_of_robustNoCode
#print axioms Transpose.Tape.linearTime_fails_of_robustNoCode_logBits
#print axioms Transpose.Tape.lintegral_encard_levelSet_le
#print axioms Transpose.Tape.lintegral_levelExcess_eq_zero_of_monotone
#print axioms Transpose.Tape.locality
#print axioms Transpose.Tape.locality_anchored
#print axioms Transpose.Tape.locality_core
#print axioms Transpose.Tape.locality_entry
#print axioms Transpose.Tape.locality_function
#print axioms Transpose.Tape.locality_interval
#print axioms Transpose.Tape.locality_oblivious
#print axioms Transpose.Tape.matrixInputs
#print axioms Transpose.Tape.matrixInputs_eq
#print axioms Transpose.Tape.mstar_discrete_class_on
#print axioms Transpose.Tape.mstar_of_not_robustNoCode
#print axioms Transpose.Tape.mstar_of_robustNoCode_counterexamples
#print axioms Transpose.Tape.netDist
#print axioms Transpose.Tape.noCode_bits_iff
#print axioms Transpose.Tape.noCode_iff_coent_zero
#print axioms Transpose.Tape.noCode_iff_forall_cap
#print axioms Transpose.Tape.noCode_io_of_robustNoCode_io
#print axioms Transpose.Tape.noCode_of_coentLinear
#print axioms Transpose.Tape.noCode_of_noCode_hint
#print axioms Transpose.Tape.noCode_of_robustNoCode
#print axioms Transpose.Tape.no_fast_transposer_of_coent
#print axioms Transpose.Tape.no_fast_transposer_of_coentLinear
#print axioms Transpose.Tape.no_fast_transposer_of_robustNoCode
#print axioms Transpose.Tape.no_fast_transposer_of_robustNoCode_bits
#print axioms Transpose.Tape.no_stationary_limits
#print axioms Transpose.Tape.no_stationary_limits_class_on
#print axioms Transpose.Tape.nodeCode
#print axioms Transpose.Tape.not_all_monotone_of_star
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coent
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coentLinear
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coentLinear_end
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coentLinear_end_io
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coentLinear_io
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coent_io
#print axioms Transpose.Tape.not_linearTimeTransposable_of_coent_nw
#print axioms Transpose.Tape.not_linearTimeTransposable_of_noCode_hint
#print axioms Transpose.Tape.not_linearTimeTransposable_of_noCode_hintLinear
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustCE_TM
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustCE_TM_dist
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustCE_TM_io
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustCE_TM_lin
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustNoCode
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustNoCode_io
#print axioms Transpose.Tape.not_linearTimeTransposable_of_robustNoCode_logBits
#print axioms Transpose.Tape.not_obliviousLinearTimeTransposable_of_ce_TM
#print axioms Transpose.Tape.not_obliviousLinearTimeTransposable_of_ce_TM_dist
#print axioms Transpose.Tape.not_obliviousLinearTimeTransposable_of_noCode
#print axioms Transpose.Tape.not_obliviousLinearTimeTransposable_of_noCode_io
#print axioms Transpose.Tape.not_robustCE_TM_of_linearTimeTransposable
#print axioms Transpose.Tape.numSlots
#print axioms Transpose.Tape.numSlots_le_horizon
#print axioms Transpose.Tape.numSlots_le_of
#print axioms Transpose.Tape.one_le_excess_of_star
#print axioms Transpose.Tape.outRev_reverse_eq
#print axioms Transpose.Tape.pairChange_spacing
#print axioms Transpose.Tape.pairRes
#print axioms Transpose.Tape.pairRes_V2
#print axioms Transpose.Tape.pairRes_admissible
#print axioms Transpose.Tape.pairRes_begin_unique
#print axioms Transpose.Tape.pairRes_chord_source_unique
#print axioms Transpose.Tape.pairRes_chord_target_unique
#print axioms Transpose.Tape.pairRes_congr
#print axioms Transpose.Tape.pairRes_end_unique
#print axioms Transpose.Tape.pairRes_subset
#print axioms Transpose.Tape.passPartition_iff
#print axioms Transpose.Tape.passPartition_indep
#print axioms Transpose.Tape.pass_fresh
#print axioms Transpose.Tape.plain_tfae
#print axioms Transpose.Tape.range_add_one_le_of_star
#print axioms Transpose.Tape.readSet
#print axioms Transpose.Tape.read_chain
#print axioms Transpose.Tape.rescaledTraj
#print axioms Transpose.Tape.rescaledTrajOf
#print axioms Transpose.Tape.rescaledTrajOf_close
#print axioms Transpose.Tape.rescaledTraj_limit_lipschitz
#print axioms Transpose.Tape.residentPair
#print axioms Transpose.Tape.robustCE_TM_att_iff
#print axioms Transpose.Tape.robustCE_TM_att_iff_robustCE_TM
#print axioms Transpose.Tape.robustCE_TM_dist_iff_robustNoCode
#print axioms Transpose.Tape.robustCE_TM_gamma_iff
#print axioms Transpose.Tape.robustCE_TM_gamma_per_iff
#print axioms Transpose.Tape.robustCE_TM_iff_robustNoCode
#print axioms Transpose.Tape.robustCE_TM_lin_iff
#print axioms Transpose.Tape.robustNoCode_bits_iff
#print axioms Transpose.Tape.robustNoCode_iff_attached
#print axioms Transpose.Tape.robustNoCode_iff_coent
#print axioms Transpose.Tape.robustNoCode_iff_forall_cap
#print axioms Transpose.Tape.robustNoCode_iff_hint
#print axioms Transpose.Tape.robustNoCode_io_of_robustNoCode
#print axioms Transpose.Tape.robustNoCode_logBits_iff
#print axioms Transpose.Tape.robustNoCode_of_gainBound
#print axioms Transpose.Tape.robustNoCode_with_iff
#print axioms Transpose.Tape.robustNoCode_with_k_iff
#print axioms Transpose.Tape.robustNoCode_with_of_robustNoCode
#print axioms Transpose.Tape.robust_io_tfae
#print axioms Transpose.Tape.robust_tfae
#print axioms Transpose.Tape.rootNode
#print axioms Transpose.Tape.rowDist_sum_ge
#print axioms Transpose.Tape.run
#print axioms Transpose.Tape.runDiagram
#print axioms Transpose.Tape.sSet
#print axioms Transpose.Tape.sideCode
#print axioms Transpose.Tape.slotLen
#print axioms Transpose.Tape.slotOf
#print axioms Transpose.Tape.slot_block_step
#print axioms Transpose.Tape.slot_cut_bound
#print axioms Transpose.Tape.slot_cut_bound_partition
#print axioms Transpose.Tape.snkCols
#print axioms Transpose.Tape.solves_mono
#print axioms Transpose.Tape.solves_profileCap_addTapes
#print axioms Transpose.Tape.solves_shiftCode
#print axioms Transpose.Tape.srcRows
#print axioms Transpose.Tape.srcRows_slotSteps_card_le
#print axioms Transpose.Tape.stepN_init_eq_some_iff
#print axioms Transpose.Tape.structCount
#print axioms Transpose.Tape.sum_cap_le
#print axioms Transpose.Tape.sum_cross_blockCap_le
#print axioms Transpose.Tape.sum_cutPairs_ge
#print axioms Transpose.Tape.tendstoUniformlyOn_of_mem
#print axioms Transpose.Tape.theoremMStar_class_nonuniform
#print axioms Transpose.Tape.theoremMStar_conclusion_can_fail
#print axioms Transpose.Tape.theoremMStar_diagram
#print axioms Transpose.Tape.theoremMStar_diagram_profile
#print axioms Transpose.Tape.theoremMStar_excess
#print axioms Transpose.Tape.theoremMStar_excess_nonuniform
#print axioms Transpose.Tape.theoremMStar_excess_robust
#print axioms Transpose.Tape.theoremMStar_level
#print axioms Transpose.Tape.theoremMStar_level_adaptive
#print axioms Transpose.Tape.theoremMStar_level_class
#print axioms Transpose.Tape.theoremMStar_level_class_on
#print axioms Transpose.Tape.theoremMStar_level_diagram
#print axioms Transpose.Tape.theoremMStar_level_nonuniform
#print axioms Transpose.Tape.theoremMStar_level_robust
#print axioms Transpose.Tape.theoremMStar_level_sub
#print axioms Transpose.Tape.theoremMStar_level_subseq
#print axioms Transpose.Tape.theoremMStar_level_walk
#print axioms Transpose.Tape.theoremMStar_walk
#print axioms Transpose.Tape.theoremP
#print axioms Transpose.Tape.theoremP_bits
#print axioms Transpose.Tape.theoremP_bits_add_one
#print axioms Transpose.Tape.theoremP_div
#print axioms Transpose.Tape.theoremP_greedy
#print axioms Transpose.Tape.theoremP_grouped
#print axioms Transpose.Tape.theoremP_grouped_bits
#print axioms Transpose.Tape.theoremP_grouped_on
#print axioms Transpose.Tape.theoremP_grouped_on_bits
#print axioms Transpose.Tape.theoremP_hyps_tr2
#print axioms Transpose.Tape.theoremP_hyps_tr2k
#print axioms Transpose.Tape.theoremP_on
#print axioms Transpose.Tape.theoremP_on_bits
#print axioms Transpose.Tape.theoremP_on_div
#print axioms Transpose.Tape.theoremP_on_pow
#print axioms Transpose.Tape.theoremP_on_robust
#print axioms Transpose.Tape.theoremP_on_robust_gamma
#print axioms Transpose.Tape.theoremP_pow
#print axioms Transpose.Tape.theoremPprime
#print axioms Transpose.Tape.theoremPprime_bits
#print axioms Transpose.Tape.theoremPprime_div
#print axioms Transpose.Tape.theoremPprime_gamma
#print axioms Transpose.Tape.theoremPprime_greedy
#print axioms Transpose.Tape.theoremPprime_grouped
#print axioms Transpose.Tape.theoremPprime_grouped_bits
#print axioms Transpose.Tape.theoremPprime_grouped_on
#print axioms Transpose.Tape.theoremPprime_grouped_on_bits
#print axioms Transpose.Tape.theoremPprime_hyps_of_oblivious
#print axioms Transpose.Tape.theoremPprime_hyps_tr2dd
#print axioms Transpose.Tape.theoremPprime_linearTime
#print axioms Transpose.Tape.theoremPprime_no_five_pass
#print axioms Transpose.Tape.theoremPprime_on
#print axioms Transpose.Tape.theoremPprime_on_bits
#print axioms Transpose.Tape.theoremPprime_on_div
#print axioms Transpose.Tape.theoremPprime_on_greedy
#print axioms Transpose.Tape.theoremPprime_on_pow
#print axioms Transpose.Tape.theoremPprime_on_robust
#print axioms Transpose.Tape.theoremPprime_on_robust_gamma
#print axioms Transpose.Tape.theoremPprime_pow
#print axioms Transpose.Tape.theoremPprime_ratio
#print axioms Transpose.Tape.touchRes
#print axioms Transpose.Tape.touchRes_admissible
#print axioms Transpose.Tape.touchRes_begin_unique
#print axioms Transpose.Tape.touchRes_chord_source_unique
#print axioms Transpose.Tape.touchRes_chord_target_unique
#print axioms Transpose.Tape.touchRes_end_unique
#print axioms Transpose.Tape.tpos
#print axioms Transpose.Tape.tpos_spec
#print axioms Transpose.Tape.tr2_cutPairs
#print axioms Transpose.Tape.tr2_obliviousOn
#print axioms Transpose.Tape.tr2_transposes
#print axioms Transpose.Tape.tr2k_obliviousOn
#print axioms Transpose.Tape.tr2k_transposes
#print axioms Transpose.Tape.traceBits_le
#print axioms Transpose.Tape.traceClass_code
#print axioms Transpose.Tape.traceClass_coent_lt
#print axioms Transpose.Tape.traceClass_of_mem
#print axioms Transpose.Tape.traceClass_of_oblivious
#print axioms Transpose.Tape.traceClass_of_obliviousOn
#print axioms Transpose.Tape.traceConst
#print axioms Transpose.Tape.traceCount
#print axioms Transpose.Tape.transAt
#print axioms Transpose.Tape.transposes_of_transposesWithin
#print axioms Transpose.Tape.uncovered_cols_le
#print axioms Transpose.Tape.uncovered_cols_le_len
#print axioms Transpose.Tape.uncovered_cols_le_slots
#print axioms Transpose.Tape.uncovered_cols_le_slots_len
#print axioms Transpose.Tape.unitSteps_inTraj
#print axioms Transpose.Tape.unitSteps_workTraj
#print axioms Transpose.Tape.volume_gap
#print axioms Transpose.Tape.weak_duality
#print axioms Transpose.Tape.work_eq_blank
#print axioms Transpose.Tape.work_eq_written
#print axioms Transpose.TransposesWithin
#print axioms Transpose.encode
#print axioms Transpose.entryBits

import options

import helpers
import math
import future
import tables
import formula
import strutils

proc sattreeil*(f : formula,
               goal : Option[sf_index_t],
               neg_goal : Option[sf_index_t],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.rhd_sf + f.prop_sf
  #echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans
  if persistent_bans * persistent_truths != {} or
    (goal.is_some and goal.get in persistent_bans) or
    (neg_goal.is_some and neg_goal.get in persistent_truths) :
    #echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets(prefer_smaller = false):
    # todo: provjeri ovo, kako znaš da je konzistentan persistent_truths?
    # mislim da bi smio staviti samo persistent_truths * gamma0
    let K = persistent_truths + varK
    ##
    #if lev == 0 and (byte2 notin K or byte5 in K or byte9 in K or byte7 in K):
    #  continue

    let truths = f.extend_forcing(K * gamma0)
    #echo repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal.is_none or goal.get in truths
    let neg_goal_avoided = neg_goal.is_none or neg_goal.get notin truths
    let pers_truths_satisfied = persistent_truths <= truths
    let pers_bans_avoided     = persistent_bans * truths == {}
    #echo repeat("  ", lev), goal_satisfied, neg_goal_avoided, pers_truths_satisfied, pers_bans_avoided
    if not( goal_satisfied and neg_goal_avoided and pers_truths_satisfied and pers_bans_avoided ):
       continue
    let N_boxed = f.boxed_sf - K
    let N_rhd   = f.rhd_sf - K
    let I       = f.rhd_sf * K
    #echo repeat("  ", lev), "I=", I, " Nrhd=", N_rhd, " Nb=", N_boxed

    if N_boxed == {} and N_rhd == {}:
      #echo repeat("  ", lev), "SUCC"
      return true

    let base_pbans = persistent_bans + (if goal.is_some(): { goal.get} else: {})
    let base_pthruths = persistent_truths +
      f.boxed_sf * K +
      ((f.boxed_sf * K).map boxD => f[boxD, left]) +
      (if neg_goal.is_some(): {neg_goal.get} else: {})
    var found_ok_I_for_boxes = false
    for I_witnesses in I.subsets(prefer_smaller = true):
      let I_bans = I - I_witnesses
      let pbans = base_pbans + (I_bans.map CrhdD => f[CrhdD, left])
      let ptruths = base_pthruths
      # TODO: mijenjaj bit oko CrhdD u zabranama
      let ok_negs = N_boxed.all do (boxC : sf_index_t) -> bool:
        let C = f[boxC, left]
        return sattreeil(f, goal = none sf_index_t, neg_goal = some C, pbans, ptruths + {boxC}, lev + 1)
      let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
        let G = f[ErhdG, right]
        return sattreeil(f, goal = some G, neg_goal = none sf_index_t, pbans, ptruths, lev + 1)
      if ok_negs and ok_pos:
        found_ok_I_for_boxes = true
        break
    if not found_ok_I_for_boxes:
      continue
    #var created_I_witnesses : set[uint16]  # successful (D, E>G) pairs, neće raditi jer ovisi o drugima EG
    var N_rhd_by_rhs = init_table[sf_index_t, set_of_fs]()
    var Ds : set[sf_index_t]
    for CrhdD in N_rhd:
      let
        C = f[CrhdD, left]
        D = f[CrhdD, right]
      Ds.incl D
      if not N_rhd_by_rhs.hasKeyOrPut(D, {CrhdD}):
        N_rhd_by_rhs[D].incl CrhdD

    let all_satisfied_rhd = Ds.all do (D : sf_index_t) -> bool:
      #echo repeat("  ", lev), "za ", D
      let base_D_pbans = base_pbans + {D}
      for I_witnesses in I.subsets(prefer_smaller = false):
        let I_bans = I - I_witnesses
        let pbans = base_D_pbans + (I_bans.map CrhdD => f[CrhdD, left])
        let ptruths = base_pthruths
        #echo repeat("  ", lev), I_witnesses, " pb ", base_D_pbans, I_bans, " pt ", ptruths
        # TODO: mijenjaj bit oko CrhdD u zabranama
        let ok_negs = N_rhd_by_rhs[D].all do (CrhdD : sf_index_t) -> bool:
          let C = f[CrhdD, left]
          return sattreeil(f, goal = some C, neg_goal = none sf_index_t, pbans, ptruths + {CrhdD}, lev + 1)
        let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
          let G = f[ErhdG, right]
          return sattreeil(f, goal = some G, neg_goal = none sf_index_t, pbans, ptruths, lev + 1)
        if ok_negs and ok_pos: return true # this block made it
      false # this block is not satisfiable
    if all_satisfied_rhd:
      #echo repeat("  ", lev), "sat:", K
      return true
  #echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false

proc sattreeil*(f : formula) : bool = sattreeil(f, some sf_index_t f.root, none sf_index_t, {}, {})

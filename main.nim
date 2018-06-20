import math
import sets
import tables
import strutils
import typetraits
import sequtils
import options
import future
import lists
import times
import algorithm
import os
import parseutils

import helpers
import formula

#[  sequent calculus  ]#


method axiom(s : ref sequent) : bool =
  return 
    s.ante.any( (a) => a.ft == falsum ) or   
    s.succ.any( (b) => b.ft == verum ) or 
    s.ante.any( (a) => s.succ.any( (b) => a.equals b ) ) 



var ts = 0
method inversion(s : ref sequent, todo : var seq[ref sequent]) : bool =
  if (len todo) > 100:
    #raise new_exception(ValueError, "too long")
    return false
  if axiom s:
    return true

  assert(is_nil s.left)
  assert(is_nil s.right)

  var left, right : ref sequent
  left = nil
  right = nil

  var good : bool = true
  var best_formula : ref formula = nil
  var best_formula_i = 0
  var best_formula_pos = 0

  for i, f in s.ante:
    case f.ft
      of {falsum, verum, neg, conditional, land, lor, notcond}:
        best_formula = f
        best_formula_i = i
        best_formula_pos = -1
        break
      of {forall, exists}:
        if (not best_formula.is_nil) and best_formula.ft notin {forall, exists}:
          continue
        if best_formula.is_nil or f.last_instanced_ts < best_formula.last_instanced_ts or
          (f.last_instanced_ts == best_formula.last_instanced_ts) and f.ft == exists:
          best_formula = f
          best_formula_i = i
          best_formula_pos = -1
      else:
        discard
  for i, f in s.succ:
    case f.ft
      of {falsum, verum, neg, conditional, land, lor, notcond}:
        best_formula = f
        best_formula_i = i
        best_formula_pos = 1
        break
      of {forall, exists}:
        if (not best_formula.is_nil) and best_formula.ft notin {forall, exists}:
          continue  
        #echo " \n ~~~> \n ",  $f.ft, " ", $f, " ", $best_formula.ft, " ", $best_formula
        if best_formula.is_nil or f.last_instanced_ts < best_formula.last_instanced_ts or
          (f.last_instanced_ts == best_formula.last_instanced_ts) and f.ft == forall:
          best_formula = f
          best_formula_i = i
          best_formula_pos = 1
        #echo "::  ", $best_formula.ft, $best_formula
      else:
        discard
      
  let f = best_formula
  let i = best_formula_i

  if best_formula_pos == -1:
    case f.ft 
      of arity0_operators:
        todo.add( new(sequent) )
        todo[-1 + len todo].deep_copy s
        left = todo[-1 + len todo]; s.left = left
      of neg, land, forall, exists:
        todo.add( new(sequent) )
        todo[-1 + len todo].deep_copy s
        left = todo[-1 + len todo]; s.left = left
      of lor, conditional:
        todo.add( new(sequent) ); todo.add( new(sequent) )
        todo[-2 + len todo].deep_copy s
        todo[-1 + len todo].deep_copy s
        left = todo[-2 + len todo]; s.left = left
        right = todo[-1 + len todo]; s.right = right
      else:
        raise new_exception(ValueError,  "unknown operator")

    case f.ft 
      of arity0_operators:
        discard
      of neg:
        left.succ.add f.left
      of land:
        left.ante.add f.left
        left.ante.add f.right
      of lor:
        left.ante.add f.left
        right.ante.add f.right
      of conditional:
        left.succ.add f.left
        right.ante.add f.right
      of {forall, exists}:
        let f = left.ante[i]       
        let q = f.left.identifier
        let templat = f.right
        f.last_instanced_ts = ts # important: changing the new instances
        inc ts
        let (rls, terms) = relationals s
        var found = false
        var sub = ""
        if f.ft == forall:
          for t in terms:
            if not left.ante.any_it( templat.is_subst_of(it, q, t) ):
              found = true
              sub = t
              break
        if not found:
          var k = 0
          while "e" & $k in terms:
            inc k
          sub = "e" & $k
        var inst : ref formula
        inst.deep_copy templat 
        inst.subst(q, sub)
        inst.last_instanced_ts = -ts
        left.ante.add inst
      else:
        raise new_exception(ValueError,  "unknown operator " & $f.ft)
    if not left.is_nil:
      if f.ft notin {exists, forall}:
        left.ante.del i 
      good = good and left.inversion todo
    if not right.is_nil:
      right.ante.del i 
      good = good and right.inversion todo
    return good

  case f.ft 
    of arity0_operators:
      todo.add( new(sequent) )
      todo[-1 + len todo].deep_copy s
      left = todo[-1 + len todo]; s.left = left
    of neg, lor, conditional, forall, exists:
      todo.add( new(sequent) )
      todo[-1 + len todo].deep_copy s
      left = todo[-1 + len todo]; s.left = left
    of land:
      todo.add( new(sequent) ); todo.add( new(sequent) )
      todo[-2 + len todo].deep_copy s
      todo[-1 + len todo].deep_copy s
      left = todo[-2 + len todo]; s.left = left
      right = todo[-1 + len todo]; s.right = right
    else:
      raise new_exception(ValueError,  "unknown operator")

  case f.ft 
    of neg:
      left.ante.add f.left
    of lor:
      left.succ.add f.left
      left.succ.add f.right
    of land:
      left.succ.add f.left
      right.succ.add f.right
    of conditional:
      left.ante.add f.left
      left.succ.add f.right
    of {forall, exists}:
      let f = left.succ[i]
      let q = f.left.identifier
      let templat = f.right
      f.last_instanced_ts = ts # important: changing the new instances
      inc ts
      let (rls, terms) = relationals s
      var found = false
      var sub = ""
      if f.ft == exists:
        for t in terms:
          if not left.succ.any_it( templat.is_subst_of(it, q, t) ):
            #for ll in left.succ:
            #  echo is_subst_of(ll, from_prefix("Ree"), "y", "e") 
            found = true
            sub = t
            break
      if not found:
        var k = 0
        while "e" & $k in terms:
          inc k
        sub = "e" & $k
      var inst : ref formula
      inst.deep_copy templat 
      inst.subst(q, sub)
      inst.last_instanced_ts = -ts
      left.succ.add inst
    else:
      raise new_exception(ValueError,  "unknown operator")
  # echo f.ft, "tu: ", $(left.is_nil), $(right.is_nil), "---"
  if not left.is_nil:
    #if 100 > len todo:
    #  echo "pr", left, " ", i
    if f.ft notin {exists, forall}:
      left.succ.del i 
    #if 100 > len todo:
    #  echo "po", left
    good = good and left.inversion todo
  if not right.is_nil:
    right.succ.del i 
    good = good and right.inversion todo
  return good
    

proc seqtree(s : ref sequent, depth : int = 0) : void =
  if s.is_nil: return
  echo repeat(' ', depth * 2), $s
  if not s.left.is_nil: seqtree(s.left, depth + 1)
  if not s.right.is_nil: seqtree(s.right, depth + 1)

#[
block:
  var a, b : seq[int]
  a = @[1, 2]
  b = a
  b.add 5
  echo b.join " "
  quit()
]#

var s : ref sequent
new(s)
s.ante = @[ from_prefix "Ax-Ey&RxyAzRyzEy~Rxy" ]
s.succ = @[ from_prefix "AxEy~Rxy" ]
echo $s
var todo : seq[ref sequent] = @[]
  
let b = s.inversion todo
echo $b, " ", todo.join(" ")

seqtree(s)
var (rls, vars) = relationals(s)
echo (rls.join " "), " <> ", vars.join " "


var fr = from_prefix "-AxAyRxyzAxAyRxyz"
fr.subst("z", "c")



#echo $fr

#[
let f = from_infix "(T > DT) & DT"   # "((T > T) > T) & ~[] #"
echo repr f
echo sattreeil f
echo sattreeilw f
quit()
]#


#[
echo "total time:", stopwatch do:
  let stotal, total = search_job(0, threads, length)

  var i = 0
  var sorted_hs = to_seq highscore.keys()
  sort(sorted_hs, system.cmp[float])
  for sfr in sorted_hs:
    let f = from_prefix highscore[sfr]
    echo sfr, " : ", f
    if i > 10:
      break
  echo total



let frm = from_infix "(p > q) -> (~(p > ~c) > (q & Bc))" #
#let frm = from_infix "~(~(T > p) > #)" # (p > q) &
echo repr frm
echo sattreeil frm

quit()

]#

quit()

import helpers
import formula
import future
import lists

# this checks whether the subsequence of the first occurences of letters starts with 'a', is sorted and without holes
# eg superduper --aab, --aba, -----abacba, but not superduper b, -ac, ---abad
# name inspired by robert webb <3
proc superduper*(fs : string) : bool =
  var current_max = ord('a')-1
  let ops_syms = lc[(ft_to_chr x) | (x <- all_operators), char]
  for i, c in fs:
    let cc = ord c
    if c in ops_syms:
      continue
    if cc <= current_max:
      continue
    if cc == current_max + 1:
      current_max += 1
    elif cc > current_max + 1:
      return false
  return true


iterator prefix_formulas*(length : int, ops = {falsum, verum, conditional, box, diamond}, variables : int = -1) : string =
  let op0 = arity0_operators * ops
  let op1 = arity1_operators * ops
  let op2 = arity2_operators * ops

  let variables = if variables == -1: if op1.card > 0: length div 2 else: 1 else: variables
  let var_syms  = lc[$char(i + ord('a'))  |  (i <- 0..variables-1), string]
  let ar0_syms  = var_syms & lc[($ ft_to_chr x) | (x <- op0), string]
  let ar1_syms  = lc[($ ft_to_chr x) | (x <- op1), string]
  let ar2_syms  = lc[($ ft_to_chr x) | (x <- op2), string]

  # we will build formulas recursively by complexity, saving the previous stages
  var fcache    = new_seq[ SinglyLinkedList[string] ](length)
  fcache[0] = to_list ar0_syms
  for stage in 2..length:
    fcache[stage - 1] = to_list lc[ (op & f) | (op <- ar1_syms, f <- fcache[stage - 1 - 1]), string ]

    for pstage1 in 1..stage-2:
      let pstage2 = stage - pstage1 - 1
      if pstage2 < pstage1:
        continue
      for op in ar2_syms:
        for f1 in fcache[pstage1 - 1]:
          for f2 in fcache[pstage2 - 1]:
            fcache[stage - 1].prepend(op & f1 & f2)
            if pstage1 != pstage2:  # skip adding (b, a) if we already have (a, b)
              fcache[stage - 1].prepend(op & f2 & f1)

  for stage in fcache:
    for f in stage:
      if superduper f:
        yield f

iterator formulas*(length : int, ops = {falsum, verum, conditional, box, diamond}, variables : int = -1) : formula =
  for f in prefix_formulas(length, ops, variables):
    yield from_prefix f

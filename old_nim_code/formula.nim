import helpers
import tables
import strutils
import future
import sequtils
import algorithm

const max_length : int = 256

type
  identifier_type* = string
  formula_type* = enum
    undefined
    falsum
    verum
    conditional
    land
    lor
    notcond
    neg
    forall
    exists
    relational
    functional
    variable
    id
  formula* = object
    ft*    : formula_type

    # connectives and quantifiers
    left*   : ref formula
    right*  : ref formula

    # quantifiers, relational, variable
    identifier*   : identifier_type
    vars* : seq[ref formula]

    last_instanced_ts* : int64
    # last_instanced_vars : seq[formula]
    # last_instanced_


const arity0_operators* = {falsum, verum}
const arity1_operators* = {neg}
const arity2_operators* = {conditional, land, lor, notcond, forall, exists}
const all_operators* = arity0_operators + arity1_operators + arity2_operators

proc toks(str : string, i : int) : tuple[curr: char, peek: char] =
  let c = str[i + 0]
  let p = case (len str) - i
    of 1: '\0'
    else: str[i + 1]
  (c, p)

proc chr_to_ft*(chr : char) : formula_type =
  case chr
    of '#': falsum
    of 'T': verum
    of '-': conditional
    of '&': land
    of '|': lor
    of '%': notcond
    of 'A': forall
    of 'E': exists
    of '~': neg
    of '(': id
    else  : undefined

method `$`*(f : formula) : string {.noSideEffect.} 
method `$`*(f : ref formula) : string {.noSideEffect.} 


proc from_prefix*(a : string, index : var int) : ref formula =
  var s = a[index]
  let ft = chr_to_ft s
  inc index
  new(result)
  result.left = nil
  result.right = nil
  result.last_instanced_ts = -1
  result.vars = @[]
  result.ft = ft
  case ft
    of arity0_operators:  # T, #
      discard  
    of arity1_operators:  # ~
      let arg   = from_prefix(a, index)
      result.left = arg
    of arity2_operators:  # A, E, >, &, %, |, -
      let vleft  = from_prefix(a, index)
      let vright = from_prefix(a, index)
      result.left = vleft
      result.right = vright
    else: # variable or relational
      if is_upper_ascii s:
        result.ft = relational
        result.identifier = $s
        result.vars = @[]
        
        if index >= len a:
          return result
        s = a[index]
        inc index
        while (is_space s) or is_lower s:          
          if is_lower s:
            var vr : ref formula
            new(vr)
            vr.ft = variable
            vr.identifier = $s
            result.vars.add vr

          if index >= len a:
            return result
          s = a[index]    
          inc index
        dec index

      elif is_lower_ascii s:
        result.ft = variable
        result.identifier = $s
  result

proc from_prefix*(a : string) : ref formula =
  var i  : int
  from_prefix(a, i)

proc `$`*(ft : formula_type) : string =
  case ft
    of falsum:      "\u27c2"
    of verum:       "\u22a4"
    of notcond:     "\u219b"
    of conditional: "\u2192"
    of land:        "\u2227"
    of lor:         "\u2228"
    of neg:         "\uac"
    of forall: "\u2200"
    of exists: "\u2203"
    else:           "\u1f631"

proc ft_to_chr*(ft : formula_type) : char =
  case ft
    of falsum:      '#'
    of verum:       'T'
    of conditional: '-'
    of land:        '&'
    of lor:         '|'
    of notcond:     '%'
    of neg:         '~'
    of forall:      'A'
    of exists:      'E'
    else:           '?'
  



proc f_to_str*(f : formula) : string {.noSideEffect.} =
  let ft = f.ft
  result = case ft
    of arity0_operators: $ft
    of arity1_operators: $ft & f_to_str(f.left[])
    of arity2_operators:
      if ft in [forall, exists]: (discard $f.last_instanced_ts; "") & $ft & f_to_str(f.left[]) & f_to_str(f.right[]) 
      else: "(" & f_to_str(f.left[]) & ' ' & $ft & ' ' & f_to_str(f.right[]) & ")"
    of relational:       f.identifier & "(" & f.vars.join(" ") & ")"
    of variable:         f.identifier
    else:                $ft

method `$`*(f : formula) : string {.noSideEffect.} =
  return f_to_str(f)

method `$`*(f : ref formula) : string {.noSideEffect.} =
  return f_to_str(f[])

# this is just for infix -> prefix conversion
type exprnode = object
  ftype : formula_type
  data  : string
  lexpr : ref exprnode
  rexpr : ref exprnode
  

proc infixp(str : string, i : var int, preferunary : bool = false) : ref exprnode =
  new(result)

  var c, p : char
  (c, p) = toks(str, i)
  var am_unary = preferunary

  var ft = chr_to_ft c
  result.ftype = ft

  case ft
    of id:
      inc i
      result.lexpr = infixp(str, i, false)
      inc i
      (c, p) = toks(str, i)
      assert(c == ')')
    of arity1_operators:
      inc i
      result.lexpr = infixp(str, i, true)
    of exists, forall:
      inc i
      result.lexpr = infixp(str, i, true)
      inc i
      result.rexpr = infixp(str, i, true)
    of arity0_operators:
      result.ftype = ft
    else:
      # relational or a variable
      if is_lower c:
        result.ftype = variable
        result.data  = $c
      else:
        result.ftype = relational
        result.data  = $c
        while p != '\0' and is_lower p:
          inc i
          (c, p) = toks(str, i)
          result.data &= $c
  # do we already know this expr is unary?
  if am_unary:
    return result

  # expr is allowed to be binary, is it?
  (c, p) = toks(str, i)
  let tn = chr_to_ft p
  if tn notin arity2_operators:
    return result

  # expr is binary
  let lexpr = result
  new(result)
  result.lexpr = lexpr

  inc i
  (c, p) = toks(str, i)
  ft = chr_to_ft c
  result.ftype = ft

  inc i
  (c, p) = toks(str, i)
  ft = chr_to_ft c

  new(result.rexpr)
  result.rexpr.ftype = ft
  case ft
    of id:
      inc i
      result.rexpr.lexpr = infixp(str, i, false)
      inc i
      (c, p) = toks(str, i)
      assert(c == ')')
    of arity1_operators:
      inc i
      result.rexpr.lexpr = infixp(str, i, true)
    of exists, forall:
      inc i
      result.rexpr.lexpr = infixp(str, i, true)
      inc i
      result.rexpr.rexpr = infixp(str, i, true)
    of arity0_operators:
      result.rexpr.ftype = ft
    else:
      # relational or a variable
      if is_lower c:
        result.rexpr.ftype = variable
        result.rexpr.data  = $c
      else:
        result.rexpr.ftype = relational
        result.rexpr.data  = $c
        while p != '\0' and is_lower p:
          inc i
          (c, p) = toks(str, i)
          result.rexpr.data &= $c
  result

proc infixp(str : string) : ref exprnode =
  var i = 0
  return infixp(replace(str, " ", ""), i)

proc exprnode_to_prefix(e : ref exprnode) : string =
  case e.ftype
    of variable, relational:
      $e.data
    of arity0_operators:
      $ft_to_chr(e.ftype)
    of arity1_operators:
      ft_to_chr(e.ftype) & exprnode_to_prefix(e.lexpr)
    of arity2_operators:
      ft_to_chr(e.ftype) & exprnode_to_prefix(e.lexpr) & exprnode_to_prefix(e.rexpr)
    of id:
      exprnode_to_prefix(e.lexpr)
    else:
      "???"

proc from_infix*(str : string) : ref formula =
  from_prefix exprnode_to_prefix infixp multi_replace(str, ("->", "-"), ("&&", "&"), ("\\/", "|"), ("||", "|"), ("/\\", "&"),
                                 ("_|_", "#"), ("[]", "B"), ("<>", "D"), ("¬", "~"), ("|>", ">"), ("*", "&"), ("+", "|"),
                                 ("\u27c2", "#"), ("\u22a4", "T"), ("\u22B3", ">"), ("\u219b", "%"), ("\u2192", "-"),
                                 ("\u2227", "&"), ("\u2228", "|"), ("\u25fb", "B"), ("\u25ca", "D"), ("\uac", "~"),
                                 ("forall", "A"), ("exists", "E") )



method subst*(first : ref formula, oldid : string, newid : string) : void =
  if first.is_nil or first.ft in {forall, exists} and first.left.identifier == oldid: return
  
  if first.identifier == oldid:
    first.identifier = newid

  if not first.vars.is_nil: 
    for x in first.vars:
      subst(x, oldid, newid)
  if not first.left.is_nil: subst(first.left, oldid, newid)
  if not first.right.is_nil: subst(first.right, oldid, newid)

proc streql(a, b, oldid, newid : string) : bool =
  # is b a, when oldid in a gets replaced with newid?
  if a == oldid:
    b == newid
  else:
    a == b

method is_subst_of*(first : ref formula, other : ref formula, oldid : string, newid : string) : bool =
  if first.is_nil and other.is_nil:
    return true
  if first.is_nil or other.is_nil:
    return false
  let ft = first.ft
  if ft != other.ft: 
    return false

  result = case ft
    of arity0_operators: true
    of arity1_operators: first.left.is_subst_of( other.left, oldid, newid)
    of arity2_operators: first.left.is_subst_of(other.left, oldid, newid) and first.right.is_subst_of(other.right, oldid, newid)
    of relational:       streql(first.identifier, other.identifier, oldid, newid) and zip(first.vars, other.vars).all( x => x[0].is_subst_of(x[1], oldid, newid)) 
    of variable:         streql(first.identifier, other.identifier, oldid, newid)
    else:                raise new_exception(ValueError,  "comparison of unknown formulae")
  
method equals*(first : ref formula, second : ref formula) : bool =
    first.is_subst_of second, "", ""
    
method relationals*(f : ref formula, bound : seq[string],
  rls : var seq[string], vars : var seq[string]): void {.noSideEffect.} =
  if f.ft == relational and f.identifier notin rls:
    rls.add f.identifier
  if f.ft == variable and f.identifier notin vars and f.identifier notin bound:
    vars.add f.identifier  
  let bound_f = 
    if f.ft in {exists, forall}:
      bound & @[f.left.identifier] 
    else: 
      bound 
  if not f.left.is_nil:
    relationals(f.left, bound_f, rls, vars)
  if not f.right.is_nil:
    relationals(f.right, bound_f, rls, vars)
  if not f.vars.is_nil:
    for v in f.vars:
      relationals(v, bound_f, rls, vars)
    


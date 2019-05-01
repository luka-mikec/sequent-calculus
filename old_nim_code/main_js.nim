# javascript frontend
import dom
import helpers
import formula
import sequent

proc seqtree*(s : ref sequent, depth : int = 0) : void =
  if s.is_nil: return
  #discard readLine(stdin)
  if not s.left.is_nil: seqtree(s.left, depth + 1)
  if not s.right.is_nil: seqtree(s.right, depth + 1)

proc check*(sf : cstring) : void {.exportc.}  =
  let f = from_infix $sf

  document.writeln("test")

 



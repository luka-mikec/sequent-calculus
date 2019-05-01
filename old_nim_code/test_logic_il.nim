import sequtils
import future

import formula
import logic_il

include principles


let
  taut = [gl, k4, k, j1, j2, j3, j4, j5]
  cont = [m, m0, p, f, w, wx, p0, r, r1, km1, km2, kw1, kw10, kw2, kw3, kw4, ipm]
  should_true  = @taut & @cont & @cont.map (x => "~(" & x & ")")
  should_false = @taut.map (x => "~(" & x & ")")

for f in should_true:
  let frm = from_infix f
  echo frm
  echo sattreeil frm

for f in should_false:
  let frm = from_infix f
  echo frm
  echo (not sattreeil frm)

echo "all test ok: ", should_true.all_it (sattreeil from_infix it) and should_false.all_it(not sattreeil from_infix it)

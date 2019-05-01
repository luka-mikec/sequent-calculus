import formula
import sequent


# "ExAyEzAwRxyzw"
# "AyExAwEzRxyzw"
var s = init_sequent("Ax Rx", "Ey(Py - AxPx)")
echo $s

var todo : seq[ref sequent] = @[]
let b = s.inversion todo

seqtree(s)

echo "Valid: ", b

#var (rls, vars) = relationals(s)
#echo (rls.join " "), " <> ", vars.join " "


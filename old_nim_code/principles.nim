# this file should be *included*, not imported, where needed

const # axioms of IL
  gl = "◻(◻p → p) → ◻p"
  k4 = "◻p → ◻◻p"
  k  = "◻(p → q) → (◻p → ◻q)"
  j1 = "◻(p → q) → (p ⊳ q)"
  j2 = "(p ⊳ q) → ((q ⊳ s) → (p ⊳ s))"
  j3 = "((p ⊳ s) ∧ (q ⊳ s)) → ((p ∨ q) ⊳ s)"
  j4 = "(p ⊳ q) → (◊p → ◊q)"
  j5 = "◊p ⊳ p"

const # extensions
  m  = "(p ⊳ q) → ((p ∧ ◻s) ⊳ (q ∧ ◻s))"
  m0 = "(p ⊳ q) → ((◊p ∧ ◻s) ⊳ (q ∧ ◻s))"
  p  = "(p ⊳ q) → ◻(p ⊳ q)"
  f  = "(p ⊳ ◊p) → ◻¬p"
  w  = "(p ⊳ q) → (p ⊳ (q ∧ ◻¬p))"
  wx = "(p ⊳ q) → ((q ∧ ◻s) ⊳ ((q ∧ ◻¬p) ∧ ◻s))"
  p0 = "(p ⊳ ◊q) → ◻(p ⊳ q)"
  r  = "(p ⊳ q) → (¬(p ⊳ ¬c) ⊳ (q ∧ ◻c))"
  r1 = "(p ⊳ q) → ((¬(p ⊳ ¬c) ∧ (x ⊳ ◊y)) ⊳ ((q ∧ ◻c) ∧ (x ⊳ y)))"
  km1 = "(p ⊳ ◊q) → ◻(p → ◊q)"
  km2 = "(p ⊳ q) → (◻(q → ◊s) → ◻(p → ◊s))"
  kw1 = "(p ⊳ ◊⊤) → (⊤ ⊳ ¬p)"
  kw10 = "((p ∧ q) ⊳ ◊p) → (p ⊳ (p ∧ ¬q))"
  kw2 = "(p ⊳ ◊q) → (q ⊳ (q ∧ ¬p))"
  kw3 = "(p ⊳ (q ∨ ◊p)) → (p ⊳ q)"
  kw4 = "(p ⊳ q) → (q ⊳ (q ∧ ◻¬p))"
  ipm = "(p ⊳ ◊q) → ◻(p ⊳ ◊q)"

const all_principles = @[gl, k4, k, j1, j2, j3, j4, j5, m, m0, p, f, w, wx, p0, r, r1, km1, km2, kw1, kw10, kw2, kw3, kw4]

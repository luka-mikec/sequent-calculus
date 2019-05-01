import lists
import times
import strutils
import math

proc stopwatch*( f : proc  ) : float =
  when declared cpu_time:
    result = cpu_time()
  else:
    when declared epoch_time:
      result = epoch_time()
  f()
  when declared cpu_time:
    result = cpu_time() - result
  else:
    when declared epoch_time:
      result = epoch_time() - result

#type bitset_type = int16
proc `[]`(x : int16, i : int) : bool = (x shr i) mod 2 == 1
proc `[]=`(x : var int16, i : int, b : bool) : void =
  if x[i] and not b   or   not x[i] and b:
    x = x xor (int16(1) shl i)
proc `[]`(x : int16, n : int, i : int, j : int) : bool = (x shr (n*i + j)) mod 2 == 1
proc `[]=`(x : var int16, n : int, i : int, j : int, b : bool) : void =
  if x[n, i, j] and not b   or   not x[n, i, j] and b:
    x = x xor int16(1 shl (n*i + j))
proc swap(x : var int16, i : int, j : int) =
  let old = x[j]
  x[j] = x[i]
  x[i] = old


proc next_permutation*[T](x: var T, n : int): bool {.discardable.} =
  ## from stdlib, modified for bitsets
  if n < 2:
    return false

  var i = n - 1
  while i > 0 and x[i-1] >= x[i]:
    dec i

  if i == 0:
    return false

  var j = n - 1
  while j >= i and x[j] <= x[i-1]:
    dec j

  # swap x[j], x[i-1]
  swap(x, j, i - 1)

  # x.reverse(i, x.high)
  for k in i..n-1:
    if k < n-1-(k-i): # not proud of this
      swap(x, k, n-1-(k-i))
    else:
      break

  result = true

#var test : int16 = cast[int16](0b1000000000000000)

iterator subsets_fast_unsorted*[T](s : set[T], prefer_smaller : bool = true) : set[T] =
  var subset : set[T]
  let m = 2^s.card - 1
  for ii in 0 .. m:
    let i = case prefer_smaller
      of true:  ii
      of false: m - ii
    subset = {}
    var tmpi : auto = i
    for val in s:
      if 1 == tmpi mod 2:
        subset.incl val
      tmpi = tmpi div 2
    yield subset



iterator subsets*[T](s : set[T], prefer_smaller : bool = true) : set[T] =
  var subset : set[T]
  let m = s.card()
  assert(m <= 16)
  for ii in 0 .. m:
    let i : int = case prefer_smaller
      of true:  ii
      of false: m - ii
    var a : int16 =  ((int16(1) shl i) - 1)  shl (m - i)
    var dowhile = true
    while dowhile:
      subset = {}
      #echo to_bin(a, 16)
      var tmpi : auto = a
      for val in s:
        if 1 == tmpi mod 2:
          subset.incl val
        tmpi = tmpi div 2
      yield subset
      dowhile = next_permutation(a, m)
      #echo dowhile

proc filter*[T](s: set[T], pred: proc (x: T): bool): set[T] =
  for val in s:
    if pred(val):
      result.incl val

#let x = {40000, 1, 7, 2, 5}
#for i in x:
#  echo i

proc bitset_to_set*[T](bitset : int64, parent : set[T]) : set[T] =
  var bitset = bitset
  for el in parent:
    if bitset mod 2 == 1:
      result.incl el
    bitset = bitset shr 1

proc all*[T](s: set[T], pred: proc (x: T): bool {.closure.}): bool =
  for val in s:
    if not pred(val):
      return false
  return true

proc some*[T](s: set[T], pred: proc (x: T): bool {.closure.}): bool =
  for val in s:
    if pred(val):
      return true
  return false

proc map*[T, S](s: set[T], f: proc (x: T): S {.closure.}): set[S] =
  for val in s:
    result.incl f(val)

proc to_list*[T](s : seq[T]) : SinglyLinkedList[T] =
  result = initSinglyLinkedList[T]()
  for val in s:
    result.prepend(val)

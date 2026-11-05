// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a

  Deduce(
    1 (max == a) by Premise,
    2 (a > b) by Premise,
    3 (max >= a) by Algebra*(1),
    4 (max >= b) by Algebra*(2,1),
  )
} else {
  max = b

  Deduce(
    1 (max == b) by Premise,
    2 (!(a > b)) by Premise,
    3 (a <= b) by Algebra*(2),
    4 (max >= a) by Algebra*(1,3),
    5 (max >= b) by Algebra*(1),
  )
}

Deduce(
  1 (max >= a) by Premise,
  2 (max >= b) by Premise,
  3 (max == a | max == b) by Premise, //LHS in if, RHS in else
)
//how can we assert that we've found the max?
assert(max >= a)
assert(max >= b)
assert(max == a | max == b)
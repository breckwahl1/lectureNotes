// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires( n >= 0 ), // precondition
    Ensures( Res[Z] == n * (n+1) )  
  )

  // any var initialized before the loop is not true inside the loop once it changes

  var sum: Z = 0 // return values
  var cur: Z = 0 // num of iterations, num of evens added so far

  // must prove invariant before loop begins
  Deduce(
    1 ( sum == 0 ) by Premise, 
    2 ( cur == 0 ) by Premise,
    3 ( sum == cur * (cur + 1) ) by Algebra*(1,2), // proves invariant before loop begins
  )

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur, sum),
      sum == cur * (cur + 1), // invariant
    )

    cur = cur + 1
    Deduce(
      1 ( cur == Old(cur) + 1 ) by Premise,
      2 ( Old(cur) != n ) by Premise,
      3 ( Old(cur) == cur - 1 ) by Algebra*(1),
      4 ( sum == Old(cur) * (Old(cur) + 1)) by Premise, 
      5 ( sum == (cur - 1) * ((cur - 1) + 1)) by Algebra*(3,4),
    )
    sum = sum + 2*cur

    // prove invariant still holds when loop ends
    Deduce(
      1 ( Old(sum) == (cur - 1) * ((cur - 1) + 1)) by Premise,
      2 ( sum == Old(sum) + 2 * cur ) by Premise,
      3 ( sum == ((cur - 1) * ((cur - 1) + 1)) + 2 * cur ) by Algebra*(1,2),
      4 ( sum == (cur - 1) * cur + 2 * cur ) by Algebra*(3),
      5 ( sum == cur * cur - cur + 2 * cur ) by Algebra*(4),
      6 ( sum == cur * cur + cur ) by Algebra*(5),
      7 ( sum == cur * (cur + 1) ) by Algebra*(6),
      // goal is the invariant
    )
  }
  // need to prove post condition before return statement
  Deduce(
    1 ( !(cur != n) ) by Premise, // condition is false
    2 ( cur == n ) by Algebra*(1), 
    3 ( sum == cur * (cur + 1) ) by Premise, // invariant is true
    4 ( sum == n * (n+1)) by Algebra*(2,3),
    // need sum == n*(n + 1)
  )
  return sum
}

//////////// test code /////////

val num: Z = 5

Deduce(
  1 ( num == 5 ) by Premise,
  2 ( num >= 0 ) by Algebra*(1), // needed to prove precondition
)

var sum5evens: Z = sumEvens(num) // do not write the function call in the proofs
Deduce(
  1 ( sum5evens == num * (num+1)) by Premise, // copying ensures.
  2 ( num == 5 ) by Premise,
  3 ( sum5evens == 30 ) by Algebra*(1,2),
)

//sum of first 5 evens: ?
assert(sum5evens == 30)
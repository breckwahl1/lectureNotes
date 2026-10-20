// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,

<<<<<<< HEAD
      // let subproof with for all introduction
      4 Let ((a: T) => SubProof(
        // implyI to build
        5 SubProof (
          6 Assume ( P(a) | Q(a) ),

          // start negI to build !R
          7 SubProof(
            8 Assume ( R(a) ),

            // use premises, plug a into them
=======
      4 Let ((a: T) => SubProof(
        //now start ImplyI to build P(a) | Q(a) __>: !R(a) 
        5 SubProof(
          6 Assume(P(a) | Q(a)),

          //now start NegI subproof to build !R(a)
          7 SubProof(
            8 Assume(R(a)),
            
            //plug a into our premises
>>>>>>> 4ce80d43cd9c4f4e543aa4a4bcd7201c34c5fece
            9 ( P(a) __>: B(a) ) by AllE[T](1),
            10 ( Q(a) __>: C(a) ) by AllE[T](2),
            11 ( R(a) __>: !B(a) & !C(a) ) by AllE[T](3),

            12 ( !B(a) & !C(a) ) by ImplyE(11, 8),
<<<<<<< HEAD

            13 ( !B(a) ) by AndE1(12),
            14 ( !C(a) ) by AndE2(12),

            // try OrE with ( P(a) | Q(a) )
            15 SubProof(
              16 Assume ( P(a) ), 
              17 ( B(a) ) by ImplyE(9,16),
              18 ( F ) by NegE(17,13),
              // goal: contradiction (F)
            ),
            19 SubProof(
              20 Assume ( Q(a) ),
              21 ( C(a) ) by ImplyE(10,20),
              22 ( F ) by NegE(21, 14),
              // goal: F
            ),
            23 ( F ) by OrE(6, 15, 19),
            // goal: F
          ),
          24 ( !R(a) ) by NegI(7), 
          // goal: !R(a)
        ),
        25 ( P(a) | Q(a) __>: !R(a) ) by ImplyI(5),
          // P(a) | Q(a) __>: !R(a) 
      )),
      26 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x)  )) ) by AllI[T](4),
      // goal: ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
=======
            13 ( !B(a) ) by AndE1(12),
            14 ( !C(a) ) by AndE2(12),

            //try OrE with P(a) | Q(a)
            15 SubProof(
              16 Assume( P(a) ),
              17 ( B(a) ) by ImplyE(9, 16),
              18 ( F ) by NegE(17, 13)

              //goal: F
            ),
            19 SubProof(
              20 Assume( Q(a) ),
              21 ( C(a) ) by ImplyE(10, 20),
              22 ( F ) by NegE(21, 14)
              //goal: F
            ),
            23 ( F ) by OrE(6, 15, 19)

            //goal: F
          ),
          24 ( !R(a) ) by NegI(7)

          //goal: !R(a) 
        ),
        25 ( P(a) | Q(a) __>: !R(a) ) by ImplyI(5)

        //need: P(a) | Q(a) __>: !R(a) 
        //my goal for all for my named individual
      )),
      26 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x)  )) ) by AllI[T](4)
      //goal: ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))

      //goal: create the conclusion which is a for all
      //use for all introduction
>>>>>>> 4ce80d43cd9c4f4e543aa4a4bcd7201c34c5fece
    )
  )
}
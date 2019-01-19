////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_cache_lru_marocchino                                       //
//                                                                    //
//  Description: Cache LRU computation                                //
//               Derived from mor1kx_cache_lru                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Stefan Wallentowitz                           //
//                      stefan.wallentowitz@tum.de                    //
//                                                                    //
//   Copyright (C) 2018 Andrey Bacherov                               //
//                      avbacherov@opencores.org                      //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// This is the least-recently-used (LRU) calculation module. It
// essentially has two types of input and output. First, the history
// information needs to be evaluated to calculate the LRU value.
// Second, the current access and the LRU are one hot values of the
// ways.
//
// This module is pure combinational. All registering is done outside
// this module. The following parameter exists:
//
//  * NUMWAYS: Number of ways (must be greater than 1)
//
// The following ports exist:
//
//  * current: The current LRU history
//  * update: The new LRU history after access
//
//  * access: 0 if no access or one-hot of the way that accesses
//  * lru_pre: LRU before the access (one hot of ways)
//  * lru_post: LRU after the access (one hot of ways)
//
// The latter three have the width of NUMWAYS apparently. The first
// three are more complicated as this is an optimized way of storing
// the history information, which will be shortly described in the
// following.
//
// A naive approach to store the history of the access is to store the
// relative "age" of each element in a vector, for example for four
// ways:
//
//   0: 1 1: 3 2: 1 3:0
//
// This needs 4x2 bits, but more important it also needs a set of
// comparators and adders. This can become increasingly complex when
// using a higher number of cache ways with an impact on area and
// timing.
//
// Similarly, it is possible to store a "stack" of the access and
// reorder this stack on an access. But the problems are similar, it
// needs comparators etc.
//
// A neat approach is to store the history efficiently coded, while
// also easing the calculation. This approach stores the information
// whether each entry is older than the others. For example for the
// four-way example (x<y means x is older than y):
//
// |0<1|0<2|0<3|1<0|1<2|1<3|2<0|2<1|2<3|3<0|3<1|3<2|
//
// This is redundant as two entries can never be equally old meaning
// x<y == !y<x, leading to a simpler version
//
// |0<1|0<2|0<3|1<2|1<3|2<3|
//
// The calculations on this vector are much simpler and it is
// therefore used by this module.
//
// The width of this vector is the triangular number of (NUMWAYS-1),
// specifically:
//  WIDTH=NUMWAYS*(NUMWAYS-1)/2.
//
// The details of the algorithms are described below. The designer
// just needs to apply current history vector and the access and gets
// the updated history and the LRU before and after the access.
//
// Instantiation example:
// mor1kx_cache_lru_marocchino
//  (.NUMWAYS(4))
// u_lru(.current  (current_history[((NUMWAYS*(NUMWAYS-1))>>1)-1:0])),
//       .access   (access[NUMWAYS-1:0]),
//       .update   (updated_history[((NUMWAYS*(NUMWAYS-1))>>1)-1:0])),
//       .lru_post (lru_post[NUMWAYS-1:0]));


module mor1kx_cache_lru_marocchino
#(
  parameter NUMWAYS = 2
)
(
  // Inputs
  input      [((NUMWAYS*(NUMWAYS-1)>>1)-1):0] current,
  input                       [(NUMWAYS-1):0] access,
  // Outputs
  output reg [((NUMWAYS*(NUMWAYS-1)>>1)-1):0] update,
  output                      [(NUMWAYS-1):0] lru_post
);

  reg [NUMWAYS-1:0] expand [NUMWAYS-1:0];

  //
  // <    0      1      2      3
  // 0    1    (0<1)  (0<2)  (0<3)
  // 1  (1<0)    1    (1<2)  (1<3)
  // 2  (2<0)  (2<1)    1    (2<3)
  // 3  (3<0)  (3<1)  (3<2)    1
  //
  // As two entries can never be equally old (needs to be avoided on
  // the outside) this is equivalent to:
  //
  // <    0      1      2      3
  // 0    1    (0<1)  (0<2)  (0<3)
  // 1 !(0<1)    1    (1<2)  (1<3)
  // 2 !(0<2) !(1<2)    1    (2<3)
  // 3 !(0<3) !(1<3) !(2<3)    1
  //
  // The lower half below the diagonal is the inverted mirror of the
  // upper half. The number of entries in each half is of course
  // equal to the width of our LRU vector and the upper half is
  // filled with the values from the vector.
  //
  // The algorithm works as follows:
  //
  //  1. Fill the matrix (expand) with the values. The entry (i,i) is
  //     statically one.
  //
  //  2. The LRU_pre vector is the vector of the ANDs of the each row.
  //
  //  3. Update the values with the access vector (if any) in the
  //     following way: If access[i] is set, the values in row i are
  //     set to 0. Similarly, the values in column i are set to 1.
  //
  //  4. The update vector of the lru history is then generated by
  //     copying the upper half of the matrix back.
  //
  //  5. The LRU_post vector is the vector of the ANDs of each row.


  // Updated history
  // (upper half of age relation matrix "expand")
  integer i1, j1, off1;
  // The off1 (offset) is used to transfer the
  // flat history vector into the upper half of the
  // age relation matrix (expand).
  always @(access or current) begin: updhist
    off1 = 0;
    for (i1 = 0; i1 < NUMWAYS; i1 = i1 + 1) begin
      for (j1 = i1 + 1; j1 < NUMWAYS; j1 = j1 + 1) begin
        // If access[i] is set, the values in row i are set to 0.
        // Similarly, the values in column i are set to 1.
        update[off1+j1-i1-1] = access[i1] ? 1'b0 : (access[j1] ? 1'b1 : current[off1+j1-i1-1]);
      end
      // new offset
      off1 = off1 + NUMWAYS - i1 - 1;
    end
  end // updhist


  // Create age relation matrix
  integer i2, j2, off2;
  // Upper half of the matrix is updated history.
  // Lower half of the matrix is just opposit to upper one.
  always @(update) begin: agematrix
    off2 = 0;
    for (i2 = 0; i2 < NUMWAYS; i2 = i2 + 1) begin
      // Diagonal entries are statically one.
      expand[i2][i2] = 1'b1;
      // Non-diagonal entries
      for (j2 = i2 + 1; j2 < NUMWAYS; j2 = j2 + 1) begin
        expand[i2][j2] =   update[off2+j2-i2-1];
        expand[j2][i2] = (~update[off2+j2-i2-1]);
      end
      // new off2
      off2 = off2 + NUMWAYS - i2 - 1;
    end
  end // agematrix


  // The LRU_post vector is the vector of the ANDs of each row.
  generate
  genvar i;
  for (i = 0; i < NUMWAYS; i = i + 1) begin: lru_res
    assign lru_post[i] = &expand[i];
  end
  endgenerate

endmodule // mor1kx_cache_lru_marocchino

module {
  func.func @vector_rescale(%arg0: memref<1000xi32>, %arg1: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.muli %3, %arg1 : i32
    %5 = arith.extui %0 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    memref.store %4, %arg0[%6] {handshake.name = "store1"} : memref<1000xi32>
    %7 = arith.addi %0, %c1_i32 : i32
    %8 = arith.cmpi ne, %7, %c1000_i32 : i32
    cf.cond_br %8, ^bb1(%7 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}

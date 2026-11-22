module {
  func.func @mul_example(%arg0: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c100_i32 = arith.constant 100 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<100xi32>
    %4 = arith.muli %3, %3 : i32
    %5 = arith.muli %4, %3 : i32
    %6 = arith.extui %0 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    memref.store %5, %arg0[%7] {handshake.name = "store1"} : memref<100xi32>
    %8 = arith.addi %0, %c1_i32 : i32
    %9 = arith.cmpi ult, %8, %c100_i32 : i32
    cf.cond_br %9, ^bb1(%8 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    return
  }
}

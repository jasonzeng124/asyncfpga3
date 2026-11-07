module {
  func.func @fir(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c999_i32 = arith.constant 999 : i32
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg1[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.subi %c999_i32, %0 : i32
    %6 = arith.extui %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load1"} : memref<1000xi32>
    %9 = arith.muli %4, %8 : i32
    %10 = arith.addi %1, %9 : i32
    %11 = arith.addi %0, %c1_i32 : i32
    %12 = arith.cmpi ult, %11, %c1000_i32 : i32
    cf.cond_br %12, ^bb1(%11, %10 : i32, i32), ^bb2(%10 : i32)
  ^bb2(%13: i32):  // pred: ^bb1
    return %13 : i32
  }
}

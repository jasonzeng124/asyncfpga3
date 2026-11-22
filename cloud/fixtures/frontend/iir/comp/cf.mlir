module {
  func.func @iir(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: i32, %arg3: i32) -> i32 {
    %c1_i32 = arith.constant 1 : i32
    %c1000_i32 = arith.constant 1000 : i32
    %c0 = arith.constant 0 : index
    %0 = memref.load %arg0[%c0] {handshake.name = "load0"} : memref<1000xi32>
    cf.br ^bb1(%c1_i32, %0 : i32, i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.muli %2, %arg2 : i32
    %4 = arith.extui %1 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.muli %6, %arg3 : i32
    %8 = arith.addi %3, %7 : i32
    %9 = arith.extui %1 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    memref.store %8, %arg0[%10] {handshake.name = "store2"} : memref<1000xi32>
    %11 = arith.addi %1, %c1_i32 : i32
    %12 = arith.cmpi ult, %11, %c1000_i32 : i32
    cf.cond_br %12, ^bb1(%11, %8 : i32, i32), ^bb2(%8 : i32)
  ^bb2(%13: i32):  // pred: ^bb1
    return %13 : i32
  }
}

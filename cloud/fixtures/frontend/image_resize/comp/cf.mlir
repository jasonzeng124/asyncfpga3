module {
  func.func @image_resize(%arg0: memref<900xi32>, %arg1: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c30_i32 = arith.constant 30 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb2
    %4 = arith.extui %3 : i32 to i64
    %c30_i64 = arith.constant 30 : i64
    %5 = arith.muli %1, %c30_i64 : i64
    %6 = arith.addi %5, %4 : i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load0"} : memref<900xi32>
    %9 = arith.subi %arg1, %8 : i32
    %10 = arith.extui %3 : i32 to i64
    %c30_i64_0 = arith.constant 30 : i64
    %11 = arith.muli %2, %c30_i64_0 : i64
    %12 = arith.addi %11, %10 : i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %9, %arg0[%13] {handshake.name = "store1"} : memref<900xi32>
    %14 = arith.addi %3, %c1_i32 : i32
    %15 = arith.cmpi ult, %14, %c30_i32 : i32
    cf.cond_br %15, ^bb2(%14 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %16 = arith.addi %0, %c1_i32 : i32
    %17 = arith.cmpi ult, %16, %c30_i32 : i32
    cf.cond_br %17, ^bb1(%16 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}

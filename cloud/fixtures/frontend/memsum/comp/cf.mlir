module {
  func.func @memsum(%arg0: memref<32xi32>, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c32_i32 = arith.constant 32 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.extui %1 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<32xi32>
    %6 = arith.addi %1, %c1_i32 : i32
    %7 = arith.muli %5, %6 : i32
    %8 = arith.addi %2, %7 : i32
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.cmpi slt, %9, %arg1 : i32
    %11 = arith.cmpi ult, %9, %c32_i32 : i32
    %12 = arith.andi %10, %11 : i1
    cf.cond_br %12, ^bb1(%9, %8 : i32, i32), ^bb2(%8 : i32)
  ^bb2(%13: i32):  // 2 preds: ^bb0, ^bb1
    return %13 : i32
  }
}

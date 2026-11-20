module {
  func.func @memsum(%arg0: memref<32xi32>, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c31_i32 = arith.constant 31 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1, ^bb3(%c0_i32 : i32)
  ^bb1:  // pred: ^bb0
    %1 = arith.addi %arg1, %c-1_i32 : i32
    %2 = arith.minui %1, %c31_i32 : i32
    %3 = arith.addi %2, %c1_i32 : i32
    cf.br ^bb2(%c0_i32, %c0_i32 : i32, i32)
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.extui %4 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load0"} : memref<32xi32>
    %9 = arith.addi %4, %c1_i32 : i32
    %10 = arith.muli %8, %9 : i32
    %11 = arith.addi %5, %10 : i32
    %12 = arith.addi %4, %c1_i32 : i32
    %13 = arith.cmpi ne, %12, %3 : i32
    cf.cond_br %13, ^bb2(%12, %11 : i32, i32), ^bb3(%11 : i32)
  ^bb3(%14: i32):  // 2 preds: ^bb0, ^bb2
    return %14 : i32
  }
}

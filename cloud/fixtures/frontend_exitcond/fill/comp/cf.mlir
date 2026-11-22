module {
  func.func @fill(%arg0: memref<32xi32>, %arg1: i32, %arg2: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c3_i32 = arith.constant 3 : i32
    %c5_i32 = arith.constant 5 : i32
    %c7_i32 = arith.constant 7 : i32
    %c31_i32 = arith.constant 31 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c3_i32, %arg2, %c0_i32 : i32, i32, i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32, %3: i32, %4: i32):  // 2 preds: ^bb0, ^bb1
    %5 = arith.shli %3, %c5_i32 : i32
    %6 = arith.xori %3, %5 : i32
    %7 = arith.addi %6, %1 : i32
    %8 = arith.extui %2 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    memref.store %7, %arg0[%9] {handshake.name = "store0"} : memref<32xi32>
    %10 = arith.addi %2, %c7_i32 : i32
    %11 = arith.andi %10, %c31_i32 : i32
    %12 = arith.shrsi %7, %c3_i32 : i32
    %13 = arith.addi %4, %12 : i32
    %14 = arith.addi %1, %c1_i32 : i32
    %15 = arith.cmpi ne, %14, %arg1 : i32
    cf.cond_br %15, ^bb1(%14, %11, %7, %13 : i32, i32, i32, i32), ^bb2(%13 : i32)
  ^bb2(%16: i32):  // 2 preds: ^bb0, ^bb1
    return %16 : i32
  }
}

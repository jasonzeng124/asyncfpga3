module {
  func.func @dot2(%arg0: memref<32xi32>, %arg1: memref<32xi32>, %arg2: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c31_i32 = arith.constant 31 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg2 : i32
    cf.cond_br %0, ^bb1, ^bb3(%c0_i32 : i32)
  ^bb1:  // pred: ^bb0
    %1 = arith.addi %arg2, %c-1_i32 : i32
    %2 = arith.minui %1, %c31_i32 : i32
    %3 = arith.addi %2, %c1_i32 : i32
    cf.br ^bb2(%c0_i32, %c0_i32 : i32, i32)
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.extui %4 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load0"} : memref<32xi32>
    %9 = arith.extui %4 : i32 to i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg1[%10] {handshake.name = "load1"} : memref<32xi32>
    %12 = arith.muli %8, %11 : i32
    %13 = arith.addi %5, %12 : i32
    %14 = arith.addi %4, %c1_i32 : i32
    %15 = arith.cmpi ne, %14, %3 : i32
    cf.cond_br %15, ^bb2(%14, %13 : i32, i32), ^bb3(%13 : i32)
  ^bb3(%16: i32):  // 2 preds: ^bb0, ^bb2
    return %16 : i32
  }
}

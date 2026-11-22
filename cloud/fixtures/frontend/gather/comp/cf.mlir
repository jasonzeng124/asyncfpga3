module {
  func.func @gather(%arg0: memref<32xi32>, %arg1: memref<32xi32>, %arg2: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c32_i32 = arith.constant 32 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg2 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.extui %1 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg1[%4] {handshake.name = "load0"} : memref<32xi32>
    %6 = arith.extsi %5 : i32 to i64
    %7 = arith.index_cast %6 : i64 to index
    %8 = memref.load %arg0[%7] {handshake.name = "load1"} : memref<32xi32>
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.muli %8, %9 : i32
    %11 = arith.addi %2, %10 : i32
    %12 = arith.addi %1, %c1_i32 : i32
    %13 = arith.cmpi slt, %12, %arg2 : i32
    %14 = arith.cmpi ult, %12, %c32_i32 : i32
    %15 = arith.andi %13, %14 : i1
    cf.cond_br %15, ^bb1(%12, %11 : i32, i32), ^bb2(%11 : i32)
  ^bb2(%16: i32):  // 2 preds: ^bb0, ^bb1
    return %16 : i32
  }
}

module {
  func.func @if_loop_2(%arg0: memref<100xi32>, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c10_i32 = arith.constant 10 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.extui %1 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<100xi32>
    %6 = arith.cmpi sgt, %5, %c10_i32 : i32
    %7 = arith.addi %2, %5 : i32
    %8 = arith.select %6, %7, %2 : i32
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.cmpi slt, %9, %arg1 : i32
    cf.cond_br %10, ^bb1(%9, %8 : i32, i32), ^bb2(%8 : i32)
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return %11 : i32
  }
}

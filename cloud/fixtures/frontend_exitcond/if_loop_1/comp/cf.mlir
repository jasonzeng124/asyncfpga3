module {
  func.func @if_loop_1(%arg0: memref<100xi32>, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c2_i32 = arith.constant 2 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.extui %1 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<100xi32>
    %6 = arith.cmpi sgt, %5, %c2_i32 : i32
    %7 = arith.muli %5, %c5_i32 : i32
    %8 = arith.addi %2, %7 : i32
    %9 = arith.select %6, %8, %2 : i32
    %10 = arith.addi %1, %c1_i32 : i32
    %11 = arith.cmpi ne, %10, %arg1 : i32
    cf.cond_br %11, ^bb1(%10, %9 : i32, i32), ^bb2(%9 : i32)
  ^bb2(%12: i32):  // 2 preds: ^bb0, ^bb1
    return %12 : i32
  }
}

module {
  func.func @collatz64(%arg0: i64) -> i32 {
    %c1_i64 = arith.constant 1 : i64
    %c0_i32 = arith.constant 0 : i32
    %c0_i64 = arith.constant 0 : i64
    %c3_i64 = arith.constant 3 : i64
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi eq, %arg0, %c1_i64 : i64
    cf.cond_br %0, ^bb2(%c0_i32 : i32), ^bb1(%arg0, %c0_i32 : i64, i32)
  ^bb1(%1: i64, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.andi %1, %c1_i64 : i64
    %4 = arith.cmpi eq, %3, %c0_i64 : i64
    %5 = arith.shrsi %1, %c1_i64 : i64
    %6 = arith.muli %1, %c3_i64 : i64
    %7 = arith.addi %6, %c1_i64 : i64
    %8 = arith.select %4, %5, %7 : i64
    %9 = arith.addi %2, %c1_i32 : i32
    %10 = arith.cmpi eq, %8, %c1_i64 : i64
    cf.cond_br %10, ^bb2(%9 : i32), ^bb1(%8, %9 : i64, i32)
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return %11 : i32
  }
}

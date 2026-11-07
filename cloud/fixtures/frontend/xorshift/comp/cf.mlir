module {
  func.func @xorshift(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c13_i32 = arith.constant 13 : i32
    %c17_i32 = arith.constant 17 : i32
    %c5_i32 = arith.constant 5 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %arg0 : i32, i32), ^bb2(%arg0 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.shli %2, %c13_i32 : i32
    %4 = arith.xori %2, %3 : i32
    %5 = arith.shrui %4, %c17_i32 : i32
    %6 = arith.xori %4, %5 : i32
    %7 = arith.shli %6, %c5_i32 : i32
    %8 = arith.xori %6, %7 : i32
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.cmpi slt, %9, %arg1 : i32
    cf.cond_br %10, ^bb1(%9, %8 : i32, i32), ^bb2(%8 : i32)
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return %11 : i32
  }
}

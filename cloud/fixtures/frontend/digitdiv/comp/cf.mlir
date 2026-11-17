module {
  func.func @digitdiv(%arg0: i32, %arg1: i32) -> i32 {
    %c2_i32 = arith.constant 2 : i32
    %c10_i32 = arith.constant 10 : i32
    %c0_i32 = arith.constant 0 : i32
    %0 = arith.cmpi ult, %arg1, %c2_i32 : i32
    %1 = arith.select %0, %c10_i32, %arg1 : i32
    %2 = arith.cmpi eq, %arg0, %c0_i32 : i32
    cf.cond_br %2, ^bb2(%c0_i32 : i32), ^bb1(%c0_i32, %arg0 : i32, i32)
  ^bb1(%3: i32, %4: i32):  // 2 preds: ^bb0, ^bb1
    %5 = arith.divui %4, %1 : i32
    %6 = arith.muli %5, %1 : i32
    %7 = arith.subi %4, %6 : i32
    %8 = arith.addi %3, %7 : i32
    %9 = arith.cmpi eq, %5, %c0_i32 : i32
    cf.cond_br %9, ^bb2(%8 : i32), ^bb1(%8, %5 : i32, i32)
  ^bb2(%10: i32):  // 2 preds: ^bb0, ^bb1
    return %10 : i32
  }
}

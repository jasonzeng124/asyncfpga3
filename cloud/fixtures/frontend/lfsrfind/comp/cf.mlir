module {
  func.func @lfsrfind(%arg0: i32, %arg1: i32) -> i32 {
    %c65535_i32 = arith.constant 65535 : i32
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c46080_i32 = arith.constant 46080 : i32
    %c256_i32 = arith.constant 256 : i32
    %0 = arith.andi %arg0, %c65535_i32 : i32
    %1 = arith.andi %arg1, %c65535_i32 : i32
    cf.br ^bb1(%c0_i32, %0 : i32, i32)
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb2
    %4 = arith.cmpi eq, %3, %1 : i32
    cf.cond_br %4, ^bb3(%2 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    %5 = arith.shrui %3, %c1_i32 : i32
    %6 = arith.andi %3, %c1_i32 : i32
    %7 = arith.cmpi eq, %6, %c0_i32 : i32
    %8 = arith.select %7, %c0_i32, %c46080_i32 : i32
    %9 = arith.xori %5, %8 : i32
    %10 = arith.addi %2, %c1_i32 : i32
    %11 = arith.cmpi ult, %10, %c256_i32 : i32
    cf.cond_br %11, ^bb1(%10, %9 : i32, i32), ^bb3(%c256_i32 : i32)
  ^bb3(%12: i32):  // 2 preds: ^bb1, ^bb2
    return %12 : i32
  }
}

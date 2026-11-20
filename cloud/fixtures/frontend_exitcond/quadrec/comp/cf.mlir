module {
  func.func @quadrec(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1013904242_i32 = arith.constant 1013904242 : i32
    %c1779033703_i32 = arith.constant 1779033703 : i32
    %c-1150833019_i32 = arith.constant -1150833019 : i32
    %c3_i32 = arith.constant 3 : i32
    %c1_i32 = arith.constant 1 : i32
    %c2_i32 = arith.constant 2 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1013904242_i32, %arg0, %c1779033703_i32, %c-1150833019_i32 : i32, i32, i32, i32, i32), ^bb2(%c-1150833019_i32, %c1779033703_i32, %arg0, %c1013904242_i32 : i32, i32, i32, i32)
  ^bb1(%1: i32, %2: i32, %3: i32, %4: i32, %5: i32):  // 2 preds: ^bb0, ^bb1
    %6 = arith.xori %4, %5 : i32
    %7 = arith.addi %3, %6 : i32
    %8 = arith.shrui %2, %c3_i32 : i32
    %9 = arith.addi %7, %8 : i32
    %10 = arith.addi %1, %c1_i32 : i32
    %11 = arith.cmpi ne, %10, %arg1 : i32
    cf.cond_br %11, ^bb1(%10, %9, %4, %5, %2 : i32, i32, i32, i32, i32), ^bb2(%2, %5, %4, %9 : i32, i32, i32, i32)
  ^bb2(%12: i32, %13: i32, %14: i32, %15: i32):  // 2 preds: ^bb0, ^bb1
    %16 = arith.shli %13, %c1_i32 : i32
    %17 = arith.shli %12, %c2_i32 : i32
    %18 = arith.xori %16, %17 : i32
    %19 = arith.shli %15, %c3_i32 : i32
    %20 = arith.xori %18, %19 : i32
    %21 = arith.xori %20, %14 : i32
    return %21 : i32
  }
}

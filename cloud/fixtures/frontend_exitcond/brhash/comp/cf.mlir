module {
  func.func @brhash(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-306674912_i32 = arith.constant -306674912 : i32
    %c17_i32 = arith.constant 17 : i32
    %c13_i32 = arith.constant 13 : i32
    %c9_i32 = arith.constant 9 : i32
    %c2_i32 = arith.constant 2 : i32
    %c5_i32 = arith.constant 5 : i32
    %c625341585_i32 = arith.constant 625341585 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %arg0 : i32, i32), ^bb5(%arg0 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb4
    %3 = arith.andi %2, %c1_i32 : i32
    %4 = arith.cmpi eq, %3, %c0_i32 : i32
    cf.cond_br %4, ^bb3, ^bb2
  ^bb2:  // pred: ^bb1
    %5 = arith.shrui %2, %c1_i32 : i32
    %6 = arith.xori %5, %c-306674912_i32 : i32
    %7 = arith.muli %6, %c17_i32 : i32
    %8 = arith.addi %7, %1 : i32
    %9 = arith.shrui %8, %c13_i32 : i32
    %10 = arith.xori %8, %9 : i32
    cf.br ^bb4(%10 : i32)
  ^bb3:  // pred: ^bb1
    %11 = arith.shli %2, %c9_i32 : i32
    %12 = arith.xori %2, %11 : i32
    %13 = arith.shrui %12, %c2_i32 : i32
    %14 = arith.shli %1, %c1_i32 : i32
    %15 = arith.addi %13, %14 : i32
    %16 = arith.shli %15, %c5_i32 : i32
    %17 = arith.xori %15, %16 : i32
    %18 = arith.xori %17, %c625341585_i32 : i32
    cf.br ^bb4(%18 : i32)
  ^bb4(%19: i32):  // 2 preds: ^bb2, ^bb3
    %20 = arith.addi %1, %c1_i32 : i32
    %21 = arith.cmpi ne, %20, %arg1 : i32
    cf.cond_br %21, ^bb1(%20, %19 : i32, i32), ^bb5(%19 : i32)
  ^bb5(%22: i32):  // 2 preds: ^bb0, ^bb4
    return %22 : i32
  }
}

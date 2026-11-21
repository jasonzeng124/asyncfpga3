module {
  func.func @nest3(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c74565_i32 = arith.constant 74565 : i32
    %c3_i32 = arith.constant 3 : i32
    %c5_i32 = arith.constant 5 : i32
    %c4_i32 = arith.constant 4 : i32
    %c2_i32 = arith.constant 2 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg0 : i32
    cf.cond_br %0, ^bb1(%c74565_i32, %c0_i32 : i32, i32), ^bb6(%c74565_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb5
    %3 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %3, ^bb2(%c0_i32, %1 : i32, i32), ^bb5(%1 : i32)
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb4
    %6 = arith.xori %2, %4 : i32
    %7 = arith.andi %6, %c3_i32 : i32
    %8 = arith.cmpi ult, %c0_i32, %7 : i32
    cf.cond_br %8, ^bb3(%c0_i32, %5 : i32, i32), ^bb4(%5 : i32)
  ^bb3(%9: i32, %10: i32):  // 2 preds: ^bb2, ^bb3
    %11 = arith.shrui %10, %c5_i32 : i32
    %12 = arith.xori %10, %11 : i32
    %13 = arith.shli %2, %c4_i32 : i32
    %14 = arith.shli %4, %c2_i32 : i32
    %15 = arith.xori %13, %14 : i32
    %16 = arith.xori %15, %9 : i32
    %17 = arith.addi %12, %16 : i32
    %18 = arith.addi %17, %c1_i32 : i32
    %19 = arith.addi %9, %c1_i32 : i32
    %20 = arith.cmpi ne, %19, %7 : i32
    cf.cond_br %20, ^bb3(%19, %18 : i32, i32), ^bb4(%18 : i32)
  ^bb4(%21: i32):  // 2 preds: ^bb2, ^bb3
    %22 = arith.addi %4, %c1_i32 : i32
    %23 = arith.cmpi ne, %22, %arg1 : i32
    cf.cond_br %23, ^bb2(%22, %21 : i32, i32), ^bb5(%21 : i32)
  ^bb5(%24: i32):  // 2 preds: ^bb1, ^bb4
    %25 = arith.addi %2, %c1_i32 : i32
    %26 = arith.cmpi ne, %25, %arg0 : i32
    cf.cond_br %26, ^bb1(%24, %25 : i32, i32), ^bb6(%24 : i32)
  ^bb6(%27: i32):  // 2 preds: ^bb0, ^bb5
    return %27 : i32
  }
}

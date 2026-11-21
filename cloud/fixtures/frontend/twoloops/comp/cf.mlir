module {
  func.func @twoloops(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c7_i32 = arith.constant 7 : i32
    %c1_i32 = arith.constant 1 : i32
    %c255_i32 = arith.constant 255 : i32
    %c3_i32 = arith.constant 3 : i32
    %c40503_i32 = arith.constant 40503 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%arg0, %c0_i32 : i32, i32), ^bb2(%arg0 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.shli %1, %c7_i32 : i32
    %4 = arith.xori %1, %3 : i32
    %5 = arith.addi %4, %2 : i32
    %6 = arith.addi %2, %c1_i32 : i32
    %7 = arith.cmpi slt, %6, %arg1 : i32
    cf.cond_br %7, ^bb1(%5, %6 : i32, i32), ^bb2(%5 : i32)
  ^bb2(%8: i32):  // 2 preds: ^bb0, ^bb1
    %9 = arith.andi %8, %c255_i32 : i32
    %10 = arith.cmpi ult, %c0_i32, %9 : i32
    cf.cond_br %10, ^bb3(%c0_i32, %8 : i32, i32), ^bb4(%8 : i32)
  ^bb3(%11: i32, %12: i32):  // 2 preds: ^bb2, ^bb3
    %13 = arith.shrui %12, %c3_i32 : i32
    %14 = arith.xori %12, %13 : i32
    %15 = arith.addi %14, %c40503_i32 : i32
    %16 = arith.addi %11, %c1_i32 : i32
    %17 = arith.cmpi ult, %16, %9 : i32
    cf.cond_br %17, ^bb3(%16, %15 : i32, i32), ^bb4(%15 : i32)
  ^bb4(%18: i32):  // 2 preds: ^bb2, ^bb3
    return %18 : i32
  }
}

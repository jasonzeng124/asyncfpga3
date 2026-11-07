module {
  func.func @isprime(%arg0: i32) -> i32 {
    %c2_i32 = arith.constant 2 : i32
    %c4_i32 = arith.constant 4 : i32
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %0 = arith.cmpi slt, %arg0, %c2_i32 : i32
    cf.cond_br %0, ^bb8(%c0_i32 : i32), ^bb1
  ^bb1:  // pred: ^bb0
    %1 = arith.cmpi sgt, %c4_i32, %arg0 : i32
    cf.cond_br %1, ^bb8(%c1_i32 : i32), ^bb3(%c2_i32 : i32)
  ^bb2(%2: i32):  // pred: ^bb7
    %3 = arith.muli %2, %2 : i32
    %4 = arith.cmpi sgt, %3, %arg0 : i32
    cf.cond_br %4, ^bb8(%c1_i32 : i32), ^bb3(%2 : i32)
  ^bb3(%5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.shrsi %arg0, %c1_i32 : i32
    cf.br ^bb4(%5 : i32)
  ^bb4(%7: i32):  // 2 preds: ^bb3, ^bb4
    %8 = arith.cmpi sgt, %7, %6 : i32
    %9 = arith.shli %7, %c1_i32 : i32
    cf.cond_br %8, ^bb5(%7 : i32), ^bb4(%9 : i32)
  ^bb5(%10: i32):  // pred: ^bb4
    %11 = arith.cmpi slt, %10, %5 : i32
    cf.cond_br %11, ^bb7(%arg0 : i32), ^bb6(%10, %arg0 : i32, i32)
  ^bb6(%12: i32, %13: i32):  // 2 preds: ^bb5, ^bb6
    %14 = arith.cmpi slt, %13, %12 : i32
    %15 = arith.subi %13, %12 : i32
    %16 = arith.select %14, %13, %15 : i32
    %17 = arith.shrsi %12, %c1_i32 : i32
    %18 = arith.cmpi slt, %17, %5 : i32
    cf.cond_br %18, ^bb7(%16 : i32), ^bb6(%17, %16 : i32, i32)
  ^bb7(%19: i32):  // 2 preds: ^bb5, ^bb6
    %20 = arith.cmpi eq, %19, %c0_i32 : i32
    %21 = arith.addi %5, %c1_i32 : i32
    cf.cond_br %20, ^bb8(%c0_i32 : i32), ^bb2(%21 : i32)
  ^bb8(%22: i32):  // 4 preds: ^bb0, ^bb1, ^bb2, ^bb7
    return %22 : i32
  }
}

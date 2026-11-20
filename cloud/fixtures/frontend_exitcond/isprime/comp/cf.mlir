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
  ^bb2:  // pred: ^bb7
    %2 = arith.muli %20, %20 : i32
    %3 = arith.cmpi sgt, %2, %arg0 : i32
    cf.cond_br %3, ^bb8(%c1_i32 : i32), ^bb3(%20 : i32)
  ^bb3(%4: i32):  // 2 preds: ^bb1, ^bb2
    %5 = arith.shrsi %arg0, %c1_i32 : i32
    cf.br ^bb4(%4 : i32)
  ^bb4(%6: i32):  // 2 preds: ^bb3, ^bb4
    %7 = arith.cmpi sgt, %6, %5 : i32
    %8 = arith.shli %6, %c1_i32 : i32
    cf.cond_br %7, ^bb5(%6 : i32), ^bb4(%8 : i32)
  ^bb5(%9: i32):  // pred: ^bb4
    %10 = arith.cmpi slt, %9, %4 : i32
    cf.cond_br %10, ^bb7(%arg0 : i32), ^bb6(%9, %arg0 : i32, i32)
  ^bb6(%11: i32, %12: i32):  // 2 preds: ^bb5, ^bb6
    %13 = arith.cmpi slt, %12, %11 : i32
    %14 = arith.subi %12, %11 : i32
    %15 = arith.select %13, %12, %14 : i32
    %16 = arith.shrsi %11, %c1_i32 : i32
    %17 = arith.cmpi slt, %16, %4 : i32
    cf.cond_br %17, ^bb7(%15 : i32), ^bb6(%16, %15 : i32, i32)
  ^bb7(%18: i32):  // 2 preds: ^bb5, ^bb6
    %19 = arith.cmpi eq, %18, %c0_i32 : i32
    %20 = arith.addi %4, %c1_i32 : i32
    cf.cond_br %19, ^bb8(%c0_i32 : i32), ^bb2
  ^bb8(%21: i32):  // 4 preds: ^bb0, ^bb1, ^bb2, ^bb7
    return %21 : i32
  }
}

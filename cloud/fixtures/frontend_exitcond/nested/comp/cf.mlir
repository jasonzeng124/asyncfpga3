module {
  func.func @nested(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c3_i32 = arith.constant 3 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg0 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1_i32 : i32, i32), ^bb4(%c1_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb3
    %3 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %3, ^bb2(%c0_i32, %2 : i32, i32), ^bb3(%2 : i32)
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %6 = arith.shli %5, %c3_i32 : i32
    %7 = arith.xori %5, %6 : i32
    %8 = arith.addi %7, %1 : i32
    %9 = arith.addi %8, %4 : i32
    %10 = arith.addi %4, %c1_i32 : i32
    %11 = arith.cmpi ne, %10, %arg1 : i32
    cf.cond_br %11, ^bb2(%10, %9 : i32, i32), ^bb3(%9 : i32)
  ^bb3(%12: i32):  // 2 preds: ^bb1, ^bb2
    %13 = arith.addi %1, %c1_i32 : i32
    %14 = arith.cmpi ne, %13, %arg0 : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb4(%12 : i32)
  ^bb4(%15: i32):  // 2 preds: ^bb0, ^bb3
    return %15 : i32
  }
}

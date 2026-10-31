module {
  func.func @ipow(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 : i32
    cf.cond_br %0, ^bb1(%arg0, %arg1, %c1_i32 : i32, i32, i32), ^bb2(%c1_i32 : i32)
  ^bb1(%1: i32, %2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %4 = arith.andi %2, %c1_i32 : i32
    %5 = arith.cmpi eq, %4, %c0_i32 : i32
    %6 = arith.muli %3, %1 : i32
    %7 = arith.select %5, %3, %6 : i32
    %8 = arith.muli %1, %1 : i32
    %9 = arith.shrsi %2, %c1_i32 : i32
    %10 = arith.cmpi sgt, %9, %c0_i32 : i32
    cf.cond_br %10, ^bb1(%8, %9, %7 : i32, i32, i32), ^bb2(%7 : i32)
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return %11 : i32
  }
}

module {
  func.func @horner(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c90_i32 = arith.constant 90 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.muli %2, %arg0 : i32
    %4 = arith.xori %1, %c90_i32 : i32
    %5 = arith.addi %3, %4 : i32
    %6 = arith.addi %1, %c1_i32 : i32
    %7 = arith.cmpi ne, %6, %arg1 : i32
    cf.cond_br %7, ^bb1(%6, %5 : i32, i32), ^bb2(%5 : i32)
  ^bb2(%8: i32):  // 2 preds: ^bb0, ^bb1
    return %8 : i32
  }
}

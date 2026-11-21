module {
  func.func @countloop(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg1 : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %3 = arith.addi %2, %1 : i32
    %4 = arith.xori %3, %arg0 : i32
    %5 = arith.addi %1, %c1_i32 : i32
    %6 = arith.cmpi slt, %5, %arg1 : i32
    cf.cond_br %6, ^bb1(%5, %4 : i32, i32), ^bb2(%4 : i32)
  ^bb2(%7: i32):  // 2 preds: ^bb0, ^bb1
    return %7 : i32
  }
}

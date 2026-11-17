module {
  func.func @sqrtsub(%arg0: i32) -> i32 {
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c2_i32 = arith.constant 2 : i32
    %0 = arith.cmpi slt, %arg0, %c1_i32 : i32
    cf.cond_br %0, ^bb2(%c0_i32 : i32), ^bb1(%arg0, %c0_i32, %c1_i32 : i32, i32, i32)
  ^bb1(%1: i32, %2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %4 = arith.subi %1, %3 : i32
    %5 = arith.addi %3, %c2_i32 : i32
    %6 = arith.addi %2, %c1_i32 : i32
    %7 = arith.cmpi slt, %4, %5 : i32
    cf.cond_br %7, ^bb2(%6 : i32), ^bb1(%4, %6, %5 : i32, i32, i32)
  ^bb2(%8: i32):  // 2 preds: ^bb0, ^bb1
    return %8 : i32
  }
}

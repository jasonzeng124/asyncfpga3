module {
  func.func @iterative_division(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c-1_i32 = arith.constant -1 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi eq, %arg1, %c0_i32 : i32
    cf.cond_br %0, ^bb4(%c-1_i32 : i32), ^bb1
  ^bb1:  // pred: ^bb0
    %1 = arith.cmpi sgt, %arg0, %c-1_i32 : i32
    %2 = arith.subi %c0_i32, %arg0 : i32
    %3 = arith.select %1, %arg0, %2 : i32
    %4 = arith.cmpi sgt, %arg1, %c-1_i32 : i32
    %5 = arith.subi %c0_i32, %arg1 : i32
    %6 = arith.select %4, %arg1, %5 : i32
    %7 = arith.cmpi slt, %3, %6 : i32
    cf.cond_br %7, ^bb3(%c0_i32 : i32), ^bb2(%3, %c0_i32 : i32, i32)
  ^bb2(%8: i32, %9: i32):  // 2 preds: ^bb1, ^bb2
    %10 = arith.subi %8, %6 : i32
    %11 = arith.addi %9, %c1_i32 : i32
    %12 = arith.cmpi slt, %10, %6 : i32
    cf.cond_br %12, ^bb3(%11 : i32), ^bb2(%10, %11 : i32, i32)
  ^bb3(%13: i32):  // 2 preds: ^bb1, ^bb2
    %14 = arith.xori %arg0, %arg1 : i32
    %15 = arith.cmpi slt, %14, %c0_i32 : i32
    %16 = arith.subi %c0_i32, %13 : i32
    %17 = arith.select %15, %16, %13 : i32
    cf.br ^bb4(%17 : i32)
  ^bb4(%18: i32):  // 2 preds: ^bb0, ^bb3
    return %18 : i32
  }
}

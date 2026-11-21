module {
  func.func @iterative_sqrt(%arg0: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %0 = arith.cmpi sgt, %c0_i32, %arg0 : i32
    cf.cond_br %0, ^bb3(%arg0 : i32), ^bb1(%arg0, %c0_i32 : i32, i32)
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb2
    %3 = arith.addi %2, %1 : i32
    %4 = arith.shrsi %3, %c1_i32 : i32
    %5 = arith.muli %4, %4 : i32
    %6 = arith.cmpi eq, %5, %arg0 : i32
    cf.cond_br %6, ^bb3(%4 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    %7 = arith.muli %4, %4 : i32
    %8 = arith.cmpi slt, %7, %arg0 : i32
    %9 = arith.addi %4, %c1_i32 : i32
    %10 = arith.addi %4, %c-1_i32 : i32
    %11 = arith.select %8, %9, %2 : i32
    %12 = arith.select %8, %1, %10 : i32
    %13 = arith.cmpi sgt, %11, %12 : i32
    cf.cond_br %13, ^bb3(%12 : i32), ^bb1(%12, %11 : i32, i32)
  ^bb3(%14: i32):  // 3 preds: ^bb0, ^bb1, ^bb2
    return %14 : i32
  }
}

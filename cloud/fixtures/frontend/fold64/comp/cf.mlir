module {
  func.func @fold64(%arg0: i64) -> i32 {
    %c255_i32 = arith.constant 255 : i32
    %c0_i32 = arith.constant 0 : i32
    %c81985529216486895_i64 = arith.constant 81985529216486895 : i64
    %c7_i64 = arith.constant 7 : i64
    %c3_i64 = arith.constant 3 : i64
    %c11_i64 = arith.constant 11 : i64
    %c1_i32 = arith.constant 1 : i32
    %c32_i64 = arith.constant 32 : i64
    %0 = arith.trunci %arg0 : i64 to i32
    %1 = arith.andi %0, %c255_i32 : i32
    %2 = arith.cmpi ult, %c0_i32, %1 : i32
    cf.cond_br %2, ^bb1(%c0_i32, %arg0, %c81985529216486895_i64 : i32, i64, i64), ^bb2(%c81985529216486895_i64 : i64)
  ^bb1(%3: i32, %4: i64, %5: i64):  // 2 preds: ^bb0, ^bb1
    %6 = arith.shli %5, %c7_i64 : i64
    %7 = arith.xori %4, %6 : i64
    %8 = arith.addi %5, %7 : i64
    %9 = arith.cmpi ult, %8, %4 : i64
    %10 = arith.shrui %4, %c3_i64 : i64
    %11 = arith.addi %8, %10 : i64
    %12 = arith.select %9, %11, %8 : i64
    %13 = arith.shrui %4, %c11_i64 : i64
    %14 = arith.xori %4, %13 : i64
    %15 = arith.addi %3, %c1_i32 : i32
    %16 = arith.cmpi ult, %15, %1 : i32
    cf.cond_br %16, ^bb1(%15, %14, %12 : i32, i64, i64), ^bb2(%12 : i64)
  ^bb2(%17: i64):  // 2 preds: ^bb0, ^bb1
    %18 = arith.shrui %17, %c32_i64 : i64
    %19 = arith.xori %17, %18 : i64
    %20 = arith.trunci %19 : i64 to i32
    return %20 : i32
  }
}

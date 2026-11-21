module {
  func.func @cmpchain(%arg0: i32, %arg1: i32) -> i32 {
    %c-1_i32 = arith.constant -1 : i32
    %c999999_i32 = arith.constant 999999 : i32
    %c256_i32 = arith.constant 256 : i32
    %c1610612736_i32 = arith.constant 1610612736 : i32
    %c1879048192_i32 = arith.constant 1879048192 : i32
    %c1342177280_i32 = arith.constant 1342177280 : i32
    %c268435456_i32 = arith.constant 268435456 : i32
    %c536870912_i32 = arith.constant 536870912 : i32
    %c805306368_i32 = arith.constant 805306368 : i32
    %c1073741824_i32 = arith.constant 1073741824 : i32
    %0 = arith.cmpi eq, %arg0, %arg1 : i32
    cf.cond_br %0, ^bb5(%c268435456_i32 : i32), ^bb1
  ^bb1:  // pred: ^bb0
    %1 = arith.andi %arg0, %arg1 : i32
    %2 = arith.cmpi sgt, %1, %c-1_i32 : i32
    cf.cond_br %2, ^bb2, ^bb5(%c536870912_i32 : i32)
  ^bb2:  // pred: ^bb1
    %3 = arith.cmpi slt, %arg0, %arg1 : i32
    cf.cond_br %3, ^bb5(%c805306368_i32 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %4 = arith.cmpi ugt, %arg0, %arg1 : i32
    cf.cond_br %4, ^bb5(%c1073741824_i32 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    %5 = arith.cmpi sgt, %arg0, %c999999_i32 : i32
    %6 = arith.cmpi ult, %arg0, %c256_i32 : i32
    %7 = arith.select %6, %c1610612736_i32, %c1879048192_i32 : i32
    %8 = arith.select %5, %c1342177280_i32, %7 : i32
    cf.br ^bb5(%8 : i32)
  ^bb5(%9: i32):  // 5 preds: ^bb0, ^bb1, ^bb2, ^bb3, ^bb4
    %10 = arith.subi %arg0, %arg1 : i32
    %11 = arith.xori %9, %10 : i32
    return %11 : i32
  }
}

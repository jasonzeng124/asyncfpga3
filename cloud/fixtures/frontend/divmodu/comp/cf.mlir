module {
  func.func @divmodu(%arg0: i32, %arg1: i32) -> i32 {
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.divui %arg0, %arg1 : i32
    %1 = arith.muli %0, %arg1 : i32
    %2 = arith.subi %arg0, %1 : i32
    %3 = arith.shli %2, %c1_i32 : i32
    %4 = arith.addi %0, %3 : i32
    return %4 : i32
  }
}

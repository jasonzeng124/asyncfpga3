module {
  func.func @divmods(%arg0: i32, %arg1: i32) -> i32 {
    %0 = arith.divsi %arg0, %arg1 : i32
    %1 = arith.remsi %arg0, %arg1 : i32
    %2 = arith.xori %0, %1 : i32
    return %2 : i32
  }
}

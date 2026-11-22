module {
  func.func @test_divui(%arg0: i32) -> i32 {
    %c1083_i32 = arith.constant 1083 : i32
    %0 = arith.divui %arg0, %c1083_i32 : i32
    return %0 : i32
  }
}

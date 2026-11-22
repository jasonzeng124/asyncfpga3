module {
  func.func @test_divui(%arg0: i32 {handshake.arg_name = "var1"}) -> i32 {
    %c1083_i32 = arith.constant {handshake.name = "constant0"} 1083 : i32
    %0 = arith.divui %arg0, %c1083_i32 {handshake.name = "divui0"} : i32
    return {handshake.name = "return0"} %0 : i32
  }
}


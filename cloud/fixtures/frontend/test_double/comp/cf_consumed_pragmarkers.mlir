module {
  func.func @test_double() -> f64 {
    %cst = arith.constant {handshake.name = "constant0"} 2.228370e-01 : f64
    return {handshake.name = "return0"} %cst : f64
  }
}


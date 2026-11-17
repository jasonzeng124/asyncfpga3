module {
  func.func @test_double() -> f64 {
    %cst = arith.constant 2.228370e-01 : f64
    return %cst : f64
  }
}

module {
  func.func @test_fneg(%arg0: f64) -> f64 {
    %0 = arith.negf %arg0 : f64
    return %0 : f64
  }
}

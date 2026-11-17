module {
  func.func @test_fneg(%arg0: f64 {handshake.arg_name = "a"}) -> f64 {
    %0 = arith.negf %arg0 {handshake.name = "negf0"} : f64
    return {handshake.name = "return0"} %0 : f64
  }
}


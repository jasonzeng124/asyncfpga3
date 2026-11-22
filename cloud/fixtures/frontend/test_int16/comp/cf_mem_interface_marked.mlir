module {
  func.func @test_int16() -> i16 {
    %c-1_i16 = arith.constant {handshake.name = "constant0"} -1 : i16
    return {handshake.name = "return0"} %c-1_i16 : i16
  }
}


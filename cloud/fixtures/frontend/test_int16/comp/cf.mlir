module {
  func.func @test_int16() -> i16 {
    %c-1_i16 = arith.constant -1 : i16
    return %c-1_i16 : i16
  }
}

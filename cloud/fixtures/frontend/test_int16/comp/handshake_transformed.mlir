module {
  handshake.func @test_int16(%arg0: !handshake.control<>, ...) -> (!handshake.channel<i16>, !handshake.control<>) attributes {argNames = ["start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i16} : <>, <i16>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %1, %arg0 : <i16>, <>
  }
}


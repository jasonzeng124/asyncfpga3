module {
  handshake.func @test_fneg(%arg0: !handshake.channel<f64>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<f64>, !handshake.control<>) attributes {argNames = ["a", "start"], resNames = ["out0", "end"]} {
    %0 = negf %arg0 {fastmath = #arith.fastmath<none>, handshake.bb = 0 : ui32, handshake.name = "negf0"} : <f64>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %0, %arg1 : <f64>, <>
  }
}


module {
  handshake.func @test_double(%arg0: !handshake.control<>, ...) -> (!handshake.channel<f64>, !handshake.control<>) attributes {argNames = ["start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2.228370e-01 : f64} : <>, <f64>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %1, %arg0 : <f64>, <>
  }
}


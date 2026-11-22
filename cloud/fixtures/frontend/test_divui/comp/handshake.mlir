module {
  handshake.func @test_divui(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["var1", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1083 : i32} : <>, <i32>
    %2 = divui %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "divui0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %2, %arg1 : <i32>, <>
  }
}


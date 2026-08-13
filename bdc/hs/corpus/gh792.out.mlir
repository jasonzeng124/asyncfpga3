module {
  handshake.func @test(%arg0: !handshake.channel<i2>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["var0", "var2", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.name = "constant0", value = 1 : i2} : <>, <i2>
    %2 = shrui %arg0, %1 {handshake.name = "shrui0"} : <i2>
    %3 = trunci %2 {handshake.name = "trunci0"} : <i2> to <i1>
    %4 = extsi %3 {handshake.name = "extsi0"} : <i1> to <i11>
    %5 = extui %4 {handshake.name = "extui0"} : <i11> to <i32>
    end {handshake.name = "end0"} %5, %arg2 : <i32>, <>
  }
}


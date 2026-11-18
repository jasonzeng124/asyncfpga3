module {
  handshake.func @divmods(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = divsi %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "divsi0"} : <i32>
    %1 = remsi %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "remsi0"} : <i32>
    %2 = xori %0, %1 {handshake.bb = 0 : ui32, handshake.name = "xori0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %2, %arg2 : <i32>, <>
  }
}


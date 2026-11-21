module {
  handshake.func @divmods(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <i32>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = divsi %1#1, %0#1 {handshake.bb = 0 : ui32, handshake.name = "divsi0"} : <i32>
    %3 = remsi %1#0, %0#0 {handshake.bb = 0 : ui32, handshake.name = "remsi0"} : <i32>
    %4 = xori %2, %3 {handshake.bb = 0 : ui32, handshake.name = "xori0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %4, %arg2 : <i32>, <>
  }
}


module {
  handshake.func @divmodu(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <i32>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = divui %1#1, %0#1 {handshake.bb = 0 : ui32, handshake.name = "divui0"} : <i32>
    %5:2 = fork [2] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i32>
    %6 = muli %5#1, %0#0 {handshake.bb = 0 : ui32, handshake.name = "muli0"} : <i32>
    %7 = subi %1#0, %6 {handshake.bb = 0 : ui32, handshake.name = "subi0"} : <i32>
    %8 = shli %7, %3 {handshake.bb = 0 : ui32, handshake.name = "shli0"} : <i32>
    %9 = addi %5#0, %8 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %9, %arg2 : <i32>, <>
  }
}


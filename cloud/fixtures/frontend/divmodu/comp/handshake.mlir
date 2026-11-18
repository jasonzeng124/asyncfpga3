module {
  handshake.func @divmodu(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = divui %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "divui0"} : <i32>
    %3 = muli %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "muli0"} : <i32>
    %4 = subi %arg0, %3 {handshake.bb = 0 : ui32, handshake.name = "subi0"} : <i32>
    %5 = shli %4, %1 {handshake.bb = 0 : ui32, handshake.name = "shli0"} : <i32>
    %6 = addi %2, %5 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %6, %arg2 : <i32>, <>
  }
}


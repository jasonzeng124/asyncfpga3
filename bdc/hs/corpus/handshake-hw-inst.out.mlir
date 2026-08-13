module {
  handshake.func @hw_inst(%arg0: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 31 : i32} : <>, <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 11 : i32} : <>, <i32>
    %4:3 = instance @__placeholder(%3, %arg0) {BITWIDTH = 31 : i32, handshake.bb = 0 : ui32, handshake.name = "call2"} : (!handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %5 = muli %4#0, %4#1 {handshake.bb = 0 : ui32, handshake.name = "muli0"} : <i32>
    %6 = addi %4#1, %4#1 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %7 = subi %3, %4#1 {handshake.bb = 0 : ui32, handshake.name = "subi0"} : <i32>
    %8 = addi %7, %4#0 {handshake.bb = 0 : ui32, handshake.name = "addi1"} : <i32>
    %9 = addi %5, %6 {handshake.bb = 0 : ui32, handshake.name = "addi2"} : <i32>
    %10 = addi %9, %8 {handshake.bb = 0 : ui32, handshake.name = "addi3"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %10, %arg0 : <i32>, <>
  }
  handshake.func private @__placeholder(!handshake.channel<i32>, !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["input_a", "start"], resNames = ["out0", "out1", "end"]}
}


// -----
module {
}


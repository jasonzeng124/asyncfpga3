module {
  handshake.func @simple_example_1(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:5 = fork [5] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%1, %addressResult, %dataResult) %0#1 {connectedBlocks = [0 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i32>) -> ()
    %1 = constant %0#2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 100 : i32} : <>, <i32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = 0 : i7} : <>, <i7>
    %addressResult, %dataResult = store[%3] %2 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store0"} : <i7>, <i32>, <i7>, <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %memEnd, %0#3 : <>, <>
  }
}


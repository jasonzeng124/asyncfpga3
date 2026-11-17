module {
  handshake.func @simple_example_1(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%0, %addressResult, %dataResult) %arg2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 100 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%2] %1 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %memEnd, %arg2 : <>, <>
  }
}


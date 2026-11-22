module {
  handshake.func @unused_arg(%arg0: memref<1xi32>, %arg1: memref<1xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "used", "b", "a_start", "used_start", "start"], resNames = ["out0", "a_end", "used_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1xi32>] %arg4 (%addressResult) %arg5 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%0] %outputs {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %dataResult, %1, %memEnd, %arg5 : <i32>, <>, <>, <>
  }
}


module {
  handshake.func @unused_arg(%arg0: memref<1xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["used", "b", "a_start", "used_start", "start"], resNames = ["out0", "a_end", "used_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    sink %arg2 {handshake.name = "sink0"} : <>
    sink %arg1 {handshake.name = "sink1"} : <i32>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1xi32>] %arg3 (%addressResult) %0#1 {connectedBlocks = [0 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i1>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %addressResult, %dataResult = load[%1] %outputs {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i1>, <i32>, <i1>, <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %dataResult, %2, %memEnd, %0#2 : <i32>, <>, <>, <>
  }
}


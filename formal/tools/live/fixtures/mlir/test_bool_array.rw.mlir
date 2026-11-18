module {
  handshake.func @test_bool_array(%arg0: memref<2xi8>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i1>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<2xi8>] %arg1 (%addressResult, %addressResult_0) %0#2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i1>, !handshake.channel<i1>) -> (!handshake.channel<i8>, !handshake.channel<i8>)
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %3 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %addressResult, %dataResult = load[%3] %outputs#0 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i1>, <i8>, <i1>, <i8>
    %4 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = true} : <>, <i1>
    %addressResult_0, %dataResult_1 = load[%4] %outputs#1 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i1>, <i8>, <i1>, <i8>
    %5 = ori %dataResult, %dataResult_1 {handshake.bb = 0 : ui32, handshake.name = "ori0"} : <i8>
    %6 = trunci %5 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i8> to <i1>
    %7 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = true} : <>, <i1>
    %8 = andi %6, %7 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i1>
    %9 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %10 = cmpi ne, %8, %9 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i1>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %10, %memEnd, %0#3 : <i1>, <>, <>
  }
}


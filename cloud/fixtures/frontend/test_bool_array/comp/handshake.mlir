module {
  handshake.func @test_bool_array(%arg0: memref<2xi8>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i1>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<2xi8>] %arg1 (%addressResult, %addressResult_0) %arg2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i8>, !handshake.channel<i8>)
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i8} : <>, <i8>
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 0 : i8} : <>, <i8>
    %5 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%5] %outputs#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i8>, <i32>, <i8>
    %addressResult_0, %dataResult_1 = load[%0] %outputs#1 {handshake.bb = 0 : ui32, handshake.name = "load1"} : <i32>, <i8>, <i32>, <i8>
    %6 = ori %dataResult, %dataResult_1 {handshake.bb = 0 : ui32, handshake.name = "ori0"} : <i8>
    %7 = andi %6, %2 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i8>
    %8 = cmpi ne, %7, %4 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i8>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %8, %memEnd, %arg2 : <i1>, <>, <>
  }
}


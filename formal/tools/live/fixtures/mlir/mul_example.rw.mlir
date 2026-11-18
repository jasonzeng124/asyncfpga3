module {
  handshake.func @mul_example(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%10, %addressResult, %addressResult_0, %dataResult_1) %result_4 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i7>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %7 = extui %6#2 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i7> to <i8>
    %8 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i8} : <>, <i8>
    %result, %index = control_merge [%4, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %10 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%6#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %13:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %14 = muli %13#0, %13#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %15 = muli %14, %13#2 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %addressResult_0, %dataResult_1 = store[%6#0] %15 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %16 = addi %7, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i8>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i8>
    %18 = trunci %17#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %19 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 100 : i8} : <>, <i8>
    %20 = cmpi ult, %17#1, %19 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i8>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %21#0, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_2, %falseResult_3 = cond_br %21#1, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink1"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}


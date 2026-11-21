module {
  handshake.func @vector_rescale(%arg0: memref<1000xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg2 (%14, %addressResult, %addressResult_0, %dataResult_1) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i10>
    %4 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %12#0 [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %8 = extui %7#2 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i10> to <i11>
    %9 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i11} : <>, <i11>
    %10 = mux %12#1 [%4, %trueResult_2] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %result, %index = control_merge [%5, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %14 = constant %13#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%7#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %17 = muli %dataResult, %11#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %addressResult_0, %dataResult_1 = store[%7#0] %17 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    %18 = addi %8, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i11>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i11>
    %20 = trunci %19#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %21 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1000 : i11} : <>, <i11>
    %22 = cmpi ult, %19#1, %21 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %23:3 = fork [3] %22 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %23#0, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i10>
    sink %falseResult {handshake.name = "sink0"} : <i10>
    %trueResult_2, %falseResult_3 = cond_br %23#1, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %23#2, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink2"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}


module {
  handshake.func @test_bitint(%arg0: memref<10xi16>, %arg1: memref<10xi5>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["arr", "weight", "arr_start", "weight_start", "start"], resNames = ["out0", "arr_end", "weight_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<10xi5>] %arg3 (%addressResult_2) %27#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i4>) -> !handshake.channel<i5>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<10xi16>] %arg2 (%addressResult) %27#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i4>) -> !handshake.channel<i16>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3:2 = fork [2] %2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %4 = extui %3#1 {handshake.bb = 0 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %5 = extui %3#0 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i4>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %12#0 [%5, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i4>, <i4>] to <i4>
    %8:3 = fork [3] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i4>
    %9 = extui %8#2 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i4> to <i5>
    %10 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i5} : <>, <i5>
    %11 = mux %12#1 [%4, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%8#1] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i16>, <i4>, <i16>
    %15 = extui %dataResult {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i16> to <i21>
    %addressResult_2, %dataResult_3 = load[%8#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i4>, <i5>, <i4>, <i5>
    %16 = extui %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i5> to <i21>
    %17 = muli %15, %16 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i21>
    %18 = extui %17 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i21> to <i32>
    %19 = addi %11, %18 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %20 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i5>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i5>
    %22 = trunci %21#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i5> to <i4>
    %23 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 10 : i5} : <>, <i5>
    %24 = cmpi ult, %21#1, %23 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i5>
    %25:3 = fork [3] %24 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %25#0, %22 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i4>
    sink %falseResult {handshake.name = "sink0"} : <i4>
    %trueResult_4, %falseResult_5 = cond_br %25#1, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %25#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %26 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %27:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %26, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

